//! Aggregation on the machine itself: many proofs of one program, verified as one, by two verifier programs.
//!
//! - The first-level program verifies `arity_0` proofs of the leaf program.
//! - The node program verifies `arity` proofs, each of the first-level program or of the node program itself.
//!
//! Both programs' proofs have one shape, so the node program verifies a child of either kind with one text.
//!
//! Every proof states the same words (`TreeStatement`): its kind, a digest of its leaves' outputs, and one claim on
//! each polynomial only the root's verifier evaluates. A node reduces the claims its children leave and carry
//! (`rec::reduce`), so the statement does not grow.
//!
//! A tree program's transcript is seeded with the tree's seed, not its own digest, which the node program could not
//! hold of itself. What binds a child to its program is its kind, a word of its statement, and the claim its core
//! leaves on its bytecode table, which the node moves to the two programs' tables stacked under the kind.

use super::BuildError;
use super::lower::{Lowered, lower};
use super::record::{D, E, Gen, K};
use crate::class_flock::FlockId;
use crate::cpu::filler::{FillBlocks, Plan};
use crate::cpu::{
    Announcement, Claim, CpuError, DecodeError, DeferredClaims, Layout, Lookup, Output, Program, ProgramPoint, Proof,
    ProveError, Prover, Stats,
};
use crate::envelope::Envelope;
use crate::leaf::N_TUPLE_BITS;
use crate::log2_ceil_usize;
use crate::pcs::Rate;
use crate::rec::LeafShape;
use crate::rec::ProofSource;
use crate::rec::claims::{DenseClaim, DensePoly, MatrixClaim, NodeClaims};
use crate::rec::hash::chain;
use crate::rec::reduce::{self, DenseTables, DenseVars, Reduced};
use crate::rec::statement::{Kind, Section, StatementLayout, TreeStatement};
use crate::rv::{Entry, ProgramError, Region};
use crate::tables::{PerTable, TableId};
use ::pcs::ring_switch::inverse_frobenius_ladder;
use fiat_shamir::arith::{Arith, Verifier};
use fiat_shamir::transcript::RawProof;
use primitives::field::{F64, F192};
use primitives::hash::Hasher;
use primitives::multilinear::{eq_table, mle_eval_par};
use thiserror::Error;

const DOMAIN: &[u8] = b"leanvm-program-tree-2";

/// The shape both tree programs' proofs have: their tables' heights and their programs' sizes.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct Shape {
    taus: PerTable<usize>,
    log_bytecode: usize,
    log_ram: usize,
    log_advice: usize,
}

impl Shape {
    /// The least shape holding both.
    fn max(self, other: Self) -> Self {
        Self {
            taus: PerTable::from_fn(|t| self.taus[t].max(other.taus[t])),
            log_bytecode: self.log_bytecode.max(other.log_bytecode),
            log_ram: self.log_ram.max(other.log_ram),
            log_advice: self.log_advice.max(other.log_advice),
        }
    }
}

/// The entries a program has past its text: its trap, its fill blocks, an illegal slot and its halt slot.
const OVERHEAD: usize = 1 + FillBlocks::WORDS + 2;

/// How many rounds the two programs' shapes are given to settle.
const ROUNDS: usize = 8;

/// A text as a program of the shape's sizes: illegal words, which nothing reaches, fill it to the shape's bytecode.
///
/// A no-op stands for an empty text, an entry point being an instruction: a program of these sizes, whatever it does,
/// is what a layout reads of a program before its deferred claims.
fn padded(text: &[u32], shape: Shape) -> Result<Program, ProgramError> {
    let mut text = if text.is_empty() { vec![0x13] } else { text.to_vec() };
    let room = (1usize << shape.log_bytecode).saturating_sub(OVERHEAD);
    if text.len() < room {
        text.resize(room, 0);
    }
    Program::new(&text, Region::TEXT.base(), Vec::new(), shape.log_ram, shape.log_advice)
}

/// A circuit's two matrices at a row point and a column point, each a prefix of the statement's.
fn matrices_at(f: FlockId, rows: &[F192], cols: &[F192]) -> [F192; 2] {
    let circuit = f.circuit();
    let k = circuit.k_log();
    let (ra, rb) = circuit.row_values(&eq_table(&cols[..k]));
    let u = eq_table(&rows[..k]);
    let dot = |r: &[F192]| u.iter().zip(r).fold(F192::ZERO, |acc, (&x, &y)| acc + x * y);
    [dot(&ra), dot(&rb)]
}

/// A verifier program's instructions by table: each runs exactly once, its traps aside, which never run.
fn rows(text: &[u32]) -> PerTable<usize> {
    let mut rows = PerTable::<usize>::default();
    for (i, &word) in text.iter().enumerate() {
        if let Some(t) = TableId::of(Entry::decode(word, Region::TEXT.address(i)).class) {
            rows[t] += 1;
        }
    }
    rows
}

/// What a node is recorded over: proofs, or their shapes alone.
#[derive(Clone, Copy)]
enum Over<'a> {
    /// A first-level node over leaf proofs, each with its run's output.
    Leaves(Option<&'a [(Output, RawProof)]>),
    /// A node over tree proofs, each with its statement.
    Children(Option<&'a [(Vec<F192>, RawProof)]>),
}

impl Over<'_> {
    const fn shape(kind: Kind) -> Self {
        match kind {
            Kind::First => Self::Leaves(None),
            Kind::Node => Self::Children(None),
        }
    }

    const fn proven(self) -> bool {
        matches!(self, Self::Leaves(Some(_)) | Self::Children(Some(_)))
    }
}

/// A recorded node's run: its advice, what it states, and its output.
struct Recorded {
    advice: Vec<u64>,
    statement: Vec<F192>,
    output: [u64; 4],
}

/// The shape a proof of a lowered program has by itself: its instructions counted by table, each run exactly once.
fn shape_of(lowered: &Lowered, advice: usize) -> Shape {
    let base = rows(&lowered.text);
    let filled = Plan::solve(base).filled(base);
    Shape {
        taus: filled.map(|rows| rows.trailing_zeros() as usize),
        log_bytecode: log2_ceil_usize(lowered.text.len() + OVERHEAD),
        log_ram: lowered.log_ram,
        log_advice: log2_ceil_usize(advice),
    }
}

/// One proof of a tree: its statement and the proof of the program run that makes it.
#[derive(Clone, Debug)]
pub struct TreeProof {
    words: Vec<F192>,
    proof: Proof,
    stats: Stats,
}

impl TreeProof {
    /// The proof of the tree program's run.
    #[must_use]
    pub const fn proof(&self) -> &Proof {
        &self.proof
    }

    /// The cost of the tree program's run: its cycles, its table heights and its committed words.
    #[must_use]
    pub const fn stats(&self) -> &Stats {
        &self.stats
    }

    /// The header of a tree proof's bytes: the magic `LVMT`, then the tree protocol's version.
    const ENVELOPE: Envelope = Envelope::new(*b"LVMT", 14);

    /// The proof's bytes: its statement's words, then its program's proof.
    #[must_use]
    pub fn to_bytes(&self) -> Vec<u8> {
        let mut body = (self.words.len() as u32).to_le_bytes().to_vec();
        for w in &self.words {
            for limb in [w.c0, w.c1, w.c2] {
                body.extend(limb.to_le_bytes());
            }
        }
        body.extend(self.proof.to_bytes());
        Self::ENVELOPE.seal(&body)
    }

    /// The tree proof these bytes encode, its run's cost left empty.
    ///
    /// # Errors
    ///
    /// - Bytes that are no tree proof.
    /// - A tree proof of another protocol version.
    pub fn from_bytes(bytes: &[u8]) -> Result<Self, DecodeError> {
        let body = Self::ENVELOPE.open(bytes)?;
        let (count, rest) = body.split_first_chunk::<4>().ok_or(DecodeError::Malformed)?;
        let n = u32::from_le_bytes(*count) as usize;
        let len = (n.checked_mul(24))
            .filter(|&len| len <= rest.len())
            .ok_or(DecodeError::Malformed)?;
        let (words, proof) = rest.split_at(len);
        let word = |chunk: &[u8]| u64::from_le_bytes(chunk.try_into().expect("eight bytes"));
        Ok(Self {
            words: (words.as_chunks::<24>().0.iter())
                .map(|w| F192::new(word(&w[..8]), word(&w[8..16]), word(&w[16..])))
                .collect(),
            proof: Proof::from_bytes(proof)?,
            stats: Stats::default(),
        })
    }

    /// The kind of tree proof this states it is, if one.
    #[must_use]
    pub fn kind(&self) -> Option<Kind> {
        self.words.first().and_then(|&w| Kind::of_word(w))
    }
}

/// Why a tree could not be built, or a proof of it made or accepted.
#[derive(Clone, Debug, PartialEq, Eq, Error)]
pub enum TreeError {
    /// The tree's arities: at least one leaf per first-level proof and two children per node.
    #[error("a tree verifies at least 1 leaf per first-level proof and 2 children per node, not {arity_0} and {arity}")]
    Arity { arity_0: usize, arity: usize },
    /// The two programs' shapes did not settle.
    #[error("the tree's programs have no common shape")]
    Shape,
    /// A program could not be built.
    #[error(transparent)]
    Build(#[from] BuildError),
    /// As many proofs as the program verifies are needed.
    #[error("{got} proofs for a program verifying {expected}")]
    Count { expected: usize, got: usize },
    /// A proof handed to a prover or to the root does not verify.
    #[error("proof {index} does not verify: {error}")]
    Child { index: usize, error: CpuError },
    /// A leaf proof of another shape than the tree was built for.
    #[error("leaf proof {index} has another shape than the tree's leaves")]
    LeafShape { index: usize },
    /// A tree program's run could not be proven.
    #[error(transparent)]
    Prove(#[from] ProveError),
    /// The root's kind is not a tree's.
    #[error("the root states no kind of tree proof")]
    Kind,
    /// The root's digest is not that of the outputs.
    #[error("the root's digest is not the outputs'")]
    Outputs,
    /// A claim the root carries is false.
    #[error("the root's claim on {0} is false")]
    Claim(&'static str),
}

/// A tree over proofs of one program, at one leaf shape.
#[derive(Clone)]
pub struct Tree<'p> {
    leaf: &'p Program,
    leaf_shape: LeafShape,
    arity_0: usize,
    arity: usize,
    rate: Rate,
    shape: Shape,
    vars: DenseVars,
    statement: StatementLayout,
    /// The transcript seed of both programs' proofs.
    seed: [F64; 4],
    stand_in: Program,
    programs: [Program; 2],
    /// Each program's instructions by table: every one runs exactly once.
    rows: [PerTable<usize>; 2],
    tables: DenseTables,
}

impl<'p> Tree<'p> {
    /// The tree over proofs of `leaf` of the shape `shape`: each first-level proof verifies `arity_0` of them, each
    /// node `arity` tree proofs, every tree proof at `rate`.
    ///
    /// # Errors
    ///
    /// Returns an error on arities no tree has, or if the programs cannot be built.
    pub fn new(
        leaf: &'p Program,
        shape: &LeafShape,
        arity_0: usize,
        arity: usize,
        rate: Rate,
    ) -> Result<Self, TreeError> {
        if arity_0 == 0 || arity < 2 {
            return Err(TreeError::Arity { arity_0, arity });
        }
        // The least shape both programs' proofs fit: each program depends on it, so it is a fixed point.
        let floor = Shape {
            taus: PerTable::from_fn(|t: TableId| t.spec().n_blocks_log(1)),
            log_bytecode: log2_ceil_usize(1 + OVERHEAD),
            log_ram: 1,
            log_advice: 1,
        };
        let mut tree = Self::at(leaf, *shape, arity_0, arity, rate, floor)?;
        for _ in 0..ROUNDS {
            let mut natural = tree.shape;
            let mut texts = Vec::new();
            for kind in Kind::ALL {
                let (run, lowered) = tree.record(Over::shape(kind), lower)?;
                natural = natural.max(shape_of(&lowered, run.advice.len()));
                texts.push(lowered.text);
            }
            if natural == tree.shape {
                return tree.finish(&texts);
            }
            tree = Self::at(leaf, *shape, arity_0, arity, rate, natural)?;
        }
        Err(TreeError::Shape)
    }

    /// The tree's parameters at a shape, its programs not built yet: a stand-in holds their place.
    fn at(
        leaf: &'p Program,
        leaf_shape: LeafShape,
        arity_0: usize,
        arity: usize,
        rate: Rate,
        shape: Shape,
    ) -> Result<Self, TreeError> {
        let rv = leaf.rv();
        let vars = DenseVars([
            crate::log2_strict_usize(rv.entries().len()) + N_TUPLE_BITS,
            log2_ceil_usize(rv.image().len().max(1)),
            shape.log_bytecode + N_TUPLE_BITS + 1,
        ]);
        let statement = StatementLayout::new(vars.0.into_iter().max().unwrap_or(0));
        let stand_in = padded(&[], shape).map_err(BuildError::from)?;
        let mut tree = Self {
            leaf,
            leaf_shape,
            arity_0,
            arity,
            rate,
            shape,
            vars,
            statement,
            seed: [F64::ZERO; 4],
            programs: [stand_in.clone(), stand_in.clone()],
            rows: [PerTable::default(); 2],
            stand_in,
            tables: DenseTables([Vec::new(), Vec::new(), Vec::new()]),
        };
        tree.seed = tree.seed();
        Ok(tree)
    }

    /// The transcript seed of both programs' proofs: the tree's whole description.
    fn seed(&self) -> [F64; 4] {
        let mut h = Hasher::new();
        h.update(DOMAIN);
        h.update(self.leaf.digest());
        let s = self.shape;
        let sizes = (self.leaf_shape.taus.values().copied())
            .chain([self.arity_0, self.arity, self.statement.len()])
            .chain(s.taus.into_values())
            .chain([s.log_bytecode, s.log_ram, s.log_advice]);
        for x in sizes {
            h.update(&(x as u64).to_le_bytes());
        }
        h.update(&[self.leaf_shape.rate.log_inv_rate(), self.rate.log_inv_rate()]);
        fiat_shamir::digest_words(&h.finalize())
    }

    /// The two programs from their texts at the settled shape, and the polynomials the root evaluates.
    fn finish(mut self, texts: &[Vec<u32>]) -> Result<Self, TreeError> {
        for kind in Kind::ALL {
            let text = &texts[kind as usize];
            self.rows[kind as usize] = rows(text);
            self.programs[kind as usize] = padded(text, self.shape).map_err(BuildError::from)?;
        }
        let rv = self.leaf.rv();
        let mut image: Vec<F64> = rv.image().iter().map(|&w| F64(w)).collect();
        image.resize(1 << self.vars[DensePoly::Image], F64::ZERO);
        // The two programs' bytecode tables, the first-level program's then the node program's: the kind is the top variable.
        let stacked: Vec<F64> = (self.programs.iter())
            .flat_map(|p| Lookup::Bytecode.table(p.rv()))
            .collect();
        self.tables = DenseTables([Lookup::Bytecode.table(rv), image, stacked]);
        Ok(self)
    }

    /// The cost of a kind of tree proof's run, with no proof: its cycles, its tables' heights, its committed words.
    ///
    /// # Panics
    ///
    /// Panics if the shape does not fit one commitment, which building the tree refuses.
    #[must_use]
    pub fn stats(&self, kind: Kind) -> Stats {
        let counts = self.shape.taus.map(|tau| 1usize << tau);
        Stats {
            proven_rows: counts.values().sum(),
            counts,
            base_counts: self.rows[kind as usize],
            committed: (self.program(kind).committed_size(counts)).expect("a shape one commitment holds"),
        }
    }

    /// The program of a kind of tree proof.
    #[must_use]
    pub const fn program(&self, kind: Kind) -> &Program {
        &self.programs[kind as usize]
    }

    /// Record one node, over proofs or over their shapes alone, and give the recorder to `then`: to lower it, or not.
    fn record<T>(&self, over: Over<'_>, then: impl FnOnce(&Gen<'_>) -> T) -> Result<(Recorded, T), BuildError> {
        // The reduction's proof is made while the node is recorded, and outlives the recorder that reads it.
        let reduction;
        let proven = over.proven();
        let mut g = Gen::new();
        let mut claims = NodeClaims::default();
        let (kind, digest) = match over {
            Over::Leaves(leaves) => {
                let LeafShape { taus, rate } = self.leaf_shape;
                let layout = Layout::announced(self.leaf.rv(), taus)?;
                let mut outputs = Vec::new();
                for i in 0..self.arity_0 {
                    let leaf = leaves.map(|l| &l[i]);
                    let source = leaf.map_or(ProofSource::Shape, |l| ProofSource::Proof(&l.1));
                    let output = leaf.map_or([0; 4], |l| *l.0.words());
                    let words = g.start(source, self.leaf.fs_seed().map(|w| w.0), output);
                    let program = self.core(&mut g, &layout, &taus, rate, words, &mut claims)?;
                    self.leaf_program_claims(&mut g, &program, proven, &mut claims);
                    outputs.extend(words);
                }
                let header = Kind::First.header(self.arity_0).map(|w| g.word(w));
                let words: Vec<K> = header.into_iter().chain(outputs).collect();
                (Kind::First, g.chain(&words))
            }
            Over::Children(children) => {
                let layout = Layout::announced(self.stand_in.rv(), self.shape.taus)?;
                let mut digests = Vec::new();
                for i in 0..self.arity {
                    let child = children.map(|c| &c[i]);
                    let source = child.map_or(ProofSource::Shape, |c| ProofSource::Proof(&c.1));
                    let words: Vec<E> = (0..self.statement.len())
                        .map(|w| g.free_e(child.map_or(F192::ZERO, |c| c.0[w])))
                        .collect();
                    let statement = TreeStatement::new(self.statement, words);
                    // The kind is a bit: it selects the child's program's half of the stacked tables.
                    let child_kind = statement.kind();
                    let square = g.square(child_kind);
                    g.ensure_eq(square, child_kind, || ())
                        .expect("a recorder refuses nothing");
                    // The child's run outputs the hash of its statement.
                    let limbs: Vec<K> = statement.words().iter().flat_map(|&w| g.limbs(w)).collect();
                    let output = g.chain(&limbs);
                    let words = g.start_on(source, self.seed.map(|w| w.0), output);
                    let program = self.core(&mut g, &layout, &self.shape.taus, self.rate, words, &mut claims)?;
                    self.node_program_claims(&mut g, &program, child_kind, proven, &mut claims);
                    self.carried(&statement, child_kind, &mut claims);
                    let [lo, hi] = statement.digest();
                    let digest = g.halves_to_d(lo, hi);
                    digests.extend(g.d_words(digest));
                }
                let header = Kind::Node.header(self.arity).map(|w| g.word(w));
                let words: Vec<K> = header.into_iter().chain(digests).collect();
                (Kind::Node, g.chain(&words))
            }
        };

        // The reduction: a proof made natively from the claims' values, verified here.
        let source = if proven {
            let values = claims.map(|e| g.e(e));
            reduction = RawProof {
                stream: values.prove(&self.vars, &self.tables).stream,
                merkle: Vec::new(),
            };
            ProofSource::Proof(&reduction)
        } else {
            ProofSource::Shape
        };
        g.start_from(source, reduce::initial_state());
        let reduced = claims.verify(&mut g, &self.vars).expect("a recorder refuses nothing");
        g.finish().expect("a recorder reads no value");
        assert!(g.finished(), "the verifier read the whole reduction");

        let statement = self.state(&mut g, &reduced, kind, digest);
        let words = statement.words().to_vec();
        let output = g.commit(&[], &words);
        let then = then(&g);
        let recorded = Recorded {
            statement: words.iter().map(|&e| g.e(e)).collect(),
            advice: g.advice,
            output,
        };
        Ok((recorded, then))
    }

    /// The core of one proof whose run output the words `output`: its announcement held to the shape, then every check.
    ///
    /// Its final transcript state and its circuits' matrix claims join `claims`; its program claim is returned.
    fn core(
        &self,
        g: &mut Gen<'_>,
        layout: &Layout,
        taus: &PerTable<usize>,
        rate: Rate,
        output: [K; 4],
        claims: &mut NodeClaims<E>,
    ) -> Result<Claim<ProgramPoint<E>, E>, BuildError> {
        for size in Announcement::sizes(taus, rate) {
            g.expect_scalar(size);
        }
        let clock = g.clock();
        let elements = output.map(|k| g.k_to_e(k));
        let DeferredClaims { program, circuits } = layout.verify_core(g, clock, &elements, rate)?;
        g.finish().expect("a recorder reads no value");
        assert!(g.finished(), "the verifier read the whole proof");
        claims.bound.extend(g.state());
        let fresh = FlockId::ALL.into_iter().zip(&circuits);
        claims.matrices.extend(fresh.map(|(f, c)| MatrixClaim::fresh(f, c)));
        Ok(program)
    }

    /// A hint of a polynomial's value at a point: the prover's, which a claim then holds it to.
    fn hint(&self, g: &mut Gen<'_>, poly: DensePoly, point: &[E], proven: bool) -> E {
        let value = if proven {
            let at: Vec<F192> = point.iter().map(|&e| g.e(e)).collect();
            mle_eval_par(&self.tables[poly], &at)
        } else {
            F192::ZERO
        };
        g.free_e(value)
    }

    /// A program claim as point claims on a bytecode table: one per multiplicity bit, at the point its Frobenius
    /// twist moves the bus point to, each a hint held to the claim by the twist.
    ///
    /// The table is a dense polynomial, its bytecode's variables, and a top coordinate if it is stacked.
    fn twisted(
        &self,
        g: &mut Gen<'_>,
        p: &ProgramPoint<E>,
        (poly, kbc, top): (DensePoly, usize, Option<E>),
        proven: bool,
        claims: &mut NodeClaims<E>,
    ) -> E {
        let (chi, alpha) = p.bytecode.split_at(kbc);
        let ladders: Vec<Vec<E>> = chi.iter().map(|&x| inverse_frobenius_ladder(g, x, 1)).collect();
        let mut total = g.zero();
        for (i, &mu) in p.twist.iter().enumerate() {
            let point: Vec<E> = (ladders.iter().map(|l| l[i]))
                .chain(alpha.iter().copied())
                .chain(top)
                .collect();
            let d = self.hint(g, poly, &point, proven);
            let twisted = (0..i).fold(d, |x, _| g.square(x));
            total = g.mul_add(mu, twisted, total);
            claims.bound.push(d);
            claims.dense.push(DenseClaim::at(poly, point, None, d));
        }
        total
    }

    /// A leaf's program claim: its bytecode table's twisted points, then RAM's image.
    fn leaf_program_claims(
        &self,
        g: &mut Gen<'_>,
        program: &Claim<ProgramPoint<E>, E>,
        proven: bool,
        claims: &mut NodeClaims<E>,
    ) {
        let p = &program.point;
        let kbc = self.vars[DensePoly::Bytecode] - N_TUPLE_BITS;
        let mut total = self.twisted(g, p, (DensePoly::Bytecode, kbc, None), proven, claims);
        let m = self.vars[DensePoly::Image];
        let low = p.image_point[..m].to_vec();
        let image = self.hint(g, DensePoly::Image, &low, proven);
        let above = (p.image_point[m..].iter()).fold(p.image_weight, |acc, &x| g.times_one_plus(acc, x));
        total = g.mul_add(above, image, total);
        g.ensure_eq(total, program.value, || ())
            .expect("a recorder refuses nothing");
        claims.bound.push(image);
        claims.dense.push(DenseClaim::at(DensePoly::Image, low, None, image));
    }

    /// A tree proof's program claim: its program's bytecode table, the stacked tables at its kind; its image is empty.
    fn node_program_claims(
        &self,
        g: &mut Gen<'_>,
        program: &Claim<ProgramPoint<E>, E>,
        kind: E,
        proven: bool,
        claims: &mut NodeClaims<E>,
    ) {
        let table = (DensePoly::Fixed, self.shape.log_bytecode, Some(kind));
        let total = self.twisted(g, &program.point, table, proven, claims);
        g.ensure_eq(total, program.value, || ())
            .expect("a recorder refuses nothing");
    }

    /// The claims a child's statement carries.
    fn carried(&self, statement: &TreeStatement<E>, kind: E, claims: &mut NodeClaims<E>) {
        let point = statement.dense_point();
        for poly in DensePoly::ALL {
            let n = self.vars[poly];
            // A first-level proof carries no claim on the stacked tables.
            let scale = (poly == DensePoly::Fixed).then_some(kind);
            claims.dense.push(DenseClaim::at(
                poly,
                point[..n].to_vec(),
                scale,
                statement.dense_value(poly),
            ));
        }
        for f in FlockId::ALL {
            claims.matrices.extend(MatrixClaim::carried(
                f,
                f.k_log(),
                statement.rows(),
                statement.cols(),
                statement.matrices(f),
            ));
        }
    }

    /// The statement a node leaves: its kind, its digest, and the reduced claims.
    fn state(&self, g: &mut Gen<'_>, reduced: &Reduced<E>, kind: Kind, digest: D) -> TreeStatement<E> {
        let zero = g.zero();
        let mut s = TreeStatement::filled(self.statement, zero);
        s.section_mut(Section::Kind)[0] = g.constant(F192::new(kind.bit(), 0, 0));
        s.section_mut(Section::Digest).copy_from_slice(&g.d_halves(digest));
        s.section_mut(Section::DensePoint)[..reduced.dense.point.len()].copy_from_slice(&reduced.dense.point);
        let values = reduced.dense.values.map(|v| v.unwrap_or(zero));
        s.section_mut(Section::DenseValues).copy_from_slice(&values);
        s.section_mut(Section::Rows).copy_from_slice(&reduced.matrices.rows);
        s.section_mut(Section::Cols).copy_from_slice(&reduced.matrices.cols);
        s.section_mut(Section::Matrices)
            .copy_from_slice(reduced.matrices.values.as_flattened());
        s
    }

    /// The hash a tree program's run outputs of its statement.
    fn output(words: &[F192]) -> Output {
        let limbs: Vec<u64> = words.iter().flat_map(|w| [w.c0, w.c1, w.c2]).collect();
        Output::new(chain(&limbs))
    }

    /// Prove a node from what it is over: its program is the tree's, so the recording is not lowered again.
    fn prove(&self, kind: Kind, over: Over<'_>) -> Result<TreeProof, TreeError> {
        let (run, ()) = self.record(over, |_| ())?;
        let Recorded {
            advice,
            statement,
            output,
        } = run;
        let run = Prover::new(self.rate).prove_seeded(self.program(kind), &advice, self.shape.taus, self.seed)?;
        debug_assert_eq!(*run.output.words(), output);
        Ok(TreeProof {
            words: statement,
            proof: run.proof,
            stats: run.stats,
        })
    }

    /// Prove a first-level node over `arity_0` proofs of the leaf program, each with its run's output.
    ///
    /// # Errors
    ///
    /// Returns an error on another number of proofs, or one that does not verify.
    pub fn prove_first(&self, leaves: &[(Output, &Proof)]) -> Result<TreeProof, TreeError> {
        if leaves.len() != self.arity_0 {
            return Err(TreeError::Count {
                expected: self.arity_0,
                got: leaves.len(),
            });
        }
        let raws = (leaves.iter().enumerate())
            .map(
                |(index, &(output, proof))| match self.leaf.verify_to_raw(output, proof) {
                    Ok(_) if LeafShape::of(proof) != Ok(self.leaf_shape) => Err(TreeError::LeafShape { index }),
                    Ok(raw) => Ok((output, raw)),
                    Err(error) => Err(TreeError::Child { index, error }),
                },
            )
            .collect::<Result<Vec<_>, _>>()?;
        self.prove(Kind::First, Over::Leaves(Some(&raws)))
    }

    /// Prove a node over `arity` tree proofs, of either kind.
    ///
    /// # Errors
    ///
    /// Returns an error on another number of proofs, or one that does not verify.
    pub fn prove_node(&self, children: &[TreeProof]) -> Result<TreeProof, TreeError> {
        if children.len() != self.arity {
            return Err(TreeError::Count {
                expected: self.arity,
                got: children.len(),
            });
        }
        let raws = (children.iter().enumerate())
            .map(|(index, child)| self.read(child, index).map(|(_, raw)| (child.words.clone(), raw)))
            .collect::<Result<Vec<_>, _>>()?;
        self.prove(Kind::Node, Over::Children(Some(&raws)))
    }

    /// A tree proof's kind and core: its program's proof verified on the tree's seed, its own claims settled.
    fn read(&self, p: &TreeProof, index: usize) -> Result<(Kind, RawProof), TreeError> {
        let kind = (p.words.len() == self.statement.len())
            .then(|| Kind::of_word(p.words[0]))
            .flatten()
            .ok_or(TreeError::Kind)?;
        let program = self.program(kind);
        let settled = (program.replay_seeded(Self::output(&p.words), &p.proof, self.seed))
            .and_then(|(claims, raw)| program.check_deferred(&claims).map(|()| raw));
        match settled {
            Ok(raw) => Ok((kind, raw)),
            Err(error) => Err(TreeError::Child { index, error }),
        }
    }

    /// The digest of the leaves' outputs a tree over them states.
    fn digest(&self, outputs: &[Output]) -> [u64; 4] {
        let outputs: Vec<[u64; 4]> = outputs.iter().map(|output| *output.words()).collect();
        let mut level: Vec<[u64; 4]> = outputs.chunks(self.arity_0).map(|o| Kind::First.digest(o)).collect();
        while level.len() > 1 {
            level = level.chunks(self.arity).map(|c| Kind::Node.digest(c)).collect();
        }
        level[0]
    }

    /// Verify a root: its proof, that it is over these outputs in order, and every claim it carries.
    ///
    /// # Errors
    ///
    /// Returns what refuses it.
    pub fn verify(&self, root: &TreeProof, outputs: &[Output]) -> Result<(), TreeError> {
        let (kind, _) = self.read(root, 0)?;
        let s = TreeStatement::new(self.statement, root.words.clone());
        if outputs.is_empty() || s.digest_words() != self.digest(outputs) {
            return Err(TreeError::Outputs);
        }
        let vars = &self.vars.0;
        for poly in DensePoly::ALL {
            // A first-level proof reduces no claim on the stacked tables.
            if poly == DensePoly::Fixed && kind == Kind::First {
                continue;
            }
            let point = &s.dense_point()[..vars[poly as usize]];
            if mle_eval_par(&self.tables[poly], point) != s.dense_value(poly) {
                return Err(TreeError::Claim(match poly {
                    DensePoly::Bytecode => "the leaf program's bytecode",
                    DensePoly::Image => "the leaf program's image",
                    DensePoly::Fixed => "the tree programs' bytecode",
                }));
            }
        }
        let held = parallel::map_collect(FlockId::ALL.len(), |f| {
            let f = FlockId::ALL[f];
            matrices_at(f, s.rows(), s.cols()) == s.matrices(f)
        });
        if held.into_iter().all(|h| h) {
            Ok(())
        } else {
            Err(TreeError::Claim("a circuit's matrices"))
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::cpu::ProvenRun;
    use crate::rv::Machine;
    use crate::rv::asm::*;

    /// One advice word in this many is forged.
    const TAMPER_STRIDE: usize = 1;

    // A program with a loop and an image, whose output is the advice's first word XOR a constant.
    fn leaf_program() -> Program {
        let text = Asm::new()
            .li(Reg::T5, Region::ADVICE.base())
            .load(Ld, Reg::T0, 0, Reg::T5)
            .li(Reg::T1, 9)
            .r(Xor, Reg::A0, Reg::T0, Reg::T1)
            .label("loop")
            .i(Addi, Reg::T1, Reg::T1, -1)
            .branch(Bne, Reg::T1, Reg::ZERO, "loop")
            .exit()
            .finish();
        Program::new(&text, Region::TEXT.base(), vec![3, 5], 2, 0).expect("a valid program")
    }

    #[test]
    fn a_tree_of_verifier_programs_verifies_and_binds_its_leaves() {
        // Fixture: four runs of the leaf program with distinct outputs, one leaf per first-level proof, two children per node.
        let program = leaf_program();
        let prover = Prover::new(Rate::MIN);
        let runs: Vec<ProvenRun> = (0..4u64)
            .map(|i| prover.prove(&program, &[100 + i]).expect("the run halts"))
            .collect();
        let shape = LeafShape::of(&runs[0].proof).expect("a proof's shape");
        let tree = Tree::new(&program, &shape, 1, 2, Rate::MIN).expect("a tree");
        let outputs: Vec<Output> = runs.iter().map(|r| r.output).collect();

        // The first level, then a node over first-level proofs, then a node over nodes: a program verifying itself.
        let firsts: Vec<TreeProof> = (runs.iter())
            .map(|r| tree.prove_first(&[(r.output, &r.proof)]).expect("a first-level proof"))
            .collect();
        assert_eq!(tree.verify(&firsts[0], &outputs[..1]), Ok(()));
        let nodes: Vec<TreeProof> = (firsts.chunks(2))
            .map(|pair| tree.prove_node(pair).expect("a node"))
            .collect();
        assert_eq!(tree.verify(&nodes[0], &outputs[..2]), Ok(()));
        let root = tree.prove_node(&nodes).expect("a root");
        assert_eq!(tree.verify(&root, &outputs), Ok(()));

        // A tree proof's bytes decode to a proof the root's verifier accepts.
        let decoded = TreeProof::from_bytes(&root.to_bytes()).expect("a tree proof's bytes");
        assert_eq!(tree.verify(&decoded, &outputs), Ok(()));

        // A leaf proof of another shape is refused before anything is recorded over it.
        let other = Prover::new(Rate::new(2).unwrap())
            .prove(&program, &[1])
            .expect("the leaf halts");
        assert!(matches!(
            tree.prove_first(&[(other.output, &other.proof)]),
            Err(TreeError::LeafShape { index: 0 })
        ));

        // A node built over proofs is the program built from the shape alone, and its run outputs its statement's hash.
        let raw = program
            .verify_to_raw(runs[0].output, &runs[0].proof)
            .expect("an honest proof");
        let leaves = [(runs[0].output, raw)];
        let (built, lowered) = (tree.record(Over::Leaves(Some(&leaves)), lower)).expect("a first-level node");
        let first = tree.program(Kind::First);
        assert_eq!(
            padded(&lowered.text, tree.shape).expect("a program").digest(),
            first.digest()
        );
        assert_eq!(Machine::new(first.rv(), &built.advice).run(), Ok(built.output));

        // Mutation: one bit of an advice word, for words across the whole proof: the program traps.
        //
        // A word the program writes before reading it, or never reads, is zero in the advice, so each word taken is not.
        let words = (0..built.advice.len()).filter(|&i| built.advice[i] != 0);
        for at in words.step_by(TAMPER_STRIDE) {
            let mut forged = built.advice.clone();
            forged[at] ^= 1 << (at % 64);
            let outcome = Machine::new(first.rv(), &forged).run();
            assert!(outcome.is_err(), "advice word {at}: {outcome:?}");
        }

        // The root binds the outputs and their order.
        let mut swapped = outputs.clone();
        swapped.swap(0, 3);
        assert_eq!(tree.verify(&root, &swapped), Err(TreeError::Outputs));
        assert_eq!(tree.verify(&root, &outputs[..2]), Err(TreeError::Outputs));

        // Mutation: a carried claim's value, which moves the statement's hash, so the root's proof no longer verifies.
        let mut forged = root;
        let at = tree.statement.range(Section::DenseValues).start;
        forged.words[at] += F192::ONE;
        assert!(matches!(tree.verify(&forged, &outputs), Err(TreeError::Child { .. })));
    }

    #[test]
    fn a_fake_child_program_is_refused_at_the_root() {
        // Invariant: a child is bound to a tree program by the claim its core leaves on its bytecode, not by its seed.
        let program = leaf_program();
        let prover = Prover::new(Rate::MIN);
        let run = prover.prove(&program, &[7]).expect("the run halts");
        let shape = LeafShape::of(&run.proof).expect("a proof's shape");
        let tree = Tree::new(&program, &shape, 1, 2, Rate::MIN).expect("a tree");

        // Fixture: a program of the tree's shape that verifies nothing, and outputs the hash of a first-level
        // statement over the leaf's output, proven on the tree's seed.
        let mut words = vec![F192::ZERO; tree.statement.len()];
        let [d0, d1, d2, d3] = Kind::First.digest(&[*run.output.words()]);
        let at = tree.statement.range(Section::Digest).start;
        (words[at], words[at + 1]) = (F192::new(d0, d1, 0), F192::new(d2, d3, 0));
        // The claims it carries are true, at the all-zero points: only its own program is false.
        let values = tree.statement.range(Section::DenseValues).start;
        for poly in [DensePoly::Bytecode, DensePoly::Image] {
            words[values + poly as usize] = F192::from(tree.tables[poly][0]);
        }
        let matrices = tree.statement.range(Section::Matrices).start;
        let zeros = vec![F192::ZERO; FlockId::MAX_K_LOG];
        for f in FlockId::ALL {
            let [a, b] = matrices_at(f, &zeros, &zeros);
            (words[matrices + 2 * f.index()], words[matrices + 2 * f.index() + 1]) = (a, b);
        }
        let output = Tree::output(&words);
        let mut asm = Asm::new();
        for (r, &w) in Reg::OUTPUTS.into_iter().zip(output.words()) {
            asm.li(r, w);
        }
        let fake = padded(&asm.exit().finish(), tree.shape).expect("a program of the shape");
        let proven = (prover.prove_seeded(&fake, &[], tree.shape.taus, tree.seed)).expect("the fake program halts");
        let (_, raw) = fake
            .replay_seeded(output, &proven.proof, tree.seed)
            .expect("its proof verifies as its own");

        // Mutation: a prover whose hints and reduction are the fake program's, so that the honest node program runs to its exit.
        let mut evil = tree.clone();
        evil.tables[DensePoly::Fixed] = [Lookup::Bytecode.table(fake.rv()), Lookup::Bytecode.table(fake.rv())].concat();
        let children = [(words.clone(), raw.clone()), (words, raw)];
        // Its programs are the tree's own.
        let root = evil
            .prove(Kind::Node, Over::Children(Some(&children)))
            .expect("the honest node program accepts the fake children");

        // The node's own proof verifies, and its digest is that of two such leaves; the claim it carries on the tree
        // programs' bytecode is the fake's, which the root refuses.
        assert!(tree.read(&root, 0).is_ok());
        assert!(matches!(
            tree.verify(&root, &[run.output, run.output]),
            Err(TreeError::Claim(_))
        ));
    }
}
