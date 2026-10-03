//! Aggregation trees: leanVM proofs of one program at the leaves, a lift node verifying each in a recursion
//! proof, a first level of nodes each verifying `arity` lifts, and uniform nodes above it each verifying `arity`
//! nodes, up to a root the native verifier checks.
//!
//! Every recursion proof of a tree has one statement layout ([`TreeStatement`]): its kind, a digest of the leaves'
//! outputs under it, and constant-size claims on the fixed polynomials. Those are the dense ones (the program's
//! stacked bytecode table and RAM's image, the lift's fixed columns and the node circuits' fixed columns,
//! [`fixed`]) at one point, and each flock circuit's matrices at one row and one column point. A node verifies its
//! children in rows ([`child`]), which leaves fresh claims on those polynomials, and reduces them with the claims
//! its children carry to one of each ([`reduce`]); only the root's verifier evaluates them.
//!
//! The lift has its own tables' heights, which the first level's nodes verify. The two node circuits share theirs,
//! so a node above the first level verifies either kind of node with the same rows: the kind is a word of the
//! child's statement whose low bit selects its circuit's half of the nodes' fixed polynomial. The nodes' heights
//! are the least fixed point of the node's heights as a function of its children's.

pub mod child;
pub mod fixed;
pub mod reduce;

use super::circuit::{self, Builder, Circuit, Dw, Ew, FINAL, Kw, Limbs, N_TABLES};
use super::inner::core::{Shape, verify_core};
use super::inner::pcs::RingMode;
use super::inner::{MatrixClaim as InnerMatrix, ProgramClaim, math};
use super::machine;
use super::proof::{self, RecError};
use super::transcript::{Source, Transcript};
use super::{InnerProof, announced_shape, valid_shape};
use crate::class_flock;
use crate::cpu::{Lookup, Program};
use crate::pcs::Rate;
use fiat_shamir::transcript::{Proof, RawProof};
use fixed::FixedLayout;
use primitives::field::{F64, F192};
use primitives::multilinear::{eq_table, mle_eval};
use reduce::{Col, DenseClaim, MatrixClaim, Row, Weight, matrix_vars, reduce_dense, reduce_matrices};

/// The domain of a tree proof's transcript seed, versioned with the circuits.
const DOMAIN: &[u8] = b"leanvm-tree-2";
/// The domain of a node's reduction transcript.
const AGGREGATE: &[u8] = b"leanvm-tree-aggregate-1";
/// The first word of a lift's and of a node's leaf digest.
const LIFT_TAG: u64 = u64::from_le_bytes(*b"tree-lft");
const NODE_TAG: u64 = u64::from_le_bytes(*b"tree-nod");

/// The dense polynomials, in order.
pub const BYTECODE: usize = 0;
pub const IMAGE: usize = 1;
pub const LIFT_FIXED: usize = 2;
pub const NODE_FIXED: usize = 3;
const N_DENSE: usize = 4;

/// A tree proof's kind: what its circuit verifies. Its high bit says whether it is a node, its low bit whether its
/// children are.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Kind {
    /// One leanVM proof.
    Lift = 0,
    /// `arity` lifts: a node of the first level.
    First = 2,
    /// `arity` nodes, of either kind.
    Node = 3,
}

impl Kind {
    const ALL: [Self; 3] = [Self::Lift, Self::First, Self::Node];

    /// The kind a statement word names.
    fn from_word(word: u64) -> Option<Self> {
        Self::ALL.into_iter().find(|&k| k as u64 == word)
    }

    /// The position of this kind's circuit in [`Kind::ALL`].
    const fn index(self) -> usize {
        match self {
            Self::Lift => 0,
            Self::First => 1,
            Self::Node => 2,
        }
    }

    /// The kind of a node over children of this kind.
    const fn parent(self) -> Self {
        match self {
            Self::Lift => Self::First,
            Self::First | Self::Node => Self::Node,
        }
    }
}

/// What a tree proof states: its kind, the digest of the leaves' outputs under it, and its claims on the fixed
/// polynomials, which hold if the leaves verify.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TreeStatement {
    pub kind: Kind,
    pub digest: [u64; 4],
    /// The dense polynomials' point; polynomial `j` is at its first `n_vars[j]` coordinates.
    pub dense_point: Vec<F192>,
    pub dense_values: [F192; N_DENSE],
    /// The matrices' row and column points; circuit `f` is at their first `k_log(f)` coordinates.
    pub rows: Vec<F192>,
    pub cols: Vec<F192>,
    /// Per flock circuit, `A` and `B` there.
    pub matrices: Vec<[F192; 2]>,
}

/// A tree proof: its statement and the recursion proof of it.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TreeProof {
    pub statement: TreeStatement,
    pub proof: Proof,
}

/// Why a tree refuses.
#[derive(Clone, Debug, PartialEq, Eq, thiserror::Error)]
pub enum TreeError {
    /// A leaf proof's announced shape is not the tree's.
    #[error("the leaf proof's shape is not the tree's")]
    LeafShape,
    /// The leaf program and shape admit no recursion circuit.
    #[error("the leaf's shape admits no recursion circuit")]
    Shape,
    /// A node is given the wrong number of children.
    #[error("a node takes {expected} children, and {got} are given")]
    Arity { expected: usize, got: usize },
    /// A node's children are not all lifts, nor all nodes.
    #[error("child {index} is not of its siblings' level")]
    Level { index: usize },
    /// A child's statement does not have the tree's layout.
    #[error("tree proof {index}'s statement is malformed")]
    Statement { index: usize },
    /// A child does not verify.
    #[error("child {index} does not verify: {error}")]
    Child { index: usize, error: RecError },
    /// The circuit is unsatisfied: the check named here fails.
    #[error("the node's circuit does not hold: {0}")]
    Unsatisfied(String),
    /// The root proof does not verify.
    #[error(transparent)]
    Root(#[from] RecError),
    /// The root's digest is not the given leaves' outputs.
    #[error("the root does not state these leaf outputs")]
    Outputs,
    /// A claim the root carries is false.
    #[error("the root's claim on {0} is false")]
    Claim(String),
}

/// A statement's words as wires.
struct StatementWires {
    kind: Kw,
    digest: Dw,
    dense_point: Vec<Ew>,
    dense_values: Vec<Ew>,
    rows: Vec<Ew>,
    cols: Vec<Ew>,
    matrices: Vec<[Ew; 2]>,
}

impl StatementWires {
    fn es(&self) -> impl Iterator<Item = Ew> + '_ {
        (self
            .dense_point
            .iter()
            .chain(&self.dense_values)
            .chain(&self.rows)
            .chain(&self.cols))
        .copied()
        .chain(self.matrices.iter().flatten().copied())
    }

    fn expose(&self, b: &mut Builder) {
        b.expose_k(self.kind);
        b.expose_d(self.digest);
        for w in self.es() {
            b.expose_e(w);
        }
    }

    /// Each word's limbs, in statement order.
    fn limbs(&self, b: &mut Builder) -> Vec<Vec<Kw>> {
        let mut out = vec![vec![self.kind], b.d_to_k(self.digest).to_vec()];
        for w in self.es() {
            out.push(b.e_to_k(w).to_vec());
        }
        out
    }

    fn values(&self, b: &Builder) -> TreeStatement {
        let e = |ws: &[Ew]| ws.iter().map(|&w| b.e(w)).collect::<Vec<_>>();
        TreeStatement {
            kind: Kind::from_word(b.k(self.kind)).expect("the circuit exposes its own kind"),
            digest: b.d(self.digest),
            dense_point: e(&self.dense_point),
            dense_values: std::array::from_fn(|j| b.e(self.dense_values[j])),
            rows: e(&self.rows),
            cols: e(&self.cols),
            matrices: self.matrices.iter().map(|m| m.map(|w| b.e(w))).collect(),
        }
    }
}

impl TreeStatement {
    /// The statement's words, as the circuit exposes them.
    pub fn words(&self) -> Vec<Limbs> {
        let e = |x: &F192| [x.c0, x.c1, x.c2, 0];
        let mut words = vec![[self.kind as u64, 0, 0, 0], self.digest];
        words.extend(
            (self
                .dense_point
                .iter()
                .chain(&self.dense_values)
                .chain(&self.rows)
                .chain(&self.cols))
            .chain(self.matrices.iter().flatten())
            .map(e),
        );
        words
    }

    /// The words' limbs, as [`StatementWires::limbs`] reads them: one for the kind, four for the digest, three per
    /// element.
    fn limbs(&self) -> Vec<u64> {
        let words = self.words();
        let mut out = vec![words[0][0]];
        out.extend(words[1]);
        for w in &words[2..] {
            out.extend(&w[..3]);
        }
        out
    }

    /// The transcript's public input: the chained compression of the limbs.
    pub fn public_input(&self) -> [F64; 4] {
        chain(&self.limbs()).map(F64)
    }
}

/// BLAKE2s compressions from the parameter IV over `words`, eight a block, zero padded, the last final: what
/// [`chain_wires`] computes in rows.
fn chain(words: &[u64]) -> Limbs {
    let n_blocks = words.len().div_ceil(8).max(1);
    let mut h = circuit::param_iv();
    for j in 0..n_blocks {
        let m: [u64; 8] = std::array::from_fn(|i| words.get(8 * j + i).copied().unwrap_or(0));
        let f = if j + 1 == n_blocks { FINAL } else { 0 };
        let mut inputs = [0u64; 14];
        inputs[0] = 64 * (j as u64 + 1);
        inputs[1] = f;
        inputs[2..6].copy_from_slice(&h);
        inputs[6..].copy_from_slice(&m);
        h = circuit::compress_words(&inputs);
    }
    h
}

fn chain_wires(b: &mut Builder, words: &[Kw]) -> Dw {
    let n_blocks = words.len().div_ceil(8).max(1);
    let zero = b.k_const(0);
    let mut h = b.d_const(circuit::param_iv());
    for j in 0..n_blocks {
        let m: [Kw; 8] = std::array::from_fn(|i| words.get(8 * j + i).copied().unwrap_or(zero));
        h = b.leaf_block(h, m, 64 * (j as u64 + 1), j + 1 == n_blocks);
    }
    h
}

/// A lift's leaf digest: its leaf's output under the lift's tag.
pub fn lift_digest(output: [u64; 4]) -> [u64; 4] {
    chain(&[LIFT_TAG, output[0], output[1], output[2], output[3]])
}

/// A node's leaf digest: its children's under the node's tag and arity.
pub fn node_digest(children: &[[u64; 4]]) -> [u64; 4] {
    let mut words = vec![NODE_TAG, children.len() as u64, 0, 0, 0, 0, 0, 0];
    words.extend(children.iter().flatten());
    chain(&words)
}

/// The digest of a tree of `arity` over `outputs`, leaves in order, each group of `arity` one node.
///
/// # Errors
///
/// [`TreeError::Outputs`] if the leaves are not a power of `arity`.
pub fn tree_digest(outputs: &[[u64; 4]], arity: usize) -> Result<[u64; 4], TreeError> {
    if !is_power(outputs.len(), arity) {
        return Err(TreeError::Outputs);
    }
    let mut level: Vec<[u64; 4]> = outputs.iter().map(|&o| lift_digest(o)).collect();
    while level.len() > 1 {
        level = level.chunks(arity).map(node_digest).collect();
    }
    Ok(level[0])
}

/// Whether `n` leaves make a tree of `arity`: one, or a power of an arity of at least two.
const fn is_power(n: usize, arity: usize) -> bool {
    let mut n = n;
    while arity > 1 && n > 1 && n.is_multiple_of(arity) {
        n /= arity;
    }
    n == 1
}

/// `d`'s words bound into `t`: the first three as one element, the fourth as another.
fn observe_digest(b: &mut Builder, t: &mut Transcript, d: Dw) {
    let [w0, w1, w2, w3] = b.d_to_k(d);
    let first = b.k_to_e([w0, w1, w2]);
    t.observe(b, first);
    let last = b.k_to_e1(w3);
    t.observe(b, last);
}

/// What fixes a tree's circuits: the leaves' program and shape, the arity and the rate, and the lift's and the
/// nodes' heights.
struct Design<'p> {
    leaf: Shape<'p>,
    arity: usize,
    rate: Rate,
    /// The lift's heights, then the nodes'.
    taus: [[usize; N_TABLES]; 2],
    /// The lift's fixed columns' layout, then the nodes'.
    fixed: [FixedLayout; 2],
    /// The dense polynomials' variables.
    n_vars: [usize; N_DENSE],
}

/// What a tree's prover and verifier hold: the design, the three circuits and the fixed polynomials' tables.
pub struct Tree<'p> {
    design: Design<'p>,
    pub lift: Circuit,
    pub first: Circuit,
    pub node: Circuit,
    /// Each circuit's fixed columns, in [`Kind::ALL`]'s order.
    columns: [Vec<Vec<F64>>; 3],
    tables: [Vec<F64>; N_DENSE],
    iv: [F64; 4],
}

impl<'p> Design<'p> {
    fn new(leaf: Shape<'p>, arity: usize, rate: Rate, taus: [[usize; N_TABLES]; 2]) -> Self {
        let fixed = taus.map(|t| FixedLayout::new(&t));
        let rv = leaf.program.rv();
        let kbc = crate::log2_strict_usize(rv.entries().len());
        let n_vars = [
            kbc + crate::leaf::N_TUPLE_BITS,
            crate::log2_ceil_usize(rv.image().len().max(1)),
            fixed[0].omega,
            fixed[1].omega + 1,
        ];
        Self {
            leaf,
            arity,
            rate,
            taus,
            fixed,
            n_vars,
        }
    }

    /// The heights of `kind`'s circuit.
    const fn taus(&self, kind: Kind) -> &[usize; N_TABLES] {
        match kind {
            Kind::Lift => &self.taus[0],
            Kind::First | Kind::Node => &self.taus[1],
        }
    }

    fn n_dense(&self) -> usize {
        self.n_vars.iter().copied().max().expect("four polynomials")
    }

    /// How many words a statement has.
    fn statement_len(&self) -> usize {
        2 + self.n_dense() + N_DENSE + 2 * matrix_vars() + 2 * class_flock::N_FLOCKS
    }

    /// The transcript's seed for every proof of the tree.
    fn iv(&self) -> [F64; 4] {
        let mut h = primitives::hash::Hasher::new();
        h.update(DOMAIN);
        h.update(self.leaf.program.digest());
        for x in self
            .leaf
            .taus
            .iter()
            .chain(&[self.leaf.log_inv_rate, self.arity])
            .chain(self.taus.iter().flatten())
        {
            h.update(&(*x as u64).to_le_bytes());
        }
        h.update(&[self.rate.log_inv_rate()]);
        h.update(&(self.statement_len() as u64).to_le_bytes());
        fiat_shamir::digest_words(&h.finalize())
    }

    /// The reduction's transcript, from its label.
    fn aggregate(b: &mut Builder) -> Transcript<'static> {
        let cv = b.d_const(fiat_shamir::digest_words(&primitives::hash::hash(AGGREGATE)).map(|w| w.0));
        Transcript::from_state(cv, Source::Shape)
    }

    /// Reduce the claims and expose the statement.
    #[expect(
        clippy::too_many_arguments,
        reason = "the statement's parts and the claims to reduce"
    )]
    fn finish(
        &self,
        b: &mut Builder,
        t: &mut Transcript,
        kind: Kind,
        digest: Dw,
        dense: &[DenseClaim],
        matrices: &[MatrixClaim],
        tables: Option<&[Vec<F64>; N_DENSE]>,
    ) -> StatementWires {
        let tables: Option<Vec<&[F64]>> = tables.map(|ts| ts.iter().map(Vec::as_slice).collect());
        let dense = crate::stage!("Dense reduction", || b.scope("dense reduction", |b| {
            reduce_dense(b, t, &self.n_vars, tables.as_deref(), dense)
        }));
        let m = crate::stage!("Matrix reduction", || b.scope("matrix reduction", |b| {
            reduce_matrices(b, t, tables.is_some(), matrices)
        }));
        let kind = b.k_const(kind as u64);
        let s = StatementWires {
            kind,
            digest,
            dense_point: dense.point,
            dense_values: dense.values,
            rows: m.rows,
            cols: m.cols,
            matrices: m.values,
        };
        s.expose(b);
        s
    }

    /// The lift's circuit verifying `leaf` (its proof and output), from the shape alone when `None`; `tables`
    /// the dense polynomials when proving.
    fn lift(
        &self,
        leaf: Option<(&RawProof, [u64; 4])>,
        tables: Option<&[Vec<F64>; N_DENSE]>,
    ) -> (Builder, StatementWires) {
        let mut b = Builder::new();
        let source = leaf.map_or(Source::Shape, |(p, _)| Source::Proof(p));
        let output = leaf.map_or([0; 4], |(_, o)| o).map(|o| b.free_k(o));
        let core = b.scope("leaf", |b| verify_core(b, &self.leaf, output, source, RingMode::Prove));
        let zero = b.k_const(0);
        let tag = b.k_const(LIFT_TAG);
        let digest = chain_wires(&mut b, &[tag, output[0], output[1], output[2], output[3], zero]);
        let (dense, hints) = b.scope("program claim", |b| self.program_claims(b, &core.program, tables));
        let matrices: Vec<MatrixClaim> = core.circuits.iter().enumerate().map(|(f, c)| fresh(f, c)).collect();
        let mut t = Self::aggregate(&mut b);
        observe_digest(&mut b, &mut t, core.state);
        for h in hints {
            t.observe(&mut b, h);
        }
        let s = self.finish(&mut b, &mut t, Kind::Lift, digest, &dense, &matrices, tables);
        (b, s)
    }

    /// The program claim as point claims on the bytecode table and RAM's image: each multiplicity bit's
    /// Frobenius twist `μ_i·φ^i(T̂(φ^{-i}(χ), α))` by its value `D_i`, a hint, at the point `(φ^{-i}(χ), α)`, and
    /// the image at its point less the variables above the image, where it is zero.
    fn program_claims(
        &self,
        b: &mut Builder,
        p: &ProgramClaim,
        tables: Option<&[Vec<F64>; N_DENSE]>,
    ) -> (Vec<DenseClaim>, Vec<Ew>) {
        let kbc = self.n_vars[BYTECODE] - crate::leaf::N_TUPLE_BITS;
        let (chi, alpha) = p.bytecode.split_at(kbc);
        let bits = p.twist.len();
        let ladders: Vec<Vec<Ew>> = chi
            .iter()
            .map(|&x| math::inverse_frobenius_ladder(b, x, 1, bits))
            .collect();
        let mut claims = Vec::with_capacity(bits + 1);
        let mut hints = Vec::with_capacity(bits + 1);
        let mut total = b.zero();
        for i in 0..bits {
            let mut point: Vec<Ew> = ladders.iter().map(|l| l[i]).collect();
            point.extend(alpha);
            let value = tables.map_or(F192::ZERO, |ts| {
                let at: Vec<F192> = point.iter().map(|&w| b.e(w)).collect();
                mle_eval(&ts[BYTECODE], &at)
            });
            let d = b.free_e(value);
            let mut twisted = d;
            for _ in 0..i {
                twisted = b.square(twisted);
            }
            total = b.mul_add(p.twist[i], twisted, total);
            claims.push(DenseClaim::at(BYTECODE, point, d));
            hints.push(d);
        }
        let m = self.n_vars[IMAGE];
        let low = p.image_point[..m].to_vec();
        let value = tables.map_or(F192::ZERO, |ts| {
            let at: Vec<F192> = low.iter().map(|&w| b.e(w)).collect();
            mle_eval(&ts[IMAGE], &at)
        });
        let image = b.free_e(value);
        let zero_above = (p.image_point[m..].iter()).fold(p.image_weight, |acc, &x| math::times_one_plus(b, acc, x));
        total = b.mul_add(zero_above, image, total);
        b.eq_e(total, p.value);
        claims.push(DenseClaim::at(IMAGE, low, image));
        hints.push(image);
        (claims, hints)
    }

    /// The circuit of a node of `kind` (`First` over lifts, `Node` over nodes) verifying `children` (each its
    /// statement and proof as its verifier read it), from the shape alone when `None`; `columns` and `tables` the
    /// circuits' fixed columns and the dense polynomials when proving.
    fn node(
        &self,
        kind: Kind,
        children: Option<&[(&TreeStatement, RawProof)]>,
        columns: Option<&[Vec<Vec<F64>>; 3]>,
        tables: Option<&[Vec<F64>; N_DENSE]>,
    ) -> (Builder, StatementWires) {
        let mut b = Builder::new();
        let iv = b.d_const(self.iv().map(|w| w.0));
        let n_dense = self.n_dense();
        let k = matrix_vars();
        let over_lifts = kind == Kind::First;
        let (taus, fixed, poly) = if over_lifts {
            (&self.taus[0], &self.fixed[0], LIFT_FIXED)
        } else {
            (&self.taus[1], &self.fixed[1], NODE_FIXED)
        };
        let mut digests = Vec::with_capacity(self.arity);
        let mut dense = Vec::new();
        let mut matrices = Vec::new();
        let mut states = Vec::with_capacity(self.arity);
        for i in 0..self.arity {
            let child = children.map(|c| &c[i]);
            let zero = TreeStatement::zero(n_dense, k, if over_lifts { Kind::Lift } else { Kind::First });
            let stmt = child.map_or(&zero, |c| c.0);
            let s = StatementWires {
                kind: b.free_k(stmt.kind as u64),
                digest: b.free_d(stmt.digest),
                dense_point: stmt.dense_point.iter().map(|&x| b.free_e(x)).collect(),
                dense_values: stmt.dense_values.iter().map(|&x| b.free_e(x)).collect(),
                rows: stmt.rows.iter().map(|&x| b.free_e(x)).collect(),
                cols: stmt.cols.iter().map(|&x| b.free_e(x)).collect(),
                matrices: stmt.matrices.iter().map(|m| m.map(|x| b.free_e(x))).collect(),
            };
            // A lift's kind is zero; a node's low bit says whether its children are nodes, and selects its half of
            // the nodes' fixed polynomial.
            let top = b.scope(format!("child {i} kind"), |b| {
                if over_lifts {
                    b.eq_k_const(s.kind, Kind::Lift as u64);
                    vec![]
                } else {
                    let word = b.k_to_e1(s.kind);
                    let over_nodes = b.add_const(word, F192::from(F64(Kind::First as u64)));
                    let square = b.square(over_nodes);
                    b.eq_e(square, over_nodes);
                    vec![over_nodes]
                }
            });
            let limbs = s.limbs(&mut b);
            let flat: Vec<Kw> = limbs.iter().flatten().copied().collect();
            let pi = chain_wires(&mut b, &flat);
            let [p0, p1, p2, p3] = b.d_to_k(pi);
            let first = b.k_to_e([p0, p1, p2]);
            let source = child.map_or(Source::Shape, |c| Source::Proof(&c.1));
            let mut t = Transcript::new(&mut b, iv, (first, p3), source);
            let cols = columns.map(|cs| cs[stmt.kind.index()].as_slice());
            let verified = b.scope(format!("child {i}"), |b| {
                child::verify_child(
                    b,
                    &mut t,
                    taus,
                    self.rate.log_inv_rate().into(),
                    &limbs,
                    &top,
                    fixed,
                    cols,
                    poly,
                )
            });
            for (j, &n) in self.n_vars.iter().enumerate() {
                dense.push(DenseClaim::at(j, s.dense_point[..n].to_vec(), s.dense_values[j]));
            }
            dense.push(verified.fixed);
            matrices.push(fresh(machine::hash_flock(), &verified.matrix));
            for (f, &[va, vb]) in s.matrices.iter().enumerate() {
                let kf = class_flock::shape(f).k_log;
                for (weights, value) in [([Weight::One, Weight::Zero], va), ([Weight::Zero, Weight::One], vb)] {
                    matrices.push(MatrixClaim {
                        circuit: f,
                        row: Row::Point(s.rows[..kf].to_vec()),
                        col: Col::Point(s.cols[..kf].to_vec()),
                        weights,
                        value,
                    });
                }
            }
            digests.push(s.digest);
            states.push((verified.state, dense.len() - 1));
        }
        let mut words = vec![b.k_const(NODE_TAG), b.k_const(self.arity as u64)];
        words.resize(8, b.k_const(0));
        for &d in &digests {
            words.extend(b.d_to_k(d));
        }
        let digest = chain_wires(&mut b, &words);
        let mut t = Self::aggregate(&mut b);
        for &(state, fixed) in &states {
            observe_digest(&mut b, &mut t, state);
            t.observe(&mut b, dense[fixed].value);
        }
        let s = self.finish(&mut b, &mut t, kind, digest, &dense, &matrices, tables);
        (b, s)
    }
}

/// A fresh claim from a lincheck: `uᵀ(A + α·B)w` at its quirky row point and its sliced column point.
fn fresh(circuit: usize, c: &InnerMatrix) -> MatrixClaim {
    MatrixClaim {
        circuit,
        row: Row::Quirky {
            z: c.z_skip,
            rest: c.x_inner_rest.clone(),
        },
        col: Col::Slices {
            slices: c.s_hat_v.clone(),
            rest: c.r_inner_rest.clone(),
        },
        weights: [Weight::One, Weight::W(c.alpha)],
        value: c.value,
    }
}

impl TreeStatement {
    /// The statement of these dimensions and `kind` with every other word zero, which a circuit built from its
    /// shape reads.
    fn zero(n_dense: usize, k: usize, kind: Kind) -> Self {
        Self {
            kind,
            digest: [0; 4],
            dense_point: vec![F192::ZERO; n_dense],
            dense_values: [F192::ZERO; N_DENSE],
            rows: vec![F192::ZERO; k],
            cols: vec![F192::ZERO; k],
            matrices: vec![[F192::ZERO; 2]; class_flock::N_FLOCKS],
        }
    }

    fn well_formed(&self, n_dense: usize) -> bool {
        let k = matrix_vars();
        self.dense_point.len() == n_dense
            && self.rows.len() == k
            && self.cols.len() == k
            && self.matrices.len() == class_flock::N_FLOCKS
    }
}

/// `heights` raised to `floor`, table by table.
fn max_taus(a: [usize; N_TABLES], b: [usize; N_TABLES]) -> [usize; N_TABLES] {
    std::array::from_fn(|t| a[t].max(b[t]))
}

impl<'p> Tree<'p> {
    /// The tree over proofs of `program` of shape `leaf_taus` at `leaf_log_inv_rate`, each node verifying
    /// `arity` children, every recursion proof at `rate`.
    ///
    /// # Errors
    ///
    /// [`TreeError::Shape`] if no proof of `program` has the leaf shape, or the arity is zero.
    pub fn new(
        program: &'p Program,
        leaf_taus: [usize; crate::tables::N_TABLES],
        leaf_log_inv_rate: usize,
        arity: usize,
        rate: Rate,
    ) -> Result<Self, TreeError> {
        if arity == 0 || !valid_shape(program, &leaf_taus, leaf_log_inv_rate) {
            return Err(TreeError::Shape);
        }
        let leaf = Shape {
            program,
            taus: leaf_taus,
            log_inv_rate: leaf_log_inv_rate,
        };
        let heights = |b: Builder| proof::heights(&b.finish().0);
        let at = |taus| Design::new(leaf, arity, rate, taus);
        let lift = heights(at([[0; N_TABLES]; 2]).lift(None, None).0);
        let first = heights(at([lift, [0; N_TABLES]]).node(Kind::First, None, None, None).0);
        let mut taus = [lift, first];
        let design = loop {
            let design = at(taus);
            let lift = heights(design.lift(None, None).0);
            let first = heights(design.node(Kind::First, None, None, None).0);
            let node = heights(design.node(Kind::Node, None, None, None).0);
            let next = [max_taus(taus[0], lift), max_taus(taus[1], max_taus(first, node))];
            if next == taus {
                break design;
            }
            taus = next;
        };
        let circuits = Kind::ALL.map(|kind| {
            let b = match kind {
                Kind::Lift => design.lift(None, None).0,
                _ => design.node(kind, None, None, None).0,
            };
            let mut circuit = b.finish().0;
            circuit.floor = *design.taus(kind);
            debug_assert_eq!(proof::heights(&circuit), circuit.floor);
            circuit
        });
        if circuits
            .iter()
            .any(|c| proof::Layout::new(c).shape.mu > crate::pcs::MAX_MU)
        {
            return Err(TreeError::Shape);
        }
        let columns = Kind::ALL.map(|kind| machine::fixed_values(&circuits[kind.index()], design.taus(kind)));
        let [lift_layout, node_layout] = &design.fixed;
        let lift_table = lift_layout.stack(&columns[0]);
        let mut node_table = node_layout.stack(&columns[1]);
        node_table.extend(node_layout.stack(&columns[2]));
        let rv = program.rv();
        let mut image: Vec<F64> = rv.image().iter().map(|&w| F64(w)).collect();
        image.resize(1 << design.n_vars[IMAGE], F64::ZERO);
        let tables = [Lookup::Bytecode.table(rv), image, lift_table, node_table];
        let iv = design.iv();
        let [lift, first, node] = circuits;
        Ok(Self {
            design,
            lift,
            first,
            node,
            columns,
            tables,
            iv,
        })
    }

    pub const fn program(&self) -> &'p Program {
        self.design.leaf.program
    }

    /// The circuit of a proof of this kind.
    pub const fn circuit(&self, kind: Kind) -> &Circuit {
        match kind {
            Kind::Lift => &self.lift,
            Kind::First => &self.first,
            Kind::Node => &self.node,
        }
    }

    /// Prove one leaf in a lift node.
    ///
    /// # Errors
    ///
    /// Refuses a leaf of another shape and one that does not verify.
    pub fn prove_lift(&self, leaf: &InnerProof) -> Result<TreeProof, TreeError> {
        let d = &self.design;
        if leaf.program.digest() != d.leaf.program.digest() {
            return Err(TreeError::LeafShape);
        }
        if announced_shape(&leaf.proof.stream) != Some((d.leaf.taus, d.leaf.log_inv_rate)) {
            return Err(TreeError::LeafShape);
        }
        let (b, s) = crate::stage!("Build circuit", || d
            .lift(Some((&leaf.proof, leaf.output)), Some(&self.tables)));
        self.prove(b, &s, Kind::Lift)
    }

    /// Prove one node over `children`, in order: a first-level node over lifts, or a node over nodes.
    ///
    /// # Errors
    ///
    /// Refuses the wrong number of children, children of two levels, and a child that does not verify.
    pub fn prove_node(&self, children: &[TreeProof]) -> Result<TreeProof, TreeError> {
        let d = &self.design;
        if children.len() != d.arity {
            return Err(TreeError::Arity {
                expected: d.arity,
                got: children.len(),
            });
        }
        let kind = children[0].statement.kind.parent();
        let read = children
            .iter()
            .enumerate()
            .map(|(index, c)| {
                if !c.statement.well_formed(d.n_dense()) {
                    return Err(TreeError::Statement { index });
                }
                if c.statement.kind.parent() != kind {
                    return Err(TreeError::Level { index });
                }
                let raw = self.read(c).map_err(|error| TreeError::Child { index, error })?;
                Ok((&c.statement, raw))
            })
            .collect::<Result<Vec<_>, _>>()?;
        let (b, s) = crate::stage!("Build circuit", || d.node(
            kind,
            Some(&read),
            Some(&self.columns),
            Some(&self.tables)
        ));
        self.prove(b, &s, kind)
    }

    /// Prove the tree over `leaves`, in order: a lift each, then each level's nodes over `arity` proofs of the
    /// level below, up to the root.
    ///
    /// # Errors
    ///
    /// [`TreeError::Outputs`] unless the leaves are a power of the arity, and whatever refuses a leaf.
    pub fn prove_tree(&self, leaves: &[InnerProof]) -> Result<TreeProof, TreeError> {
        let arity = self.design.arity;
        if !is_power(leaves.len(), arity) {
            return Err(TreeError::Outputs);
        }
        let mut level: Vec<TreeProof> = leaves.iter().map(|l| self.prove_lift(l)).collect::<Result<_, _>>()?;
        while level.len() > 1 {
            level = level
                .chunks(arity)
                .map(|c| self.prove_node(c))
                .collect::<Result<_, _>>()?;
        }
        Ok(level.pop().expect("one root"))
    }

    /// Verify a tree proof's recursion proof alone, short of what its statement claims.
    ///
    /// # Errors
    ///
    /// The recursion proof does not verify.
    pub fn verify_proof(&self, p: &TreeProof) -> Result<(), TreeError> {
        if !p.statement.well_formed(self.design.n_dense()) {
            return Err(TreeError::Statement { index: 0 });
        }
        self.read(p)?;
        Ok(())
    }

    /// Verify a tree proof's recursion proof, returning it as its verifier read it.
    fn read(&self, p: &TreeProof) -> Result<RawProof, RecError> {
        proof::verify_to_raw(
            self.circuit(p.statement.kind),
            &p.statement.words(),
            self.iv,
            p.statement.public_input(),
            self.design.rate.log_inv_rate().into(),
            &p.proof,
        )
    }

    fn prove(&self, b: Builder, s: &StatementWires, kind: Kind) -> Result<TreeProof, TreeError> {
        let statement = s.values(&b);
        let (mut circuit, assignment, failures) = b.finish();
        if let Some(first) = failures.into_iter().next() {
            return Err(TreeError::Unsatisfied(first));
        }
        circuit.floor = *self.design.taus(kind);
        assert!(&circuit == self.circuit(kind), "the circuit is the shape's");
        let proof = proof::prove(
            &circuit,
            &assignment,
            self.iv,
            statement.public_input(),
            self.design.rate,
        );
        Ok(TreeProof { statement, proof })
    }

    /// Verify a tree's root: its recursion proof, that it states the leaves' outputs `outputs`, and every claim
    /// it carries, against the program and the circuits.
    ///
    /// # Errors
    ///
    /// Returns the first check that refuses.
    pub fn verify(&self, root: &TreeProof, outputs: &[[u64; 4]]) -> Result<(), TreeError> {
        let d = &self.design;
        let s = &root.statement;
        if !s.well_formed(d.n_dense()) {
            return Err(TreeError::Statement { index: 0 });
        }
        let kind = match outputs.len() {
            1 => Kind::Lift,
            n if n == d.arity => Kind::First,
            _ => Kind::Node,
        };
        if s.kind != kind {
            return Err(TreeError::Outputs);
        }
        self.read(root)?;
        if s.digest != tree_digest(outputs, d.arity)? {
            return Err(TreeError::Outputs);
        }
        self.settle(s)
    }

    /// The claims a statement carries, evaluated.
    fn settle(&self, s: &TreeStatement) -> Result<(), TreeError> {
        let names = [
            "the bytecode table",
            "RAM's image",
            "the lift's fixed columns",
            "the nodes' fixed columns",
        ];
        for (j, &n) in self.design.n_vars.iter().enumerate() {
            if mle_eval(&self.tables[j], &s.dense_point[..n]) != s.dense_values[j] {
                return Err(TreeError::Claim(names[j].into()));
            }
        }
        for (f, &[va, vb]) in s.matrices.iter().enumerate() {
            let circuit = class_flock::circuit(f);
            let k = circuit.k_log();
            let u = eq_table(&s.rows[..k]);
            let (ra, rb) = circuit.row_values(&eq_table(&s.cols[..k]));
            let dot = |r: &[F192]| u.iter().zip(r).fold(F192::ZERO, |acc, (&x, &y)| acc + x * y);
            if dot(&ra) != va || dot(&rb) != vb {
                let (t, part) = class_flock::flock(f);
                return Err(TreeError::Claim(format!(
                    "the {} {part:?} circuit's matrices",
                    crate::tables::CLASSES[t].name
                )));
            }
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests;
