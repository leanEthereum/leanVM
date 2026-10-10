//! Aggregation trees: RISC-V proofs of one program at the leaves, recursion proofs above them, one root the native verifier checks.
//!
//! ```text
//!                 node                  verifies arity recursion proofs of either kind
//!               /      \
//!        first-level   first-level      each verifies arity_0 RISC-V proofs
//!          /  \          /  \
//!       leaf  leaf    leaf  leaf
//! ```
//!
//! Every tree proof states the same words, whatever the tree's size:
//!
//! - its kind, and a digest of the leaves' outputs under it;
//! - one claim on each of the bytecode table, RAM's image and the nodes' fixed polynomial, which holds both circuits' fixed columns;
//! - each flock circuit's two matrices at one row point and one column point.
//!
//! Each node reduces the claims its children leave and carry to one of each, and only the root's verifier evaluates them.

use crate::class_flock::FlockId;
use crate::cpu::{Announcement, DecodeError, Lookup, Output, Program, Proof, ProvenRun, Stats, VerifyError};
use crate::envelope::Envelope;
use crate::pcs::Rate;
use crate::rec::circuit::{Circuit, Finished};
use crate::rec::fixed::FixedColumns;
use crate::rec::layout::RecLayout;
use crate::rec::table::PerRecTable;
use crate::rec::transcript::ProofSource;
use crate::rec::verifier::ProofShape;
use crate::tables::PerTable;
use design::{ChildWitness, Design, LeafWitness, NodeInputs, NodeRows};
use fiat_shamir::{FromNarg, ProofTranscript};
use primitives::field::{F64, F192};
use primitives::multilinear::{eq_table, mle_eval_par};
use reduce::DenseTables;
use statement::TreeStatement;
use thiserror::Error;
use tracing::info_span;

mod claims;
mod design;
mod fixed;
mod reduce;
mod statement;
mod stats;
#[cfg(test)]
mod tests;

pub use crate::rec::circuit::Unsatisfied;
pub use crate::tables::Part;
pub use claims::DensePoly;
pub use statement::Kind;
pub use stats::{CircuitStats, TableStats};

/// The most rounds the search for the nodes' heights takes: each round at least doubles a table.
const MAX_ROUNDS: usize = 8;

/// The shape every leaf proof of a tree shares.
///
/// It is each table's height and the commitment's rate, as a proof announces them.
///
/// A tree's circuits are built from it, so they verify leaves of that shape only.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct LeafShape {
    /// Each table's base-two logarithm of rows.
    taus: PerTable<usize>,
    /// The commitment's rate.
    rate: Rate,
}

/// One leaf of a tree: a proof of a run, and the output it proves.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Leaf<'a> {
    /// The proof of the run.
    proof: &'a Proof,
    /// The output the proof claims.
    output: Output,
}

/// How a tree is shaped.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct TreeShape {
    /// The shape every leaf proof shares.
    pub leaf: LeafShape,
    /// The leaf proofs a first-level node verifies, at least one.
    pub arity_0: usize,
    /// The tree proofs a higher node verifies, at least two.
    pub arity: usize,
    /// The commitment rate of every tree proof.
    pub rate: Rate,
}

/// An aggregation tree over proofs of one program.
///
/// It is the tree's verifying key, and what its prover needs.
///
/// It is built from the program and the shape alone, before any proof exists.
pub struct Tree<'p> {
    /// How it is shaped.
    shape: TreeShape,
    /// What fixes the circuits.
    design: Design<'p>,
    /// Each kind's circuit, the first level's first.
    circuits: [Circuit; 2],
    /// Each kind's circuit's fixed columns, the first level's first.
    columns: [FixedColumns; 2],
    /// The dense polynomials the root's claims are settled against.
    tables: DenseTables,
}

/// A proof made by one node of a tree, the root's included.
///
/// A first-level node's proof covers leaf proofs.
///
/// A higher node's proof covers tree proofs.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TreeProof {
    /// What its circuit verifies, its statement's first word.
    kind: Kind,
    /// Its statement's words.
    words: Vec<F192>,
    /// The recursion proof.
    proof: ProofTranscript,
    /// The rate it is proven at.
    rate: Rate,
}

/// A claim of a root's statement that is false.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Error)]
pub enum FalseClaim {
    /// A claim on a dense polynomial.
    #[error("on {0:?}")]
    Dense(DensePoly),
    /// A claim on a flock circuit's matrices.
    #[error("on the {table} table's {part:?} circuit's matrices")]
    Matrix {
        /// The table.
        table: &'static str,
        /// Which of its circuits.
        part: Part,
    },
}

/// Why a tree cannot be built, a tree proof cannot be made, or a root is refused.
#[derive(Clone, Debug, PartialEq, Eq, Error)]
pub enum TreeError {
    /// The arities make no tree: a first level takes at least one leaf, a node at least two children.
    #[error("a first level of {arity_0} leaves and nodes of {arity} children make no tree")]
    Arity {
        /// The leaves a first-level node verifies.
        arity_0: usize,
        /// The children a node verifies.
        arity: usize,
    },
    /// No RISC-V proof of the program has the leaves' shape.
    #[error("the leaves' shape: {0}")]
    LeafShape(VerifyError),
    /// No recursion circuit of the shapes fits one commitment.
    #[error("the tree's circuits fit no commitment")]
    TooLarge,
    /// A node is given the wrong number of proofs.
    #[error("a node of {expected} children is given {got}")]
    Children {
        /// The node's arity.
        expected: usize,
        /// How many it is given.
        got: usize,
    },
    /// A number of leaves no tree of these arities has.
    #[error("{leaves} leaves make no tree of a first level of {arity_0} and nodes of {arity}")]
    LeafCount {
        /// How many leaves.
        leaves: usize,
        /// The first level's arity.
        arity_0: usize,
        /// The nodes' arity.
        arity: usize,
    },
    /// A leaf proof announces another shape than the tree's.
    #[error("leaf {index} has another shape than the tree's")]
    ForeignLeaf {
        /// The leaf's index among its node's.
        index: usize,
    },
    /// A leaf proof does not verify.
    #[error("leaf {index}: {error}")]
    Leaf {
        /// The leaf's index among its node's.
        index: usize,
        /// Why its verifier refuses it.
        error: VerifyError,
    },
    /// A child proof does not verify.
    #[error("child {index}: {error}")]
    Child {
        /// The child's index among its node's.
        index: usize,
        /// Why its verifier refuses it.
        error: VerifyError,
    },
    /// The circuit's rows do not hold on the prover's values.
    #[error("the circuit does not hold: {0}")]
    Unsatisfied(Unsatisfied),
    /// A proof at another rate than the tree's.
    #[error(
        "a proof at log-inv-rate {}, and the tree's is {}",
        .got.log_inv_rate(),
        .expected.log_inv_rate()
    )]
    Rate {
        /// The tree's.
        expected: Rate,
        /// The proof's.
        got: Rate,
    },
    /// The root is not of the kind its number of leaves gives.
    #[error("{leaves} leaves have a {expected:?} root, and the proof is a {got:?}")]
    Kind {
        /// How many leaves.
        leaves: usize,
        /// The kind they give.
        expected: Kind,
        /// The proof's.
        got: Kind,
    },
    /// The root's recursion proof does not verify.
    #[error("the root: {0}")]
    Root(VerifyError),
    /// The root's digest is not that of the given leaves' outputs.
    #[error("the root does not state these leaf outputs")]
    Outputs,
    /// A claim the root carries is false.
    #[error("the root's claim {0} is false")]
    Claim(FalseClaim),
}

impl LeafShape {
    /// The shape of proofs with these table heights at this rate.
    pub(crate) const fn new(taus: PerTable<usize>, rate: Rate) -> Self {
        Self { taus, rate }
    }

    /// The shape a proof announces.
    ///
    /// # Errors
    ///
    /// A proof whose announcement is not valid.
    pub fn of(proof: &Proof) -> Result<Self, DecodeError> {
        Self::announced(proof).ok_or(DecodeError::Malformed)
    }

    /// The shape a proof of a run would announce, from the run's measured cost.
    ///
    /// So a tree's key is built before any leaf is proven.
    #[must_use]
    pub fn measured(stats: &Stats, rate: Rate) -> Self {
        // Every proven table height is a power of two, so its logarithm is exact.
        Self::new(stats.counts.map(|rows| rows.ilog2() as usize), rate)
    }

    /// The shape a proof's first scalars announce, if they are a valid announcement.
    fn announced(proof: &Proof) -> Option<Self> {
        let mut narg = proof.0.narg.as_slice();
        let scalars: [F192; Announcement::LEN] =
            std::array::from_fn(|_| F192::from_narg(&mut narg).unwrap_or_default());
        let announcement = Announcement::decode(&scalars).ok()?;
        Some(Self::new(announcement.taus, announcement.rate))
    }
}

impl TreeShape {
    /// The kind of the root over this many leaves: a first-level node over `n_0`, a node over `n_0 n^d`.
    ///
    /// # Errors
    ///
    /// A number of leaves no tree of these arities has.
    pub fn root_kind(&self, leaves: usize) -> Result<Kind, TreeError> {
        let Self { arity_0, arity, .. } = *self;
        let count = TreeError::LeafCount { leaves, arity_0, arity };
        if leaves == 0 || arity < 2 || !leaves.is_multiple_of(arity_0) {
            return Err(count);
        }
        let mut nodes = leaves / arity_0;
        while nodes > 1 && nodes.is_multiple_of(arity) {
            nodes /= arity;
        }
        match (nodes, leaves == arity_0) {
            (1, true) => Ok(Kind::First),
            (1, false) => Ok(Kind::Node),
            _ => Err(count),
        }
    }
}

impl<'a> Leaf<'a> {
    /// The leaf of a proof and the output it proves.
    #[must_use]
    pub const fn new(proof: &'a Proof, output: Output) -> Self {
        Self { proof, output }
    }
}

impl<'a> From<&'a ProvenRun> for Leaf<'a> {
    fn from(run: &'a ProvenRun) -> Self {
        Self::new(&run.proof, run.output)
    }
}

impl TreeProof {
    /// The header of a tree proof's bytes: the magic `LVMT`, then the tree protocol's version.
    ///
    /// The version is bumped by every change to what a tree proof says.
    const ENVELOPE: Envelope = Envelope::new(*b"LVMT", 14);

    /// The kind of node that made the proof.
    #[must_use]
    pub const fn kind(&self) -> Kind {
        self.kind
    }

    /// The proof's bytes.
    #[must_use]
    pub fn to_bytes(&self) -> Vec<u8> {
        Self::ENVELOPE.seal(&self.body())
    }

    /// The tree proof these bytes encode.
    ///
    /// # Errors
    ///
    /// - Bytes that are no tree proof.
    /// - A tree proof of another protocol version.
    pub fn from_bytes(bytes: &[u8]) -> Result<Self, DecodeError> {
        // The header first: a foreign version is refused before its body is read.
        let body = Self::ENVELOPE.open(bytes)?;
        Self::from_body(body).ok_or(DecodeError::Malformed)
    }

    /// The body behind the header: its rate, its statement's words, then the recursion proof.
    ///
    /// ```text
    /// | log_inv_rate: u8 | n_words: u32 | words: 24 bytes each | proof |
    /// ```
    fn body(&self) -> Vec<u8> {
        let n_words = u32::try_from(self.words.len()).expect("a statement of a few hundred words");
        let mut bytes = vec![self.rate.log_inv_rate()];
        bytes.extend(n_words.to_le_bytes());
        for w in &self.words {
            bytes.extend([w.c0, w.c1, w.c2].iter().flat_map(|l| l.to_le_bytes()));
        }
        bytes.extend(self.proof.to_bytes());
        bytes
    }

    /// The tree proof a body encodes, if it encodes one and nothing more.
    fn from_body(bytes: &[u8]) -> Option<Self> {
        let (&rate, rest) = bytes.split_first()?;
        let (n_words, rest) = rest.split_first_chunk::<4>()?;
        let n_words = usize::try_from(u32::from_le_bytes(*n_words)).ok()?;
        let (words, proof) = rest.split_at_checked(n_words.checked_mul(24)?)?;
        let words: Vec<F192> = (words.as_chunks::<24>().0.iter())
            .map(|w| {
                let limb = |i: usize| u64::from_le_bytes(w[8 * i..8 * i + 8].try_into().expect("eight bytes"));
                F192::new(limb(0), limb(1), limb(2))
            })
            .collect();
        Some(Self {
            kind: Kind::of_word(*words.first()?)?,
            words,
            proof: ProofTranscript::from_bytes(proof)?,
            rate: Rate::new(rate).ok()?,
        })
    }
}

impl<'p> Tree<'p> {
    /// The tree over proofs of a program, shaped as given.
    ///
    /// The circuits are built from the shapes alone, so a verifier needs no proof to build its key.
    ///
    /// # Errors
    ///
    /// - Arities that make no tree: a first level of no leaf, or nodes of fewer than two children.
    /// - A leaf shape no proof of the program has.
    /// - Circuits that fit no commitment.
    pub fn new(program: &'p Program, shape: TreeShape) -> Result<Self, TreeError> {
        let TreeShape {
            leaf: leaves,
            arity_0,
            arity,
            rate,
        } = shape;
        if arity_0 == 0 || arity < 2 {
            return Err(TreeError::Arity { arity_0, arity });
        }
        let leaf = || ProofShape::new(program, leaves.taus, leaves.rate).map_err(|e| TreeError::LeafShape(e.into()));
        let (design, circuits) = Self::converge(|taus| Design::new(leaf()?, arity_0, arity, rate, taus))?;
        let columns = circuits.each_ref().map(|c| FixedColumns::of(c, &design.taus));
        let fixed = design.fixed.polynomial([&columns[0], &columns[1]]);
        let rv = program.rv();
        let mut image: Vec<F64> = rv.image().iter().map(|&w| F64(w)).collect();
        image.resize(1 << design.vars.0[DensePoly::Image as usize], F64::ZERO);
        let tables = DenseTables([Lookup::Bytecode.table(rv), image, fixed]);
        Ok(Self {
            shape,
            design,
            circuits,
            columns,
            tables,
        })
    }

    /// The heights both circuits share, and the circuits at them.
    ///
    /// They are the least fixed point of `tau -> max(tau, first(tau), node(tau))`, from the first level's own heights.
    ///
    /// Each round only raises heights, and a node's rows grow with the logarithm of its children's, so few rounds reach it.
    fn converge(
        design: impl Fn(PerRecTable<usize>) -> Result<Design<'p>, TreeError>,
    ) -> Result<(Design<'p>, [Circuit; 2]), TreeError> {
        let mut taus = design(PerRecTable::default())?.shape(Kind::First).circuit.heights();
        for _ in 0..MAX_ROUNDS {
            let d = design(taus)?;
            let built = Kind::ALL.map(|kind| d.shape(kind).circuit);
            let next = PerRecTable::from_fn(|t| built.iter().map(|c| c.heights()[t]).fold(taus[t], usize::max));
            if next == taus {
                let circuits = built.map(|mut c| {
                    c.floor = taus;
                    c
                });
                RecLayout::from_taus(taus).map_err(|_| TreeError::TooLarge)?;
                return Ok((d, circuits));
            }
            taus = next;
        }
        Err(TreeError::TooLarge)
    }

    /// The circuit of a proof of this kind.
    pub(crate) const fn circuit(&self, kind: Kind) -> &Circuit {
        &self.circuits[kind as usize]
    }

    /// Prove a first-level node over its leaves, each a RISC-V proof and its output, in order.
    ///
    /// # Errors
    ///
    /// The wrong number of leaves, a leaf of another shape, or a leaf that does not verify.
    pub fn prove_first(&self, leaves: &[Leaf<'_>]) -> Result<TreeProof, TreeError> {
        let d = &self.design;
        if leaves.len() != d.arity_0 {
            return Err(TreeError::Children {
                expected: d.arity_0,
                got: leaves.len(),
            });
        }
        let shape = LeafShape::new(*d.leaf.taus(), d.leaf.rate());
        let program = d.leaf.program();
        let items = (leaves.iter().enumerate())
            .map(|(index, &Leaf { proof, output })| {
                if LeafShape::announced(proof) != Some(shape) {
                    return Err(TreeError::ForeignLeaf { index });
                }
                program
                    .verify(output, proof)
                    .map_err(|error| TreeError::Leaf { index, error })?;
                Ok(LeafWitness {
                    proof: &proof.0,
                    output: *output.words(),
                })
            })
            .collect::<Result<Vec<_>, _>>()?;
        let inputs = NodeInputs::Prove {
            items: &items,
            tables: &self.tables,
        };
        let rows = info_span!("Build circuit").in_scope(|| d.first(&inputs));
        self.prove_rows(rows, Kind::First)
    }

    /// Prove a node over its children, tree proofs of either kind, in order.
    ///
    /// # Errors
    ///
    /// The wrong number of children, or a child that does not verify.
    pub fn prove_node(&self, children: &[TreeProof]) -> Result<TreeProof, TreeError> {
        let d = &self.design;
        if children.len() != d.arity {
            return Err(TreeError::Children {
                expected: d.arity,
                got: children.len(),
            });
        }
        for (index, c) in children.iter().enumerate() {
            self.read(c).map_err(|error| TreeError::Child { index, error })?;
        }
        let statements: Vec<TreeStatement> = (children.iter())
            .map(|c| TreeStatement::new(d.statement, c.words.clone()))
            .collect();
        let items: Vec<ChildWitness<'_>> = (children.iter().zip(&statements))
            .map(|(c, statement)| ChildWitness {
                statement,
                proof: &c.proof,
                columns: &self.columns[c.kind as usize],
            })
            .collect();
        let inputs = NodeInputs::Prove {
            items: &items,
            tables: &self.tables,
        };
        let rows = info_span!("Build circuit").in_scope(|| d.node(&inputs));
        self.prove_rows(rows, Kind::Node)
    }

    /// Prove the tree over its leaves, each a RISC-V proof and its output, in order.
    ///
    /// The first level, then each level of nodes, up to the root.
    ///
    /// # Errors
    ///
    /// A number of leaves no tree of the arities has, or a leaf the first level refuses.
    pub fn prove(&self, leaves: &[Leaf<'_>]) -> Result<TreeProof, TreeError> {
        self.shape.root_kind(leaves.len())?;
        let (arity_0, arity) = (self.design.arity_0, self.design.arity);
        let mut level: Vec<TreeProof> = (leaves.chunks(arity_0))
            .map(|leaves| self.prove_first(leaves))
            .collect::<Result<_, _>>()?;
        while level.len() > 1 {
            level = level
                .chunks(arity)
                .map(|c| self.prove_node(c))
                .collect::<Result<_, _>>()?;
        }
        Ok(level.pop().expect("one root"))
    }

    /// Verify a root: its recursion proof, that it states these leaf outputs in order, and every claim it carries.
    ///
    /// # Errors
    ///
    /// Returns the first check that refuses.
    #[tracing::instrument(name = "Verify tree", skip_all)]
    pub fn verify(&self, root: &TreeProof, outputs: &[Output]) -> Result<(), TreeError> {
        let d = &self.design;
        if root.rate != d.rate {
            return Err(TreeError::Rate {
                expected: d.rate,
                got: root.rate,
            });
        }
        let expected = self.shape.root_kind(outputs.len())?;
        if root.kind != expected {
            return Err(TreeError::Kind {
                leaves: outputs.len(),
                expected,
                got: root.kind,
            });
        }
        self.read(root).map_err(TreeError::Root)?;
        let statement = TreeStatement::new(d.statement, root.words.clone());
        if statement.digest_words() != self.digest(outputs) {
            return Err(TreeError::Outputs);
        }
        self.settle(&statement, root.kind)
    }

    /// The digest the root over these leaf outputs states.
    fn digest(&self, outputs: &[Output]) -> [u64; 4] {
        let (arity_0, arity) = (self.design.arity_0, self.design.arity);
        let outputs: Vec<[u64; 4]> = outputs.iter().map(|output| *output.words()).collect();
        let mut level: Vec<[u64; 4]> = outputs.chunks(arity_0).map(|o| Kind::First.digest(o)).collect();
        while level.len() > 1 {
            level = level.chunks(arity).map(|c| Kind::Node.digest(c)).collect();
        }
        level[0]
    }

    /// Verify a tree proof's recursion proof, short of its claims.
    fn read(&self, p: &TreeProof) -> Result<(), VerifyError> {
        let limbs: Vec<[u64; 4]> = p.words.iter().map(|w| [w.c0, w.c1, w.c2, 0]).collect();
        self.circuit(p.kind).verify_with(
            &limbs,
            &self.design.session,
            self.design.rate,
            &p.proof,
            &self.columns[p.kind as usize],
        )?;
        Ok(())
    }

    /// Prove a circuit's rows: its reduction, then its recursion proof.
    fn prove_rows(&self, rows: NodeRows, kind: Kind) -> Result<TreeProof, TreeError> {
        let d = &self.design;
        let reduction = rows.claim_values().prove(&d.session, &d.vars, &self.tables);
        let Finished {
            assignment, failures, ..
        } = info_span!("Reduce in rows").in_scope(|| rows.reduce(d, ProofSource::Proof(&reduction)));
        if let Some(first) = failures.into_iter().next() {
            return Err(TreeError::Unsatisfied(first));
        }
        let proof = (self.circuit(kind))
            .prove_with(&assignment, &d.session, d.rate, Some(&self.columns[kind as usize]))
            .map_err(|_| TreeError::TooLarge)?;
        let words = (assignment.statement().iter())
            .map(|l| F192::new(l[0], l[1], l[2]))
            .collect();
        Ok(TreeProof {
            kind,
            words,
            proof,
            rate: d.rate,
        })
    }

    /// Evaluate every claim a root's statement carries.
    #[tracing::instrument(name = "Settle claims", skip_all)]
    fn settle(&self, s: &TreeStatement, kind: Kind) -> Result<(), TreeError> {
        let vars = &self.design.vars.0;
        for poly in DensePoly::ALL {
            // A first-level node reduces no claim on the fixed polynomial.
            if poly == DensePoly::Fixed && kind == Kind::First {
                continue;
            }
            let point = &s.dense_point()[..vars[poly as usize]];
            if mle_eval_par(&self.tables.0[poly as usize], point) != s.dense_value(poly) {
                return Err(TreeError::Claim(FalseClaim::Dense(poly)));
            }
        }
        let held = parallel::map_collect(FlockId::ALL.len(), |f| {
            let f = FlockId::ALL[f];
            let circuit = f.circuit();
            let k = circuit.k_log();
            let (ra, rb) = circuit.row_values(&eq_table(&s.cols()[..k]));
            let u = eq_table(&s.rows()[..k]);
            let dot = |r: &[F192]| u.iter().zip(r).fold(F192::ZERO, |acc, (&x, &y)| acc + x * y);
            [dot(&ra), dot(&rb)] == s.matrices(f)
        });
        (FlockId::ALL.into_iter().zip(held))
            .find(|&(_, h)| !h)
            .map_or(Ok(()), |(f, _)| {
                Err(TreeError::Claim(FalseClaim::Matrix {
                    table: f.table().name(),
                    part: f.part(),
                }))
            })
    }
}
