//! Aggregation trees: leaf proofs of one or more families, recursion proofs above them, one root the native verifier checks.
//!
//! ```text
//!                 node                  verifies arity tree proofs of any kind
//!               /      \
//!        first-level   first-level      each verifies arity_0 leaves of one family
//!          /  \          /  \
//!       leaf  leaf    leaf  leaf
//! ```
//!
//! A leaf family is RISC-V proofs of one program, at most one such family per tree, or proofs of one recursion circuit
//! (a batch of signatures, say). Each family has its first-level kind; nodes take children of any kind, so one tree
//! mixes families.
//!
//! Every tree proof states the same words, whatever the tree's size:
//!
//! - its kind, and a digest of what the leaves under it state;
//! - one claim on each dense polynomial the tree has: the RISC-V program's bytecode table and RAM image, the leaf circuits' fixed polynomial, and the nodes' fixed polynomial, which holds every kind's circuit's fixed columns;
//! - each flock circuit's two matrices at one row point and one column point.
//!
//! Each node reduces the claims its children leave and carry to one of each, and only the root's verifier evaluates them.

use crate::class_flock::FlockId;
use crate::cpu::{Announcement, DecodeError, Output, Program, Proof, ProvenRun, Stats, VerifyError};
use crate::envelope::Envelope;
use crate::pcs::Rate;
use crate::rec::circuit::{Circuit, Finished, Limbs};
use crate::rec::fixed::FixedColumns;
use crate::rec::layout::RecLayout;
use crate::rec::proof::statement_seed;
use crate::rec::table::PerRecTable;
use crate::rec::transcript::ProofSource;
use crate::rec::verifier::ProofShape;
use crate::tables::PerTable;
use design::{ChildWitness, CircuitFamily, CircuitWitness, Design, Family, LeafWitness, NodeInputs, NodeRows};
use fiat_shamir::transcript::{ProofTranscript, RawProof};
use primitives::field::{F64, F192};
use primitives::multilinear::{eq_table, mle_eval_par};
use reduce::DenseTables;
use statement::{Level, TreeStatement};
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

/// The shape every RISC-V leaf proof of a tree shares.
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

/// A recursion circuit whose proofs are leaves of a tree: its circuit, its fixed columns, its transcript's seed and its proofs' rate.
///
/// A batch of signatures gives it (`XmssBatch::leaves`).
#[derive(Clone, Copy)]
pub struct LeafCircuit<'p> {
    /// The circuit.
    pub(crate) circuit: &'p Circuit,
    /// Its fixed columns at its heights.
    pub(crate) columns: &'p FixedColumns,
    /// Its proofs' transcript's seed, which names the circuit and its size.
    pub(crate) iv: [F64; 4],
    /// Its proofs' rate.
    pub(crate) rate: Rate,
}

/// One family of a tree's leaves.
#[derive(Clone, Copy)]
pub enum Leaves<'p> {
    /// RISC-V proofs of one program, of one shape.
    Runs {
        /// The program.
        program: &'p Program,
        /// The proofs' shape.
        shape: LeafShape,
    },
    /// Proofs of one recursion circuit.
    Circuit(LeafCircuit<'p>),
}

/// One leaf of a tree: a proof, and what it proves.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Leaf<'a>(LeafProof<'a>);

/// A leaf's proof and what it proves.
#[derive(Clone, Debug, PartialEq, Eq)]
enum LeafProof<'a> {
    /// A RISC-V proof of a run, and the output it claims.
    Run { proof: &'a Proof, output: Output },
    /// A proof of the recursion circuit of seed `iv`, and its statement.
    Circuit {
        iv: Limbs,
        statement: Vec<Limbs>,
        proof: &'a ProofTranscript,
        rate: Rate,
    },
}

/// What one leaf states, which the root's verifier is given.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LeafStatement(Stated);

/// What a leaf states: a run's output, or a recursion circuit's statement.
#[derive(Clone, Debug, PartialEq, Eq)]
enum Stated {
    /// A RISC-V proof's output.
    Run(Output),
    /// The statement of a proof of the recursion circuit of seed `iv`.
    Circuit { iv: Limbs, words: Vec<Limbs> },
}

/// The tree a root is expected to cover: its shape, and what each leaf states.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Subtree {
    /// A first-level node: what its leaves state, in order, every leaf of one family.
    First(Vec<LeafStatement>),
    /// A node: its children, in order.
    Node(Vec<Self>),
}

/// How a tree is shaped.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct TreeShape {
    /// The leaf proofs a first-level node verifies, at least one.
    pub arity_0: usize,
    /// The tree proofs a higher node verifies, at least two.
    pub arity: usize,
    /// The commitment rate of every tree proof.
    pub rate: Rate,
}

/// An aggregation tree over leaf proofs of some families.
///
/// It is the tree's verifying key, and what its prover needs.
///
/// It is built from the leaf families and the shape alone, before any proof exists.
pub struct Tree<'p> {
    /// How it is shaped.
    shape: TreeShape,
    /// What fixes the circuits.
    design: Design<'p>,
    /// Each kind's circuit, by code.
    circuits: Vec<Circuit>,
    /// Each kind's circuit's fixed columns, by code.
    columns: Vec<FixedColumns>,
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
    /// Leaf families that make no tree: none, two of RISC-V proofs, or one recursion circuit twice.
    #[error("a tree has at least one leaf family, at most one of RISC-V proofs, and each recursion circuit once")]
    Families,
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
    /// A number of leaves no balanced tree of these arities has.
    #[error("{leaves} leaves make no tree of a first level of {arity_0} and nodes of {arity}")]
    LeafCount {
        /// How many leaves.
        leaves: usize,
        /// The first level's arity.
        arity_0: usize,
        /// The nodes' arity.
        arity: usize,
    },
    /// A leaf of no family of the tree, of another family than its node's first, or of another shape than its family's.
    #[error("leaf {index} is of another family or shape than its first-level node's")]
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
    /// A child whose kind is none of the tree's.
    #[error("child {index} is of no kind of the tree")]
    ForeignChild {
        /// The child's index among its node's.
        index: usize,
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
    /// The root is not of the kind the expected tree's top gives.
    #[error("the expected tree has a {expected:?} root, and the proof is a {got:?}")]
    Kind {
        /// The kind the expected tree gives.
        expected: Kind,
        /// The proof's.
        got: Kind,
    },
    /// The root's recursion proof does not verify.
    #[error("the root: {0}")]
    Root(VerifyError),
    /// The root's digest is not that of the expected tree.
    #[error("the root does not state the expected tree's leaves")]
    Digest,
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
        let scalars = proof.0.stream.get(..Announcement::LEN)?.try_into().ok()?;
        let announcement = Announcement::decode(scalars).ok()?;
        Some(Self::new(announcement.taus, announcement.rate))
    }
}

impl<'p> LeafCircuit<'p> {
    /// The leaf circuit of a circuit, its fixed columns at its heights, its proofs' seed and rate.
    pub(crate) const fn new(circuit: &'p Circuit, columns: &'p FixedColumns, iv: [F64; 4], rate: Rate) -> Self {
        Self {
            circuit,
            columns,
            iv,
            rate,
        }
    }

    /// Its seed, as words.
    fn seed(&self) -> Limbs {
        self.iv.map(|w| w.0)
    }
}

impl TreeShape {
    /// The levels of nodes of the balanced tree over this many leaves: zero for a first-level node over `n_0`, `d` over `n_0 n^d`.
    ///
    /// # Errors
    ///
    /// A number of leaves no tree of these arities has.
    pub fn depth(&self, leaves: usize) -> Result<usize, TreeError> {
        let Self { arity_0, arity, .. } = *self;
        let count = TreeError::LeafCount { leaves, arity_0, arity };
        if leaves == 0 || arity_0 == 0 || arity < 2 || !leaves.is_multiple_of(arity_0) {
            return Err(count);
        }
        let (mut nodes, mut depth) = (leaves / arity_0, 0);
        while nodes > 1 && nodes.is_multiple_of(arity) {
            nodes /= arity;
            depth += 1;
        }
        if nodes == 1 { Ok(depth) } else { Err(count) }
    }
}

impl<'a> Leaf<'a> {
    /// The leaf of a RISC-V proof and the output it proves.
    #[must_use]
    pub const fn new(proof: &'a Proof, output: Output) -> Self {
        Self(LeafProof::Run { proof, output })
    }

    /// The leaf of a proof of a leaf circuit at `rate`, and the statement it proves.
    pub(crate) fn circuit(
        leaf: &LeafCircuit<'_>,
        statement: Vec<Limbs>,
        proof: &'a ProofTranscript,
        rate: Rate,
    ) -> Self {
        Self(LeafProof::Circuit {
            iv: leaf.seed(),
            statement,
            proof,
            rate,
        })
    }

    /// What it states.
    #[must_use]
    pub fn statement(&self) -> LeafStatement {
        LeafStatement(match &self.0 {
            LeafProof::Run { output, .. } => Stated::Run(*output),
            LeafProof::Circuit { iv, statement, .. } => Stated::Circuit {
                iv: *iv,
                words: statement.clone(),
            },
        })
    }
}

impl<'a> From<&'a ProvenRun> for Leaf<'a> {
    fn from(run: &'a ProvenRun) -> Self {
        Self::new(&run.proof, run.output)
    }
}

impl LeafStatement {
    /// The statement of a proof of a leaf circuit.
    pub(crate) fn circuit(leaf: &LeafCircuit<'_>, words: Vec<Limbs>) -> Self {
        Self(Stated::Circuit { iv: leaf.seed(), words })
    }
}

impl From<Output> for LeafStatement {
    fn from(output: Output) -> Self {
        Self(Stated::Run(output))
    }
}

impl Subtree {
    /// The balanced tree over these leaves, in order: first-level nodes of `arity_0` consecutive leaves, then nodes of `arity` consecutive children up to one root.
    ///
    /// # Errors
    ///
    /// A number of leaves no tree of the shape's arities has.
    pub fn balanced(leaves: Vec<LeafStatement>, shape: &TreeShape) -> Result<Self, TreeError> {
        shape.depth(leaves.len())?;
        let mut level: Vec<Self> = groups(leaves, shape.arity_0).into_iter().map(Self::First).collect();
        while level.len() > 1 {
            level = groups(level, shape.arity).into_iter().map(Self::Node).collect();
        }
        Ok(level.pop().expect("one root"))
    }
}

/// The items in consecutive groups of `n`, the last one shorter if they do not divide.
fn groups<T>(items: Vec<T>, n: usize) -> Vec<Vec<T>> {
    let mut items = items.into_iter().peekable();
    let mut out = Vec::new();
    while items.peek().is_some() {
        out.push(items.by_ref().take(n).collect());
    }
    out
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
    /// The tree over leaves of these families, by index (`Kind::First(i)` verifies family `i`), shaped as given.
    ///
    /// The circuits are built from the families and the shape alone, so a verifier needs no proof to build its key.
    ///
    /// # Errors
    ///
    /// - Arities that make no tree: a first level of no leaf, or nodes of fewer than two children.
    /// - No family, two of RISC-V proofs, or one recursion circuit twice.
    /// - A leaf shape no proof of the program has.
    /// - Circuits that fit no commitment.
    pub fn new(leaves: &[Leaves<'p>], shape: TreeShape) -> Result<Self, TreeError> {
        let TreeShape { arity_0, arity, rate } = shape;
        if arity_0 == 0 || arity < 2 {
            return Err(TreeError::Arity { arity_0, arity });
        }
        let runs = leaves.iter().filter(|l| matches!(l, Leaves::Runs { .. })).count();
        let seeds: Vec<Limbs> = (leaves.iter())
            .filter_map(|l| match l {
                Leaves::Circuit(c) => Some(c.seed()),
                Leaves::Runs { .. } => None,
            })
            .collect();
        let repeated = (seeds.iter().enumerate()).any(|(i, s)| seeds[..i].contains(s));
        if leaves.is_empty() || runs > 1 || repeated {
            return Err(TreeError::Families);
        }
        let families = || {
            let mut slot = 0;
            (leaves.iter())
                .map(|&l| match l {
                    Leaves::Runs { program, shape } => ProofShape::new(program, shape.taus, shape.rate)
                        .map(Family::Runs)
                        .map_err(|e| TreeError::LeafShape(e.into())),
                    Leaves::Circuit(c) => {
                        slot += 1;
                        CircuitFamily::new(c, slot - 1).map(Family::Circuit)
                    }
                })
                .collect::<Result<Vec<_>, _>>()
        };
        let (design, circuits) = Self::converge(|taus| Design::new(families()?, arity_0, arity, rate, taus))?;
        let columns: Vec<FixedColumns> = circuits.iter().map(|c| FixedColumns::of(c, &design.taus)).collect();
        let tables = design.tables(&columns);
        Ok(Self {
            shape,
            design,
            circuits,
            columns,
            tables,
        })
    }

    /// The heights every kind's circuit shares, and the circuits at them, by code.
    ///
    /// They are the least fixed point of `tau -> max(tau, max_k circuit_k(tau))`, from the first-level circuits' own heights.
    ///
    /// Each round only raises heights, and a node's rows grow with the logarithm of its children's, so few rounds reach it.
    fn converge(
        design: impl Fn(PerRecTable<usize>) -> Result<Design<'p>, TreeError>,
    ) -> Result<(Design<'p>, Vec<Circuit>), TreeError> {
        let max = |taus: PerRecTable<usize>, built: &[Circuit]| {
            PerRecTable::from_fn(|t| built.iter().map(|c| c.heights()[t]).fold(taus[t], usize::max))
        };
        let start = design(PerRecTable::default())?;
        let firsts: Vec<Circuit> = (start.kinds().into_iter())
            .filter(|&k| k != Kind::Node)
            .map(|k| start.shape(k).circuit)
            .collect();
        let mut taus = max(PerRecTable::default(), &firsts);
        for _ in 0..MAX_ROUNDS {
            let d = design(taus)?;
            let built: Vec<Circuit> = d.kinds().into_iter().map(|k| d.shape(k).circuit).collect();
            let next = max(taus, &built);
            if next == taus {
                let circuits = (built.into_iter())
                    .map(|mut c| {
                        c.floor = taus;
                        c
                    })
                    .collect();
                RecLayout::from_taus(taus).map_err(|_| TreeError::TooLarge)?;
                return Ok((d, circuits));
            }
            taus = next;
        }
        Err(TreeError::TooLarge)
    }

    /// Every kind of the tree's proofs, by code: a first-level node per leaf family, and a node.
    #[must_use]
    pub fn kinds(&self) -> Vec<Kind> {
        self.design.kinds()
    }

    /// Whether a kind is one of the tree's.
    const fn has(&self, kind: Kind) -> bool {
        kind.code() < self.circuits.len()
    }

    /// The circuit of a proof of this kind, one of the tree's.
    pub(crate) fn circuit(&self, kind: Kind) -> &Circuit {
        &self.circuits[kind.code()]
    }

    /// The circuit of a proof of this kind as `CheckRec` reads it: the builder calls that make it, one per line, then `circuit` and the circuit's dump, then `next` and the bus's `next` key of every slot of the circuit's rows, per table, row-major.
    ///
    /// # Panics
    ///
    /// Panics if building the circuit again gives another circuit.
    #[cfg(feature = "circuit-trace")]
    pub fn circuit_dump(&self, kind: Kind) -> String {
        let (finished, calls) = crate::rec::circuit::traced(|| self.design.shape(kind));
        let mut circuit = finished.circuit;
        circuit.floor = self.circuit(kind).floor;
        assert_eq!(&circuit, self.circuit(kind), "a circuit is built the same every time");
        calls + "circuit\n" + &circuit.dump() + &self.columns[kind.code()].dump_next(&circuit)
    }

    /// The family of a leaf of this seed, or of a RISC-V proof with none.
    fn family(&self, seed: Option<Limbs>) -> Option<usize> {
        (self.design.families.iter()).position(|f| match (f, seed) {
            (Family::Runs(_), None) => true,
            (Family::Circuit(c), Some(seed)) => c.leaf.seed() == seed,
            _ => false,
        })
    }

    /// Prove a first-level node over its leaves, in order, all of one family.
    ///
    /// # Errors
    ///
    /// The wrong number of leaves, a leaf of no family of the tree, of another family than the first or of another shape than its family's, or a leaf that does not verify.
    pub fn prove_first(&self, leaves: &[Leaf<'_>]) -> Result<TreeProof, TreeError> {
        let d = &self.design;
        if leaves.len() != d.arity_0 {
            return Err(TreeError::Children {
                expected: d.arity_0,
                got: leaves.len(),
            });
        }
        let seed = |l: &Leaf<'_>| match l.0 {
            LeafProof::Run { .. } => None,
            LeafProof::Circuit { iv, .. } => Some(iv),
        };
        let family = (self.family(seed(&leaves[0]))).ok_or(TreeError::ForeignLeaf { index: 0 })?;
        let kind = Kind::First(family);
        let foreign = |index| TreeError::ForeignLeaf { index };
        let rows = match &d.families[family] {
            Family::Runs(shape) => {
                let announced = LeafShape::new(*shape.taus(), shape.rate());
                let items = (leaves.iter().enumerate())
                    .map(|(index, leaf)| {
                        let LeafProof::Run { proof, output } = leaf.0 else {
                            return Err(foreign(index));
                        };
                        if LeafShape::announced(proof) != Some(announced) {
                            return Err(foreign(index));
                        }
                        let raw = (shape.program().verify_to_raw(output, proof)).map_err(|error| TreeError::Leaf {
                            index,
                            error: error.into(),
                        })?;
                        Ok(LeafWitness {
                            raw,
                            output: *output.words(),
                        })
                    })
                    .collect::<Result<Vec<_>, _>>()?;
                let inputs = NodeInputs::Prove {
                    items: &items,
                    tables: &self.tables,
                };
                info_span!("Build circuit").in_scope(|| d.first_runs(kind, shape, &inputs))
            }
            Family::Circuit(family) => {
                let c = &family.leaf;
                let items = (leaves.iter().enumerate())
                    .map(|(index, leaf)| {
                        let LeafProof::Circuit {
                            iv,
                            ref statement,
                            proof,
                            rate,
                        } = leaf.0
                        else {
                            return Err(foreign(index));
                        };
                        let words = statement.len() == c.circuit.statement_len && statement.iter().all(|w| w[3] == 0);
                        if iv != c.seed() || rate != c.rate || !words {
                            return Err(foreign(index));
                        }
                        let raw = (c.circuit.verify_to_raw_with(statement, c.iv, c.rate, proof, c.columns)).map_err(
                            |error| TreeError::Leaf {
                                index,
                                error: error.into(),
                            },
                        )?;
                        Ok(CircuitWitness {
                            statement: statement.clone(),
                            raw,
                            columns: c.columns,
                        })
                    })
                    .collect::<Result<Vec<_>, _>>()?;
                let inputs = NodeInputs::Prove {
                    items: &items,
                    tables: &self.tables,
                };
                info_span!("Build circuit").in_scope(|| d.first_circuit(kind, family, &inputs))
            }
        };
        self.prove_rows(rows, kind)
    }

    /// Prove a node over its children, tree proofs of any kind, in order.
    ///
    /// # Errors
    ///
    /// The wrong number of children, a child of no kind of the tree, or a child that does not verify.
    pub fn prove_node(&self, children: &[TreeProof]) -> Result<TreeProof, TreeError> {
        let d = &self.design;
        if children.len() != d.arity {
            return Err(TreeError::Children {
                expected: d.arity,
                got: children.len(),
            });
        }
        let raws = (children.iter().enumerate())
            .map(|(index, c)| {
                if !self.has(c.kind) {
                    return Err(TreeError::ForeignChild { index });
                }
                self.read(c).map_err(|error| TreeError::Child { index, error })
            })
            .collect::<Result<Vec<_>, _>>()?;
        let statements: Vec<TreeStatement> = (children.iter())
            .map(|c| TreeStatement::new(d.statement, c.words.clone()))
            .collect();
        let items: Vec<ChildWitness<'_>> = (children.iter().zip(&statements).zip(raws))
            .map(|((c, statement), raw)| ChildWitness {
                statement,
                raw,
                columns: &self.columns[c.kind.code()],
            })
            .collect();
        let inputs = NodeInputs::Prove {
            items: &items,
            tables: &self.tables,
        };
        let rows = info_span!("Build circuit").in_scope(|| d.node(&inputs));
        self.prove_rows(rows, Kind::Node)
    }

    /// Prove the balanced tree over its leaves, in order, each first-level node's of one family.
    ///
    /// The first level, then each level of nodes, up to the root.
    ///
    /// # Errors
    ///
    /// A number of leaves no tree of the arities has, or a leaf the first level refuses.
    pub fn prove(&self, leaves: &[Leaf<'_>]) -> Result<TreeProof, TreeError> {
        self.shape.depth(leaves.len())?;
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

    /// Verify a root: its recursion proof, that it covers the expected tree, and every claim it carries.
    ///
    /// # Errors
    ///
    /// Returns the first check that refuses.
    #[tracing::instrument(name = "Verify tree", skip_all)]
    pub fn verify(&self, root: &TreeProof, expected: &Subtree) -> Result<(), TreeError> {
        let d = &self.design;
        if root.rate != d.rate {
            return Err(TreeError::Rate {
                expected: d.rate,
                got: root.rate,
            });
        }
        let (kind, digest) = self.expect(expected)?;
        if root.kind != kind {
            return Err(TreeError::Kind {
                expected: kind,
                got: root.kind,
            });
        }
        self.read(root).map_err(TreeError::Root)?;
        let statement = TreeStatement::new(d.statement, root.words.clone());
        if statement.digest_words() != digest {
            return Err(TreeError::Digest);
        }
        self.settle(&statement, root.kind)
    }

    /// The kind and the digest of the root of an expected tree.
    fn expect(&self, tree: &Subtree) -> Result<(Kind, Limbs), TreeError> {
        let d = &self.design;
        let count = |expected, got| {
            (got == expected)
                .then_some(())
                .ok_or(TreeError::Children { expected, got })
        };
        match tree {
            Subtree::First(leaves) => {
                count(d.arity_0, leaves.len())?;
                let seed = |l: &LeafStatement| match l.0 {
                    Stated::Run(_) => None,
                    Stated::Circuit { iv, .. } => Some(iv),
                };
                let first = seed(&leaves[0]);
                let family = self.family(first).ok_or(TreeError::ForeignLeaf { index: 0 })?;
                if let Some(index) = leaves.iter().position(|l| seed(l) != first) {
                    return Err(TreeError::ForeignLeaf { index });
                }
                let items: Vec<Limbs> = (leaves.iter())
                    .map(|l| match &l.0 {
                        Stated::Run(output) => *output.words(),
                        Stated::Circuit { words, .. } => statement_seed(words).map(|w| w.0),
                    })
                    .collect();
                let level = first.map_or(Level::Runs, Level::Circuit);
                Ok((Kind::First(family), level.digest(&items)))
            }
            Subtree::Node(children) => {
                count(d.arity, children.len())?;
                let digests = (children.iter())
                    .map(|c| self.expect(c).map(|(_, digest)| digest))
                    .collect::<Result<Vec<_>, _>>()?;
                Ok((Kind::Node, Level::Node.digest(&digests)))
            }
        }
    }

    /// Verify a tree proof's recursion proof, short of its claims, returning it as its verifier read it.
    fn read(&self, p: &TreeProof) -> Result<RawProof, VerifyError> {
        let limbs: Vec<[u64; 4]> = p.words.iter().map(|w| [w.c0, w.c1, w.c2, 0]).collect();
        let raw = self.circuit(p.kind).verify_to_raw_with(
            &limbs,
            self.design.iv,
            self.design.rate,
            &p.proof,
            &self.columns[p.kind.code()],
        )?;
        Ok(raw)
    }

    /// Prove a circuit's rows: its reduction, then its recursion proof.
    fn prove_rows(&self, rows: NodeRows, kind: Kind) -> Result<TreeProof, TreeError> {
        let d = &self.design;
        let reduction = rows.claim_values().prove(&d.vars, &self.tables);
        let raw = RawProof {
            stream: reduction.stream,
            merkle: Vec::new(),
        };
        let Finished {
            assignment, failures, ..
        } = info_span!("Reduce in rows").in_scope(|| rows.reduce(d, ProofSource::Proof(&raw)));
        if let Some(first) = failures.into_iter().next() {
            return Err(TreeError::Unsatisfied(first));
        }
        let proof = (self.circuit(kind))
            .prove_with(&assignment, d.iv, d.rate, Some(&self.columns[kind.code()]))
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

    /// Evaluate every claim a root's statement carries: each dense polynomial a proof of its kind carries a claim on, and every flock circuit's matrices.
    #[tracing::instrument(name = "Settle claims", skip_all)]
    fn settle(&self, s: &TreeStatement, kind: Kind) -> Result<(), TreeError> {
        let d = &self.design;
        for poly in DensePoly::ALL.into_iter().filter(|&p| d.active(kind, p)) {
            let point = &s.dense_point()[..d.vars.0[poly as usize]];
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
