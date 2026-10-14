//! Aggregation trees: leaf proofs of one family, recursion proofs above them, one root the native verifier checks.
//!
//! ```text
//!                 node                  verifies arity tree proofs of any kind
//!               /      \
//!        first-level   first-level      each verifies arity_0 leaves
//!          /  \          /  \
//!       leaf  leaf    leaf  leaf
//! ```
//!
//! A tree's leaves are of one family: RISC-V proofs of one program, or proofs of one recursion circuit (a batch of
//! signatures, say). The tree's session names the family, so a tree proof verifies under a tree of its own family only.
//!
//! Every tree proof states the same words, whatever the tree's size:
//!
//! - its kind, and a digest;
//! - one claim on each dense polynomial the tree has: the RISC-V program's bytecode table and RAM image, or the leaf circuit's fixed polynomial, and the nodes' fixed polynomial, which holds every circuit's fixed columns;
//! - each flock circuit's two matrices at one row point and one column point.
//!
//! Each node reduces the claims its children leave and carry to one of each, and only the root's verifier evaluates them.
//!
//! A tree has one of two semantics, which its shape fixes:
//!
//! - **Outputs**: the digest is of what the leaves under the proof state, in order, through the tree's fixed shape.
//! - **Claim sets**: the leaves publish claim sets, and the digest is of the set the proof declares: by default the
//!   union of its children's sets, or any part of it. Each node proves every claim it declares is one of its
//!   children's (`union`), so every claim of the root's set is one a leaf published, whatever the tree's shape: anyone
//!   may combine any proofs of the tree, up to its largest arity, and the root's verifier needs the set alone. What a
//!   claim means is the leaf's (`multiset`). A RISC-V leaf's output is the hash of its set's digest; a signature
//!   circuit's leaf publishes one group, a claim a signature, read from its statement (`leaf_set`).
//!
//! A claim-set tree has a node circuit for each arity from two to its largest, all of one height, or two tiers each
//! at heights of its own (a small tier): small proofs then never pay for the largest node's union and children.

use crate::commitment::Rate;
use crate::cpu::{Output, Program, Proof, ProvenRun, VerifyError};
use crate::rec::circuit::{Circuit, Finished, Limbs, chain};
use crate::rec::fixed::FixedColumns;
use crate::rec::proof::CircuitKey;
use crate::rec::table::{Heights, Table};
use crate::rec::transcript::ProofSource;
use crate::rec::verifier::ProofShape;
use crate::tables::CircuitId;
use design::{
    ChildWitness, CircuitFamily, CircuitWitness, Design, Family, LARGE, LeafWitness, Level, NodeInputs, NodeRows, SMALL,
};
use fiat_shamir::{LengthPrefixed, ProofTranscript, ProverState, SessionId};
pub(crate) use leaf_set::{ClaimLayout, ClaimWord};
use pcs::merkle::Openings;
use primitives::field::F192;
use primitives::multilinear::{eq_table, mle_eval_par};
use reduce::DenseTables;
use statement::{Items, TreeStatement};
use thiserror::Error;
use tracing::info_span;
use union::{FillError, UnionFill};

mod design;
mod leaf_set;

mod multiset;
mod proof;
mod reduce;
mod shape;
mod statement;

mod union;

pub use crate::rec::circuit::Unsatisfied;
pub use crate::tables::Part;
pub use multiset::{Capacity, Claim, ClaimGroup, ClaimSet, ClaimSetError};
pub use proof::TreeProof;
pub use reduce::DensePoly;
pub use shape::{ClaimShape, LeafShape, Tier, TreeShape};
pub use statement::Kind;

/// The most rounds the search for the nodes' heights takes: each round at least doubles a table.
const MAX_ROUNDS: usize = 8;

/// A recursion circuit whose proofs are leaves of a tree: its key (the circuit and its fixed columns), its transcript's
/// session, its proofs' rate, and how its statement states claims.
///
/// A batch of signatures gives it (`XmssBatch::leaves`). Its proofs are plain recursion proofs: the recursion machine
/// has no zero-knowledge proof.
#[derive(Clone, Copy)]
pub struct LeafCircuit<'p> {
    /// The circuit and its fixed columns at its heights.
    pub(crate) key: &'p CircuitKey,
    /// Its proofs' transcript's session, which names the circuit and its size.
    pub(crate) session: SessionId,
    /// Its proofs' rate.
    pub(crate) rate: Rate,
    /// How its statement states claims, one a signature: what a proof of it publishes in a claim-set tree.
    pub(crate) claims: &'static ClaimLayout,
}

/// A tree's leaf family: what every leaf of the tree is a proof of.
#[derive(Clone, Copy)]
pub enum Leaves<'p> {
    /// RISC-V proofs of one program, of one shape, plain or zero knowledge as the shape says.
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
    /// A proof of the recursion circuit of session `session`, and its statement.
    Circuit {
        session: SessionId,
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
    /// The statement of a proof of the recursion circuit of session `session`.
    Circuit { session: SessionId, words: Vec<Limbs> },
}

/// The tree a root is expected to cover: its shape, and what each leaf states.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Subtree {
    /// A first-level node: what its leaves state, in order.
    First(Vec<LeafStatement>),
    /// A node: its children, in order.
    Node(Vec<Self>),
}

/// What a recursion circuit costs: one of a tree's, or a signature batch's.
#[derive(Clone, Debug, PartialEq, Eq)]
#[non_exhaustive]
pub struct CircuitStats {
    /// Each table of the recursion machine, in the machine's order.
    pub tables: Vec<TableStats>,
    /// The words a proof of the circuit commits.
    pub committed: usize,
}

/// One table of a circuit: its rows, and the height they are padded to.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[non_exhaustive]
pub struct TableStats {
    /// The table's name.
    pub name: &'static str,
    /// The rows the circuit puts in the table.
    pub rows: usize,
    /// The base-two logarithm of the table's height, none if the proof leaves the table out.
    ///
    /// The height is a power of two, at least the rows.
    pub height_log: Option<usize>,
}

impl TableStats {
    /// The rows its proof has: its height, zero if the proof leaves it out.
    #[must_use]
    pub const fn height(&self) -> usize {
        match self.height_log {
            Some(tau) => 1 << tau,
            None => 0,
        }
    }
}

impl CircuitStats {
    /// What a circuit costs.
    ///
    /// # Panics
    ///
    /// Panics if the circuit fits no commitment, which every caller has refused before.
    pub(crate) fn of(circuit: &Circuit) -> Self {
        // The circuit's rows per table, and the padded heights it is proven at.
        let (rows, heights) = (circuit.row_counts(), circuit.heights());

        // One entry per table of the recursion machine, in its order.
        let tables = (Table::ALL.iter())
            .map(|&table| TableStats {
                name: table.name(),
                rows: rows[table],
                height_log: heights[table],
            })
            .collect();

        let committed = circuit.committed_words().expect("the circuit fits one commitment");
        Self { tables, committed }
    }
}

/// An aggregation tree over leaf proofs of one family.
///
/// It is the tree's verifying key, and what its prover needs.
///
/// It is built from the leaf family and the shape alone, before any proof exists.
pub struct Tree<'p> {
    /// How it is shaped.
    shape: TreeShape,
    /// What fixes the circuits.
    design: Design<'p>,
    /// Each circuit's key, by its position: the first level's first.
    keys: Vec<CircuitKey>,
    /// The dense polynomials the root's claims are settled against.
    tables: DenseTables,
}

/// A leaf of a claim-set tree: a leaf proof, and the claim set it publishes.
///
/// A RISC-V proof's output is the hash of the set's digest; a proof of a signature circuit states the set's claims.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ClaimLeaf<'a> {
    /// The proof and what it states.
    leaf: Leaf<'a>,
    /// The set it publishes.
    claims: &'a ClaimSet,
}

/// A proof of a claim-set tree and the set it declares: what one party hands another to combine.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Aggregate {
    /// The proof.
    pub proof: TreeProof,
    /// The set its statement's digest is of.
    pub claims: ClaimSet,
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
    /// A small tier past the tree's: an arity outside two to the tree's, or a capacity past the tree's.
    #[error("a small tier of {arity} children and {capacity:?} does not fit within the tree's")]
    SmallTier {
        /// Its arity.
        arity: usize,
        /// Its capacity.
        capacity: Capacity,
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
    /// A leaf of another family or shape than the tree's.
    #[error("leaf {index} is of another family or shape than the tree's")]
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
    /// An operation of the other semantics: positional proving or verifying on a claim-set tree, or the reverse.
    #[error("the tree is {}", if *.claims { "a claim-set tree" } else { "a tree of outputs" })]
    Semantics {
        /// Whether the tree is a claim-set tree.
        claims: bool,
    },
    /// A proof of no circuit of the tree.
    #[error("a proof of kind {0}, which the tree has no circuit of")]
    Circuit(usize),
    /// A leaf that does not publish the claim set given with it: a RISC-V output not the hash of its digest, or a
    /// statement stating another set, or claims of more than one label.
    #[error("leaf {index} does not publish its claim set")]
    LeafClaims {
        /// The leaf's index among its node's.
        index: usize,
    },
    /// A child's statement is not of the claim set given with it.
    #[error("child {index}'s statement is not of its claim set")]
    ChildClaims {
        /// The child's index among its node's.
        index: usize,
    },
    /// The children's sets, or the declared set, do not fit the tree's capacity.
    #[error("the claim sets do not fit the tree's capacity")]
    Capacity,
    /// A declared claim no child carries.
    #[error("the declared claim {0:?} is not covered by the children")]
    NotCovered(Claim),
    /// A declared or root set that is not canonical, or past the capacity.
    #[error("the claim set: {0}")]
    ClaimSet(ClaimSetError),
    /// The root does not state this claim set.
    #[error("the root does not state this claim set")]
    Claims,
}

/// The digest a first-level node binds a leaf circuit's statement by: the first 32 bytes its proof's transcript would squeeze after the session and the instance.
///
/// A leaf's verifier rows draw it from their transcript once it has absorbed the instance (`Transcript::digest_so_far`).
fn instance_digest(session: &SessionId, statement: &[Limbs]) -> Limbs {
    let mut ps = ProverState::new(session, &LengthPrefixed(statement.as_flattened()));
    primitives::hash::digest_words(&ps.verifier_message::<[u8; 32]>())
}

impl<'p> LeafCircuit<'p> {
    /// The leaf circuit of a circuit's key, its proofs' session and rate, and how its statement states claims.
    pub(crate) const fn new(key: &'p CircuitKey, session: SessionId, rate: Rate, claims: &'static ClaimLayout) -> Self {
        Self {
            key,
            session,
            rate,
            claims,
        }
    }

    /// The circuit.
    pub(crate) const fn circuit(&self) -> &'p Circuit {
        self.key.circuit()
    }

    /// Its fixed columns at its heights.
    pub(crate) const fn columns(&self) -> &'p FixedColumns {
        self.key.fixed()
    }

    /// Its session, as words.
    pub(crate) fn seed(&self) -> Limbs {
        primitives::hash::digest_words(&self.session.0)
    }
}

impl<'a> Leaf<'a> {
    /// The leaf of a RISC-V proof and the output it proves.
    #[must_use]
    pub const fn new(proof: &'a Proof, output: Output) -> Self {
        Self(LeafProof::Run { proof, output })
    }

    /// The leaf of a proof of a leaf circuit at `rate`, and the statement it proves.
    pub(crate) const fn circuit(
        leaf: &LeafCircuit<'_>,
        statement: Vec<Limbs>,
        proof: &'a ProofTranscript,
        rate: Rate,
    ) -> Self {
        Self(LeafProof::Circuit {
            session: leaf.session,
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
            LeafProof::Circuit { session, statement, .. } => Stated::Circuit {
                session: *session,
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
    pub(crate) const fn circuit(leaf: &LeafCircuit<'_>, words: Vec<Limbs>) -> Self {
        Self(Stated::Circuit {
            session: leaf.session,
            words,
        })
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

impl<'a> ClaimLeaf<'a> {
    /// The leaf of a proof that publishes this set: a RISC-V proof whose output is the hash of its digest, as a guest
    /// that commits the digest gives, or a proof of a signature circuit whose statement states it.
    #[must_use]
    pub const fn new(leaf: Leaf<'a>, claims: &'a ClaimSet) -> Self {
        Self { leaf, claims }
    }
}

impl<'p> Tree<'p> {
    /// The tree over leaves of this family, shaped as given.
    ///
    /// The circuits are built from the family and the shape alone, so a verifier needs no proof to build its key.
    ///
    /// # Errors
    ///
    /// - Arities that make no tree: a first level of no leaf, or nodes of fewer than two children.
    /// - A small tier past the tree's.
    /// - A leaf shape no proof of the program has.
    /// - Circuits that fit no commitment.
    pub fn new(leaves: Leaves<'p>, shape: TreeShape) -> Result<Self, TreeError> {
        shape.check()?;
        let tiers = shape.claims.map_or(1, |c| c.tiers());
        let family = || match leaves {
            Leaves::Runs { program, shape } => ProofShape::new(program, shape)
                .map(Family::Runs)
                .map_err(|e| TreeError::LeafShape(e.into())),
            Leaves::Circuit(c) => CircuitFamily::new(c).map(Family::Circuit),
        };
        let (design, circuits) = Self::converge(tiers, |taus| Design::new(family()?, &shape, taus))?;
        let keys: Vec<CircuitKey> = (circuits.into_iter().map(CircuitKey::new))
            .collect::<Result<_, _>>()
            .map_err(|_| TreeError::TooLarge)?;
        let columns: Vec<&FixedColumns> = keys.iter().map(CircuitKey::fixed).collect();
        let tables = design.tables(&columns);
        Ok(Self {
            shape,
            design,
            keys,
            tables,
        })
    }

    /// Each tier's heights, which its circuits share, and the circuits at them, by their position.
    ///
    /// They are the least fixed point of `tau -> max(tau, each of a tier's circuits' heights at tau)`, every tier
    /// from the first-level circuit's own heights: a small tier's wrap verifies the large tier's proofs, and the large
    /// tier's nodes the small tier's, so the tiers' heights are found together. A table is absent from a tier's
    /// heights, its height none, only while all the tier's circuits lack it.
    ///
    /// Each round only raises heights, and a node's rows grow with the logarithm of its children's, so few rounds reach it.
    fn converge(
        tiers: usize,
        design: impl Fn(&[Heights]) -> Result<Design<'p>, TreeError>,
    ) -> Result<(Design<'p>, Vec<Circuit>), TreeError> {
        let max = |taus: Heights, built: &[Circuit]| {
            Heights::from_fn(|t| built.iter().map(|c| c.heights()[t]).fold(taus[t], Option::max))
        };
        // The first-level circuit does not depend on the heights: those of a circuit of no rows build it.
        let empty = Heights::from_fn(|t: Table| t.height_log(0));
        let start = design(&vec![empty; tiers])?.shape(0).circuit.heights();
        let mut taus = vec![start; tiers];
        for _ in 0..MAX_ROUNDS {
            let d = design(&taus)?;
            let built: Vec<Circuit> = (0..d.places.len()).map(|p| d.shape(p).circuit).collect();
            let next: Vec<Heights> = (d.tiers.iter().zip(&taus))
                .map(|(tier, &taus)| max(taus, &built[tier.places.clone()]))
                .collect();
            if next == taus {
                let circuits = (built.into_iter().zip(&d.places))
                    .map(|(c, p)| c.with_floor(taus[p.tier]))
                    .collect();
                return Ok((d, circuits));
            }
            taus = next;
        }
        Err(TreeError::TooLarge)
    }

    /// The circuit at this position.
    pub(crate) fn circuit(&self, position: usize) -> &Circuit {
        self.keys[position].circuit()
    }

    /// The position of the circuit of a kind: the first level's, or of a claim-set tree's nodes, the one of the largest
    /// arity.
    const fn position_of(&self, kind: Kind) -> usize {
        match kind {
            Kind::First => 0,
            Kind::Node => self.design.places.len() - 1,
        }
    }

    /// The circuit of a kind as `CheckRec` reads it: the builder calls that make it, one per line, then `circuit` and the circuit's dump, then `next` and the bus's `next` key of every slot of the circuit's rows, per table, row-major.
    ///
    /// # Panics
    ///
    /// Panics if building the circuit again gives another circuit.
    #[cfg(feature = "circuit-trace")]
    pub fn circuit_dump(&self, kind: Kind) -> String {
        let position = self.position_of(kind);
        let (finished, calls) = crate::rec::circuit::traced(|| self.design.shape(position));
        let mut circuit = finished.circuit;
        circuit.floor = self.circuit(position).floor;
        assert_eq!(
            &circuit,
            self.circuit(position),
            "a circuit is built the same every time"
        );
        calls + "circuit\n" + &circuit.dump() + &self.keys[position].fixed().dump_next(&circuit)
    }

    /// The capacity of a claim-set tree's largest nodes and roots, or why this tree has none.
    fn capacity(&self) -> Result<Capacity, TreeError> {
        (self.design.claims.map(|c| c.capacity)).ok_or(TreeError::Semantics { claims: false })
    }

    /// Nothing, if a proof is at the rate of the tree's proofs.
    fn check_rate(&self, p: &TreeProof) -> Result<(), TreeError> {
        let expected = self.design.rate;
        if p.rate == expected {
            Ok(())
        } else {
            Err(TreeError::Rate { expected, got: p.rate })
        }
    }

    /// Nothing, if this is a tree of outputs.
    const fn outputs(&self) -> Result<(), TreeError> {
        match self.design.claims {
            Some(_) => Err(TreeError::Semantics { claims: true }),
            None => Ok(()),
        }
    }

    /// The position of a proof's circuit, if it is of one of the tree's circuits and states as many words as its
    /// statements have.
    fn known(&self, p: &TreeProof) -> Result<usize, TreeError> {
        match self.design.position(p.circuit) {
            Some(position) if p.words.len() == self.design.statement.len() => Ok(position),
            _ => Err(TreeError::Circuit(p.circuit)),
        }
    }

    /// Prove a first-level node over its leaves, in order.
    ///
    /// # Errors
    ///
    /// A tree of outputs only. The wrong number of leaves, a leaf of another family or shape than the tree's, or a leaf
    /// that does not verify.
    pub fn prove_first(&self, leaves: &[Leaf<'_>]) -> Result<TreeProof, TreeError> {
        self.outputs()?;
        let d = &self.design;
        let leaves: Vec<&Leaf<'_>> = leaves.iter().collect();
        let rows = match &d.family {
            Family::Runs(shape) => {
                let items = self.leaf_witnesses(shape, &leaves, |_, _| Ok([0; 4]))?;
                let inputs = NodeInputs::Prove {
                    items: &items,
                    tables: &self.tables,
                    union: None,
                };
                info_span!("Build circuit").in_scope(|| d.first_runs_rows(shape, &inputs))
            }
            Family::Circuit(family) => {
                let items = self.circuit_witnesses(family, &leaves)?;
                let inputs = NodeInputs::Prove {
                    items: &items,
                    tables: &self.tables,
                    union: None,
                };
                info_span!("Build circuit").in_scope(|| d.first_circuit_rows(family, &inputs))
            }
        };
        self.prove_rows(rows)
    }

    /// Nothing, if a first-level node is given as many leaves as it verifies.
    const fn leaf_count(&self, got: usize) -> Result<(), TreeError> {
        let expected = self.design.arity_0;
        if got == expected {
            Ok(())
        } else {
            Err(TreeError::Children { expected, got })
        }
    }

    /// The first level's witnesses of its RISC-V leaves of this shape, each verified natively; `claims` gives a leaf's
    /// set's digest from its index and output.
    fn leaf_witnesses<'a>(
        &self,
        shape: &ProofShape<'_>,
        leaves: &[&Leaf<'a>],
        claims: impl Fn(usize, &Output) -> Result<[u64; 4], TreeError>,
    ) -> Result<Vec<LeafWitness<'a>>, TreeError> {
        self.leaf_count(leaves.len())?;
        let announced = shape.shape();
        let program = shape.program();
        (leaves.iter().enumerate())
            .map(|(index, leaf)| {
                let LeafProof::Run { proof, output } = leaf.0 else {
                    return Err(TreeError::ForeignLeaf { index });
                };
                if LeafShape::announced(proof) != Some(announced) {
                    return Err(TreeError::ForeignLeaf { index });
                }
                let claims = claims(index, &output)?;
                let openings =
                    (program.verify_recording(output, proof)).map_err(|error| TreeError::Leaf { index, error })?;
                Ok(LeafWitness {
                    proof: &proof.0,
                    openings,
                    output: *output.words(),
                    set: claims,
                })
            })
            .collect()
    }

    /// The first level's witnesses of its leaves of the leaf circuit, each verified natively.
    fn circuit_witnesses<'a>(
        &self,
        family: &CircuitFamily<'a>,
        leaves: &[&Leaf<'a>],
    ) -> Result<Vec<CircuitWitness<'a>>, TreeError> {
        self.leaf_count(leaves.len())?;
        let c = &family.leaf;
        (leaves.iter().enumerate())
            .map(|(index, leaf)| {
                let LeafProof::Circuit {
                    session,
                    ref statement,
                    proof,
                    rate,
                } = leaf.0
                else {
                    return Err(TreeError::ForeignLeaf { index });
                };
                let words = statement.len() == c.circuit().statement_len && statement.iter().all(|w| w[3] == 0);
                if session != c.session || rate != c.rate || !words {
                    return Err(TreeError::ForeignLeaf { index });
                }
                let openings =
                    (c.key.verify(statement, &c.session, c.rate, proof)).map_err(|error| TreeError::Leaf {
                        index,
                        error: error.into(),
                    })?;
                Ok(CircuitWitness {
                    statement: statement.clone(),
                    proof,
                    openings,
                    columns: c.columns(),
                })
            })
            .collect()
    }

    /// The node's witnesses of its children, proofs of `tier`, each verified natively, short of its claims.
    fn child_witnesses<'a>(
        &'a self,
        tier: usize,
        children: &[&'a TreeProof],
        statements: &'a [TreeStatement],
    ) -> Result<Vec<ChildWitness<'a>>, TreeError> {
        (children.iter().zip(statements).enumerate())
            .map(|(index, (c, statement))| {
                let position = self.known(c)?;
                if self.design.places[position].tier != tier {
                    return Err(TreeError::Circuit(c.circuit));
                }
                let openings = self
                    .read(c, position)
                    .map_err(|error| TreeError::Child { index, error })?;
                Ok(ChildWitness {
                    statement,
                    proof: &c.proof,
                    openings,
                    columns: self.keys[position].fixed(),
                })
            })
            .collect()
    }

    /// Prove a node over its children, tree proofs of either kind, in order.
    ///
    /// A child is verified under the tree's session, which names the tree's leaf family: a tree proof of another tree is refused as a child that does not verify.
    ///
    /// # Errors
    ///
    /// A tree of outputs only. The wrong number of children, or a child that does not verify.
    pub fn prove_node(&self, children: &[TreeProof]) -> Result<TreeProof, TreeError> {
        self.outputs()?;
        let d = &self.design;
        if children.len() != d.arity {
            return Err(TreeError::Children {
                expected: d.arity,
                got: children.len(),
            });
        }
        let children: Vec<&TreeProof> = children.iter().collect();
        children.iter().try_for_each(|c| self.known(c).map(drop))?;
        let statements: Vec<TreeStatement> = (children.iter()).map(|c| c.statement(d.statement)).collect();
        let items = self.child_witnesses(SMALL, &children, &statements)?;
        let inputs = NodeInputs::Prove {
            items: &items,
            tables: &self.tables,
            union: None,
        };
        let rows = info_span!("Build circuit").in_scope(|| d.node_rows(&inputs, 1));
        self.prove_rows(rows)
    }

    /// Prove a first-level node of a claim-set tree over its leaves, in order, declaring `declare`, by default the
    /// union of the leaves' sets.
    ///
    /// # Errors
    ///
    /// - A tree of outputs.
    /// - The wrong number of leaves, a leaf of another family or shape, a leaf that does not verify, or one that does
    ///   not publish its set: a RISC-V output not the hash of its digest, a statement stating another set or claims
    ///   of more than one label.
    /// - A declared set that is not canonical, past the capacity, or with a claim no leaf carries.
    /// - Leaves whose sets together do not fit the first level's capacity: the small tier's, if the tree has one.
    pub fn aggregate_leaves(
        &self,
        leaves: &[ClaimLeaf<'_>],
        declare: Option<&ClaimSet>,
    ) -> Result<Aggregate, TreeError> {
        self.capacity()?;
        let d = &self.design;
        let plain: Vec<&Leaf<'_>> = leaves.iter().map(|l| &l.leaf).collect();
        let sets: Vec<&ClaimSet> = leaves.iter().map(|l| l.claims).collect();
        let (rows, claims) = match &d.family {
            Family::Runs(shape) => {
                let digests: Vec<[u64; 4]> = sets.iter().map(|s| s.digest()).collect();
                let items = self.leaf_witnesses(shape, &plain, |index, output| {
                    // The guest commits the digest, so its output is the digest's hash.
                    if *output.words() == chain(&digests[index]) {
                        Ok(digests[index])
                    } else {
                        Err(TreeError::LeafClaims { index })
                    }
                })?;
                let (union, claims) = self.fill(0, &sets, declare)?;
                let inputs = NodeInputs::Prove {
                    items: &items,
                    tables: &self.tables,
                    union: Some(&union),
                };
                let rows = info_span!("Build circuit").in_scope(|| d.first_runs_rows(shape, &inputs));
                (rows, claims)
            }
            Family::Circuit(family) => {
                let items = self.circuit_witnesses(family, &plain)?;
                // The statement states the set: one group, a claim a signature.
                let stated = |(w, set): (&CircuitWitness<'_>, &&ClaimSet)| {
                    family.leaf.claims.set(&w.statement).as_ref() == Some(*set)
                };
                if let Some(index) = items.iter().zip(&sets).position(|p| !stated(p)) {
                    return Err(TreeError::LeafClaims { index });
                }
                let (union, claims) = self.fill(0, &sets, declare)?;
                let inputs = NodeInputs::Prove {
                    items: &items,
                    tables: &self.tables,
                    union: Some(&union),
                };
                let rows = info_span!("Build circuit").in_scope(|| d.first_circuit_rows(family, &inputs));
                (rows, claims)
            }
        };
        let proof = self.prove_rows(rows)?;
        Ok(Aggregate { proof, claims })
    }

    /// Prove a node of a claim-set tree over any of its proofs, from one to the tree's arity, each with the set it
    /// declares, declaring `declare`, by default the union of their sets.
    ///
    /// The children may be of any kind and any provers'. A node's places past its children verify the first child again
    /// and are absent: their sets are read as the empty set. So a lone child is taken once, by a node of two, which
    /// narrows or republishes it whatever the size of its set within the capacity.
    ///
    /// In a tree of two tiers, the node is the small tier's if the children are few enough and their sets and the
    /// declared set fit its capacity, else the large tier's one node. A child of the large tier is wrapped first, a
    /// proof of its own.
    ///
    /// # Errors
    ///
    /// - A tree of outputs.
    /// - No child, or more than the arity; a child that does not verify, or whose statement is not of its set.
    /// - A declared set that is not canonical, past the capacity, or with a claim no child carries.
    /// - Children whose sets together do not fit the capacity.
    pub fn aggregate(&self, children: &[&Aggregate], declare: Option<&ClaimSet>) -> Result<Aggregate, TreeError> {
        self.capacity()?;
        let d = &self.design;
        let n = children.len();
        // A lone child is taken by a node of two, its other place absent.
        let small = d.place(SMALL, Level::Node(n.max(2))).map(|p| (p, n.max(2)));
        let large = d.place(LARGE, Level::Node(d.arity)).map(|p| (p, d.arity));
        if n == 0 || n > d.arity || (small.is_none() && large.is_none()) {
            return Err(TreeError::Children {
                expected: d.arity,
                got: n,
            });
        }
        let mut wraps = Vec::with_capacity(n);
        for (index, c) in children.iter().enumerate() {
            let position = self.known(&c.proof)?;
            wraps.push(
                (d.places[position].tier == LARGE)
                    .then(|| self.wrap(index, c))
                    .transpose()?,
            );
        }
        let children: Vec<&Aggregate> = (children.iter().zip(&wraps))
            .map(|(&c, w)| w.as_ref().unwrap_or(c))
            .collect();
        let proofs: Vec<&TreeProof> = children.iter().map(|c| &c.proof).collect();
        let statements: Vec<TreeStatement> = (proofs.iter()).map(|c| c.statement(d.statement)).collect();
        let items = self.child_witnesses(SMALL, &proofs, &statements)?;
        if let Some(index) = (statements.iter().zip(&children)).position(|(s, c)| s.digest_words() != c.claims.digest())
        {
            return Err(TreeError::ChildClaims { index });
        }
        let sets: Vec<&ClaimSet> = children.iter().map(|c| &c.claims).collect();
        // The first tier whose union holds the sets. A place past the children verifies the first child again, absent
        // from the union.
        for (position, slots) in small.into_iter().chain(large) {
            let (union, claims) = match self.fill(position, &sets, declare) {
                Err(TreeError::Capacity) => continue,
                filled => filled?,
            };
            let slot_items: Vec<ChildWitness<'_>> = (0..slots)
                .map(|i| {
                    let w = &items[if i < n { i } else { 0 }];
                    ChildWitness {
                        statement: w.statement,
                        proof: w.proof,
                        openings: w.openings.clone(),
                        columns: w.columns,
                    }
                })
                .collect();
            let inputs = NodeInputs::Prove {
                items: &slot_items,
                tables: &self.tables,
                union: Some(&union),
            };
            let rows = info_span!("Build circuit").in_scope(|| d.node_rows(&inputs, position));
            let proof = self.prove_rows(rows)?;
            return Ok(Aggregate { proof, claims });
        }
        Err(TreeError::Capacity)
    }

    /// Wrap child `index`, a proof of the large tier: a proof of the small tier stating its set.
    fn wrap(&self, index: usize, child: &Aggregate) -> Result<Aggregate, TreeError> {
        let d = &self.design;
        let position = (d.place(SMALL, Level::Wrap)).expect("a tree of two tiers wraps");
        let statements = [child.proof.statement(d.statement)];
        let items = (self.child_witnesses(LARGE, &[&child.proof], &statements)).map_err(|e| match e {
            TreeError::Child { error, .. } => TreeError::Child { index, error },
            e => e,
        })?;
        if statements[0].digest_words() != child.claims.digest() {
            return Err(TreeError::ChildClaims { index });
        }
        let inputs = NodeInputs::Prove {
            items: &items,
            tables: &self.tables,
            union: None,
        };
        let rows = info_span!("Build circuit").in_scope(|| d.node_rows(&inputs, position));
        let proof = self.prove_rows(rows)?;
        Ok(Aggregate {
            proof,
            claims: child.claims.clone(),
        })
    }

    /// The union's values over these sets in the circuit at `position`, and the set it declares: `declare`, or the
    /// canonical union, which must fit the circuit's tier's capacity.
    fn fill(
        &self,
        position: usize,
        sets: &[&ClaimSet],
        declare: Option<&ClaimSet>,
    ) -> Result<(UnionFill, ClaimSet), TreeError> {
        let capacity = self.capacity()?;
        let declared = match declare {
            Some(set) => {
                set.check(capacity).map_err(TreeError::ClaimSet)?;
                set.clone()
            }
            None => {
                let union = ClaimSet::from_claims(sets.iter().flat_map(|s| s.claims()));
                union.check(capacity).map_err(|_| TreeError::Capacity)?;
                union
            }
        };
        let tier = self.design.places[position].tier;
        let held = (self.design.claims).map_or(capacity, |c| c.tier_capacity(tier));
        if declared.n_claims() >= held.claims || declared.groups.len() > held.groups {
            return Err(TreeError::Capacity);
        }
        let shape = self
            .design
            .union_shape(position)
            .expect("a claim-set tree's node has a union");
        let fill = UnionFill::new(&shape, sets, &declared).map_err(|e| match e {
            FillError::Children | FillError::Declared => TreeError::Capacity,
            FillError::NotCovered(claim) => TreeError::NotCovered(claim),
        })?;
        Ok((fill, declared))
    }

    /// Prove the balanced tree over its leaves, in order.
    ///
    /// The first level, then each level of nodes, up to the root.
    ///
    /// # Errors
    ///
    /// A tree of outputs only. A number of leaves no tree of the arities has, or a leaf the first level refuses.
    pub fn prove(&self, leaves: &[Leaf<'_>]) -> Result<TreeProof, TreeError> {
        self.outputs()?;
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
    /// A tree of outputs only. Returns the first check that refuses.
    #[tracing::instrument(name = "Verify tree", skip_all)]
    pub fn verify(&self, root: &TreeProof, expected: &Subtree) -> Result<(), TreeError> {
        self.outputs()?;
        let d = &self.design;
        self.check_rate(root)?;
        let (kind, digest) = self.expect(expected)?;
        if root.kind() != kind {
            return Err(TreeError::Kind {
                expected: kind,
                got: root.kind(),
            });
        }
        let position = self.known(root)?;
        self.read(root, position).map_err(TreeError::Root)?;
        let statement = root.statement(d.statement);
        if statement.digest_words() != digest {
            return Err(TreeError::Digest);
        }
        self.settle(&statement, position)
    }

    /// Verify the root of a claim-set tree: its recursion proof, that its set is canonical and within the capacity,
    /// that it states this set, and every claim it carries.
    ///
    /// The root may be of any kind and either tier, made by anyone, over any shape of tree: the set is all its
    /// statement says.
    ///
    /// # Errors
    ///
    /// A tree of outputs. Otherwise the first check that refuses.
    #[tracing::instrument(name = "Verify claim-set tree", skip_all)]
    pub fn verify_claims(&self, root: &TreeProof, claims: &ClaimSet) -> Result<(), TreeError> {
        let capacity = self.capacity()?;
        let d = &self.design;
        self.check_rate(root)?;
        let position = self.known(root)?;
        claims.check(capacity).map_err(TreeError::ClaimSet)?;
        self.read(root, position).map_err(TreeError::Root)?;
        let statement = root.statement(d.statement);
        if statement.digest_words() != claims.digest() {
            return Err(TreeError::Claims);
        }
        self.settle(&statement, position)
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
                let items = (leaves.iter().enumerate())
                    .map(|(index, l)| match (&d.family, &l.0) {
                        (Family::Runs(_), Stated::Run(output)) => Ok(*output.words()),
                        (Family::Circuit(c), Stated::Circuit { session, words }) if *session == c.leaf.session => {
                            Ok(instance_digest(session, words))
                        }
                        _ => Err(TreeError::ForeignLeaf { index }),
                    })
                    .collect::<Result<Vec<Limbs>, _>>()?;
                let under = match &d.family {
                    Family::Runs(_) => Items::Runs,
                    Family::Circuit(c) => Items::Circuit(c.leaf.seed()),
                };
                Ok((Kind::First, under.digest(&items)))
            }
            Subtree::Node(children) => {
                count(d.arity, children.len())?;
                let digests = (children.iter())
                    .map(|c| self.expect(c).map(|(_, digest)| digest))
                    .collect::<Result<Vec<_>, _>>()?;
                Ok((Kind::Node, Items::Node.digest(&digests)))
            }
        }
    }

    /// Verify a tree proof's recursion proof, short of its claims, returning every opening it authenticated.
    ///
    /// The proof is of the tree's circuit at `position`.
    fn read(&self, p: &TreeProof, position: usize) -> Result<Vec<Openings>, VerifyError> {
        self.keys[position]
            .verify(&p.limbs(), &self.design.session(), self.design.rate, &p.proof)
            .map_err(Into::into)
    }

    /// Prove the rows of the circuit at `position`: its reduction, then its recursion proof.
    fn prove_rows(&self, rows: NodeRows) -> Result<TreeProof, TreeError> {
        let d = &self.design;
        let position = rows.position();
        let reduction = rows.claim_values().prove(&d.session(), &d.vars, &self.tables);
        let Finished {
            assignment, failures, ..
        } = info_span!("Reduce in rows").in_scope(|| rows.reduce(d, ProofSource::Proof(&reduction, &[])));
        if let Some(first) = failures.into_iter().next() {
            return Err(TreeError::Unsatisfied(first));
        }
        let proof = self.keys[position].prove(&assignment, &d.session(), d.rate);
        Ok(TreeProof::new(d.code(position), &assignment, proof, d.rate))
    }

    /// Evaluate every claim a root's statement carries: each dense polynomial a proof of its circuit carries a claim on,
    /// and every flock circuit's matrices.
    #[tracing::instrument(name = "Settle claims", skip_all)]
    fn settle(&self, s: &TreeStatement, position: usize) -> Result<(), TreeError> {
        let d = &self.design;
        // A first-level node carries a claim only on a polynomial its leaves fix.
        let carried = |poly| position != 0 || d.leaves_fix(poly);
        for poly in d.statement.polys().filter(|&p| carried(p)) {
            let point = &s.dense_point()[..d.vars.0[poly as usize]];
            if mle_eval_par(&self.tables.0[poly as usize], point) != s.dense_value(poly) {
                return Err(TreeError::Claim(FalseClaim::Dense(poly)));
            }
        }
        let held = parallel::map_collect(CircuitId::ALL.len(), |f| {
            let f = CircuitId::ALL[f];
            let circuit = f.circuit();
            let k = circuit.k_log();
            let (ra, rb) = circuit.row_values(&eq_table(&s.cols()[..k]));
            let u = eq_table(&s.rows()[..k]);
            let dot = |r: &[F192]| u.iter().zip(r).fold(F192::ZERO, |acc, (&x, &y)| acc + x * y);
            [dot(&ra), dot(&rb)] == s.matrices(f)
        });
        (CircuitId::ALL.into_iter().zip(held))
            .find(|&(_, h)| !h)
            .map_or(Ok(()), |(f, _)| {
                Err(TreeError::Claim(FalseClaim::Matrix {
                    table: f.table().name(),
                    part: f.part(),
                }))
            })
    }

    /// What the circuit of one kind of node costs: of a claim-set tree's nodes, the one of the largest arity.
    #[must_use]
    pub fn stats(&self, kind: Kind) -> CircuitStats {
        self.circuit_stats(self.position_of(kind))
    }

    /// What the circuit at this position costs.
    fn circuit_stats(&self, position: usize) -> CircuitStats {
        // Invariant: building the tree refused any circuit that fits no commitment.
        CircuitStats::of(self.circuit(position))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::cpu::{DecodeError, Prover};
    use crate::rec::RecError;
    use crate::rec::circuit::{Assignment, Builder, Kw};
    use crate::rec::sphincs::{SphincsBatch, SphincsClaim, SphincsProof};
    use crate::rec::tree::design::NodeRows;
    use crate::rec::tree::reduce::tests::{Forge, forged_reduction};
    use crate::rec::tree::statement::Section;
    use crate::rec::xmss::{XmssBatch, XmssClaim, XmssError, XmssProof, XmssSignature};
    use crate::rv::Region;
    use crate::rv::asm::*;
    use crate::tables::TableId;
    use fiat_shamir::ProofTranscript;
    use flock::FlockError;
    use flock::zerocheck::ZerocheckError;
    use leanxmss_host::{LEAF_INDEX, MESSAGE};
    use std::sync::LazyLock;
    use zk::Randomness;

    // A program whose output is its one advice word, after a loop that reads every framework block.
    fn program() -> &'static Program {
        static PROGRAM: LazyLock<Program> = LazyLock::new(|| {
            let text = Asm::new()
                .li(Reg::T0, Region::ADVICE.base())
                .load(Ld, Reg::A0, 0, Reg::T0)
                .li(Reg::T1, 9)
                .label("loop")
                .i(Addi, Reg::T1, Reg::T1, -1)
                .branch(Bne, Reg::T1, Reg::ZERO, "loop")
                .exit()
                .finish();
            Program::new(&text, Region::TEXT.base(), vec![3, 5], 2, 0).expect("a valid program")
        });
        &PROGRAM
    }

    // The 2 to 1 shape at the lowest rate.
    const PAIRS: TreeShape = TreeShape {
        arity_0: 2,
        arity: 2,
        rate: Rate::MIN,
        claims: None,
    };

    // Four leaves of distinct outputs, a tree of first level 2 and arity 2 over them, and its proofs.
    struct Fixture {
        tree: Tree<'static>,
        leaves: Vec<(Proof, Output)>,
        firsts: [TreeProof; 2],
        root: TreeProof,
    }

    fn runs(shape: LeafShape) -> Leaves<'static> {
        Leaves::Runs {
            program: program(),
            shape,
        }
    }

    fn fixture() -> &'static Fixture {
        static FIXTURE: LazyLock<Fixture> = LazyLock::new(|| {
            let leaves: Vec<(Proof, Output)> = (1..=4)
                .map(|advice| {
                    let run = Prover::new(Rate::MIN)
                        .prove(program(), &[advice])
                        .expect("the run halts");
                    (run.proof, run.output)
                })
                .collect();
            let shape = LeafShape::of(&leaves[0].0).expect("a canonical announcement");
            let tree = Tree::new(runs(shape), PAIRS).expect("a tree");
            let firsts = [0, 2].map(|i| {
                let pair = [
                    Leaf::new(&leaves[i].0, leaves[i].1),
                    Leaf::new(&leaves[i + 1].0, leaves[i + 1].1),
                ];
                tree.prove_first(&pair).expect("honest leaves")
            });
            let root = tree.prove_node(&firsts).expect("honest children");
            Fixture {
                tree,
                leaves,
                firsts,
                root,
            }
        });
        &FIXTURE
    }

    impl Fixture {
        fn outputs(&self) -> Vec<Output> {
            self.leaves.iter().map(|l| l.1).collect()
        }

        fn statements(&self) -> Vec<LeafStatement> {
            self.leaves.iter().map(|l| l.1.into()).collect()
        }

        fn pairs(&self) -> Vec<Leaf<'_>> {
            self.leaves.iter().map(|(p, o)| Leaf::new(p, *o)).collect()
        }
    }

    // The balanced tree over these leaves' outputs.
    fn balanced(outputs: &[Output], shape: &TreeShape) -> Result<Subtree, TreeError> {
        Subtree::balanced(outputs.iter().map(|&o| o.into()).collect(), shape)
    }

    #[test]
    fn a_tree_verifies_and_binds_its_leaves_in_order() {
        let f = fixture();
        let outputs = f.outputs();
        assert_eq!((f.firsts[0].kind(), f.root.kind()), (Kind::First, Kind::Node));
        let verify = |root, outputs: &[Output]| f.tree.verify(root, &balanced(outputs, &PAIRS)?);
        verify(&f.root, &outputs).expect("the root");
        verify(&f.firsts[1], &outputs[2..]).expect("a first-level node is the root of its leaves");

        let mut wrong = outputs.clone();
        let [a0, a1, a2, a3] = *wrong[3].words();
        wrong[3] = Output::new([a0 ^ 1, a1, a2, a3]);
        assert_eq!(verify(&f.root, &wrong), Err(TreeError::Digest));
        let mut swapped = outputs.clone();
        swapped.swap(0, 1);
        assert_eq!(verify(&f.root, &swapped), Err(TreeError::Digest));
        assert_eq!(
            verify(&f.root, &outputs[..3]),
            Err(TreeError::LeafCount {
                leaves: 3,
                arity_0: 2,
                arity: 2
            })
        );
        assert_eq!(
            verify(&f.root, &outputs[..2]),
            Err(TreeError::Kind {
                expected: Kind::First,
                got: Kind::Node
            })
        );
    }

    #[test]
    fn one_leaf_is_a_root() {
        let f = fixture();
        let shape = LeafShape::of(&f.leaves[0].0).expect("a canonical announcement");
        let single = TreeShape { arity_0: 1, ..PAIRS };
        let tree = Tree::new(runs(shape), single).expect("a tree");
        let root = tree.prove(&f.pairs()[..1]).expect("an honest leaf");
        tree.verify(&root, &balanced(&[f.leaves[0].1], &single).expect("one leaf"))
            .expect("the root of one leaf");
        assert_eq!(
            tree.verify(&root, &balanced(&[f.leaves[1].1], &single).expect("one leaf")),
            Err(TreeError::Digest)
        );

        // A first-level node of that tree is no child of a tree of another first level.
        let child = tree.prove_first(&f.pairs()[1..2]).expect("an honest leaf");
        assert!(matches!(
            f.tree.prove_node(&[f.firsts[0].clone(), child]),
            Err(TreeError::Child { index: 1, .. })
        ));
    }

    #[test]
    fn what_a_prover_is_handed_is_checked() {
        let f = fixture();
        let shape = LeafShape::of(&f.leaves[0].0).expect("a canonical announcement");
        for (arity_0, arity) in [(2, 1), (0, 2)] {
            assert!(matches!(
                Tree::new(
                    runs(shape),
                    TreeShape {
                        arity_0,
                        arity,
                        ..PAIRS
                    }
                ),
                Err(TreeError::Arity { .. })
            ));
        }
        assert_eq!(
            f.tree.prove_node(&f.firsts[..1]).map(|_| ()),
            Err(TreeError::Children { expected: 2, got: 1 })
        );

        // A leaf that does not verify, and one of another shape.
        let pairs = f.pairs();
        let mut forged = f.leaves[1].0.clone();
        let mid = forged.0.narg.len() / 24 / 2;
        forged.0.narg[24 * mid] ^= 1;
        assert!(matches!(
            f.tree
                .prove_first(&[pairs[0].clone(), Leaf::new(&forged, f.leaves[1].1)]),
            Err(TreeError::Leaf { index: 1, .. })
        ));
        let ProvenRun {
            proof: longer, output, ..
        } = (Prover::new(Rate::new(2).expect("a rate")).prove(program(), &[7])).expect("the run halts");
        assert_eq!(
            f.tree
                .prove_first(&[Leaf::new(&longer, output), pairs[1].clone()])
                .map(|_| ()),
            Err(TreeError::ForeignLeaf { index: 0 })
        );

        // A child whose statement is not its proof's.
        let mut changed = f.firsts[1].clone();
        changed.words[5] += F192::ONE;
        assert!(matches!(
            f.tree.prove_node(&[f.firsts[0].clone(), changed]),
            Err(TreeError::Child { index: 1, .. })
        ));
    }

    // A root over subtrees of two depths verifies against its own topology only.
    #[test]
    fn a_root_states_its_topology() {
        let f = fixture();
        let mixed = f
            .tree
            .prove_node(&[f.root.clone(), f.firsts[0].clone()])
            .expect("a node verifies either kind");
        let pairs = |o: &[Output]| Subtree::First(o.iter().map(|&o| o.into()).collect());
        let outputs = f.outputs();
        let topology = Subtree::Node(vec![
            balanced(&outputs, &PAIRS).expect("four leaves"),
            pairs(&outputs[..2]),
        ]);
        f.tree.verify(&mixed, &topology).expect("the root of its topology");
        let flipped = Subtree::Node(vec![
            pairs(&outputs[..2]),
            balanced(&outputs, &PAIRS).expect("four leaves"),
        ]);
        assert_eq!(f.tree.verify(&mixed, &flipped), Err(TreeError::Digest));
        let mut six = outputs.clone();
        six.extend_from_slice(&outputs[..2]);
        assert!(matches!(
            balanced(&six, &PAIRS),
            Err(TreeError::LeafCount { leaves: 6, .. })
        ));
    }

    // The reduction an honest prover proves, as its rows read it.
    fn honest_reduction(tree: &Tree<'_>, rows: &NodeRows) -> ProofTranscript {
        rows.claim_values()
            .prove(&tree.design.session(), &tree.design.vars, &tree.tables)
    }

    // The circuit a prover's rows build, at the nodes' heights.
    fn proven_circuit(tree: &Tree<'_>, rows: NodeRows) -> Circuit {
        let reduction = honest_reduction(tree, &rows);
        let Finished {
            mut circuit, failures, ..
        } = rows.reduce(&tree.design, ProofSource::Proof(&reduction, &[]));
        assert!(failures.is_empty(), "{failures:?}");
        circuit.floor = tree.design.tiers[SMALL].taus;
        circuit
    }

    #[test]
    fn a_proven_circuit_is_the_shapes() {
        let f = fixture();
        let d = &f.tree.design;
        let leaves: Vec<LeafWitness> = (f.leaves[..2].iter())
            .map(|(proof, output)| LeafWitness {
                proof: &proof.0,
                openings: program().verify_recording(*output, proof).expect("an honest leaf"),
                output: *output.words(),
                set: [0; 4],
            })
            .collect();
        let Family::Runs(shape) = &d.family else {
            panic!("a tree of RISC-V proofs")
        };
        let rows = d.first_runs_rows(
            shape,
            &NodeInputs::Prove {
                items: &leaves,
                tables: &f.tree.tables,
                union: None,
            },
        );
        assert!(
            &proven_circuit(&f.tree, rows) == f.tree.circuit(0),
            "the leaves build another circuit"
        );

        let statements = f.firsts.each_ref().map(|p| p.statement(d.statement));
        let items: Vec<ChildWitness<'_>> = (f.firsts.iter().zip(&statements))
            .map(|(p, statement)| ChildWitness {
                statement,
                proof: &p.proof,
                openings: f.tree.read(p, 0).expect("an honest child"),
                columns: f.tree.keys[0].fixed(),
            })
            .collect();
        let rows = d.node_rows(
            &NodeInputs::Prove {
                items: &items,
                tables: &f.tree.tables,
                union: None,
            },
            1,
        );
        assert!(
            &proven_circuit(&f.tree, rows) == f.tree.circuit(1),
            "the children build another circuit"
        );
    }

    // A fake first-level node's circuit: its leaves' outputs are free wires, its claims an honest statement's.
    fn fake_first(tree: &Tree<'_>, honest: &TreeProof, outputs: &[[u64; 4]]) -> (Circuit, Assignment) {
        let mut b = Builder::new();
        let items: Vec<[Kw; 4]> = outputs.iter().map(|o| o.map(|w| b.free_k(w))).collect();
        let digest = Items::Runs.digest_rows(&mut b, &items);
        let mut words = vec![b.e_const(F192::ZERO)];
        words.extend(TreeStatement::digest_halves(&mut b, digest));
        words.extend(
            honest.words[tree.design.statement.range(Section::Digest).end..]
                .iter()
                .map(|&w| b.free_e(w)),
        );
        for w in words {
            b.expose(w);
        }
        let Finished {
            mut circuit,
            assignment,
            failures,
        } = b.finish();
        assert!(failures.is_empty(), "{failures:?}");
        circuit.floor = tree.design.tiers[SMALL].taus;
        (circuit, assignment)
    }

    // A key's proof of its assignment's statement, as a tree proof of the circuit at a position.
    fn tree_proof(tree: &Tree<'_>, position: usize, key: &CircuitKey, assignment: &Assignment) -> TreeProof {
        let d = &tree.design;
        let proof = key.prove(assignment, &d.session(), d.rate);
        TreeProof::new(d.code(position), assignment, proof, d.rate)
    }

    // Reduce rows over the given tables, as a cheating prover holding them would, and prove the circuit at their position.
    fn proven_over(tree: &Tree<'_>, position: usize, rows: NodeRows, tables: &DenseTables) -> TreeProof {
        let d = &tree.design;
        let reduction = rows.claim_values().prove(&d.session(), &d.vars, tables);
        let Finished {
            assignment, failures, ..
        } = rows.reduce(d, ProofSource::Proof(&reduction, &[]));
        assert!(failures.is_empty(), "{failures:?}");
        tree_proof(tree, position, &tree.keys[position], &assignment)
    }

    // An honest node's rows over a child circuit the tree does not have hold, and only the root's settlement of the fixed polynomial refuses it.
    #[test]
    fn a_fake_child_circuit_is_refused_at_the_root() {
        let f = fixture();
        let d = &f.tree.design;
        let fake_outputs = [[0xdead, 1, 2, 3], [0xbeef, 4, 5, 6]];
        let (fake, assignment) = fake_first(&f.tree, &f.firsts[0], &fake_outputs);
        assert_eq!(fake.heights(), d.tiers[SMALL].taus, "the fake has the nodes' heights");
        let fake = CircuitKey::new(fake).expect("the fake fits");
        let child = tree_proof(&f.tree, 0, &fake, &assignment);
        assert!(
            f.tree.read(&child, 0).is_err(),
            "natively, the fake is no first-level node"
        );
        let limbs = child.limbs();
        let openings = fake
            .verify(&limbs, &d.session(), d.rate, &child.proof)
            .expect("the fake proves its own circuit");

        // The prover hands the rows the fake's fixed columns, and its fixed polynomial the fake's stack.
        let columns = fake.fixed();
        let mut tables = f.tree.tables.clone();
        tables.0[DensePoly::Fixed as usize] = d.tiers[SMALL].fixed.polynomial(&[columns, f.tree.keys[1].fixed()]);
        let statement = TreeStatement::new(d.statement, child.words);
        let items: Vec<ChildWitness<'_>> = (0..2)
            .map(|_| ChildWitness {
                statement: &statement,
                proof: &child.proof,
                openings: openings.clone(),
                columns,
            })
            .collect();
        let inputs = |tables| NodeInputs::Prove {
            items: &items,
            tables,
            union: None,
        };
        let outputs: Vec<Output> = [fake_outputs, fake_outputs]
            .concat()
            .into_iter()
            .map(Output::new)
            .collect();

        // An honest reduction over the tree's polynomials fails on the fake's hints.
        let honest = f.tree.prove_rows(d.node_rows(&inputs(&f.tree.tables), 1));
        assert!(
            matches!(&honest, Err(TreeError::Unsatisfied(check)) if check.scope()[0] == "reduction"),
            "{:?}",
            honest.map(|p| p.kind())
        );

        // Reduced over the forged polynomial, every row holds and the root's proof verifies.
        let root = proven_over(&f.tree, 1, d.node_rows(&inputs(&tables), 1), &tables);
        f.tree.read(&root, 1).expect("the root's recursion proof verifies");
        assert_eq!(
            f.tree.verify(&root, &balanced(&outputs, &PAIRS).expect("four leaves")),
            Err(TreeError::Claim(FalseClaim::Dense(DensePoly::Fixed)))
        );
    }

    // Four signers' leanXMSS claims and signatures, one signature per batch, and each one's proof.
    struct Signed {
        batch: XmssBatch,
        claims: Vec<XmssClaim>,
        proofs: Vec<XmssProof>,
    }

    fn signed() -> &'static Signed {
        static SIGNED: LazyLock<Signed> = LazyLock::new(|| {
            let batch = XmssBatch::new(1, Rate::MIN).expect("one signature fits");
            let (claims, proofs) = (leanxmss_host::signers(4).into_iter())
                .map(|(pk, s)| {
                    let claim = XmssClaim {
                        public_param: pk.public_param,
                        merkle_root: pk.merkle_root,
                        epoch: LEAF_INDEX,
                        message: MESSAGE,
                    };
                    let signature = XmssSignature {
                        chain_tips: s.chain_tips,
                        randomness: s.randomness,
                        merkle_proof: s.merkle_proof,
                    };
                    let proof = batch.prove(&[claim], &[signature]).expect("an honest signature");
                    (claim, proof)
                })
                .unzip();
            Signed { batch, claims, proofs }
        });
        &SIGNED
    }

    impl Signed {
        fn leaves(&self) -> Vec<Leaf<'_>> {
            (self.claims.iter().zip(&self.proofs))
                .map(|(c, p)| self.batch.leaf(&[*c], p).expect("one claim"))
                .collect()
        }

        fn statements(&self) -> Vec<LeafStatement> {
            (self.claims.iter())
                .map(|c| self.batch.statement(&[*c]).expect("one claim"))
                .collect()
        }
    }

    // A 2 to 1 tree over the leanXMSS proofs, its two first-level nodes and the node over them.
    struct XmssTree {
        tree: Tree<'static>,
        firsts: [TreeProof; 2],
        node: TreeProof,
    }

    fn xmss_tree() -> &'static XmssTree {
        static TREE: LazyLock<XmssTree> = LazyLock::new(|| {
            let s = signed();
            let tree = Tree::new(s.batch.leaves(), PAIRS).expect("a tree");
            let leaves = s.leaves();
            let firsts = [0, 2].map(|i| tree.prove_first(&leaves[i..i + 2]).expect("honest leaves"));
            let node = tree.prove_node(&firsts).expect("honest children");
            XmssTree { tree, firsts, node }
        });
        &TREE
    }

    #[test]
    fn an_xmss_tree_binds_its_statements() {
        let (s, x) = (signed(), xmss_tree());
        let statements = s.statements();
        let leaves = s.leaves();
        assert_eq!((x.firsts[0].kind(), x.node.kind()), (Kind::First, Kind::Node));
        let four = Subtree::balanced(statements.clone(), &PAIRS).expect("four leaves");
        x.tree.verify(&x.node, &four).expect("the node");
        x.tree
            .verify(&x.firsts[1], &Subtree::First(statements[2..].to_vec()))
            .expect("a first-level node is the root of its leaves");

        // A node over nodes.
        let root = x
            .tree
            .prove_node(&[x.node.clone(), x.node.clone()])
            .expect("honest children");
        x.tree
            .verify(&root, &Subtree::Node(vec![four.clone(), four]))
            .expect("the root over two nodes");

        // Mutation: one claim's message, or two leaves swapped.
        //
        //     the leaves' statements' hashes are the first-level digest's items
        //     → another digest
        let mut changed = s.claims[3];
        changed.message[0] ^= 1;
        let mut forged = statements.clone();
        forged[3] = s.batch.statement(&[changed]).expect("one claim");
        let verify = |leaves: Vec<LeafStatement>| x.tree.verify(&x.node, &Subtree::balanced(leaves, &PAIRS)?);
        assert_eq!(verify(forged), Err(TreeError::Digest));
        let mut swapped = statements;
        swapped.swap(0, 1);
        assert_eq!(verify(swapped), Err(TreeError::Digest));
        let outputs = vec![LeafStatement::from(Output::new([0; 4])); 4];
        assert_eq!(verify(outputs), Err(TreeError::ForeignLeaf { index: 0 }));

        // A leaf whose claims are not its proof's.
        let wrong = s.batch.leaf(&[changed], &s.proofs[3]).expect("one claim");
        assert!(matches!(
            x.tree.prove_first(&[leaves[0].clone(), wrong]),
            Err(TreeError::Leaf { index: 1, .. })
        ));
        // A leaf of another batch size.
        let pair = XmssBatch::new(2, Rate::MIN).expect("two signatures fit");
        let other = pair.leaf(&s.claims[..2], &s.proofs[0]).expect("two claims");
        assert_eq!(
            x.tree.prove_first(&[leaves[0].clone(), other]).map(|_| ()),
            Err(TreeError::ForeignLeaf { index: 1 })
        );
    }

    // A claim-set tree of 2 to 1 over leaves of at most four claims in total.
    const CLAIM_PAIRS: TreeShape = TreeShape {
        claims: Some(ClaimShape {
            capacity: Capacity { claims: 5, groups: 1 },
            small: None,
        }),
        ..PAIRS
    };

    #[test]
    fn a_claim_set_tree_over_xmss_leaves_states_their_signers() {
        // Invariant: a leanXMSS leaf publishes its claims as one group, the set the guest publishes for the same
        // signatures, and a claim-set tree over such leaves states the union of their sets.
        let s = signed();
        let tree = Tree::new(s.batch.leaves(), CLAIM_PAIRS).expect("a claim-set tree");
        let leaves = s.leaves();
        let sets: Vec<ClaimSet> = (s.claims.iter())
            .map(|c| s.batch.claim_set(&[*c]).expect("one claim"))
            .collect();
        let first = |i: usize| {
            let pair = [0, 1].map(|j| ClaimLeaf::new(leaves[i + j].clone(), &sets[i + j]));
            tree.aggregate_leaves(&pair, None).expect("honest leaves")
        };
        let firsts = [first(0), first(2)];
        tree.verify_claims(&firsts[0].proof, &firsts[0].claims)
            .expect("a first-level root");
        let root = tree
            .aggregate(&[&firsts[0], &firsts[1]], None)
            .expect("honest children");

        // The guest's set of the four signers, canonical: the root's.
        let guest = leanxmss_host::SignerSet::from_claims(leanxmss_host::batch(4).set.claims());
        let guest = ClaimSet {
            groups: (guest.label_groups().into_iter())
                .map(|(label, members)| ClaimGroup { label, members })
                .collect(),
        };
        assert_eq!(root.claims, guest);
        tree.verify_claims(&root.proof, &guest)
            .expect("the root of the four signers");

        // A batch's set, in its claims' order, is the guest's for the same signers.
        let four = XmssBatch::new(4, Rate::MIN).expect("four signatures fit");
        let set = four.claim_set(&s.claims).expect("one epoch and message");
        assert_eq!(set.digest(), leanxmss_host::batch(4).set.digest());

        // Mutation: a leaf given another leaf's set, claims of two messages, the set of the root narrowed.
        //
        //     leaf 1's statement states its own claim
        //     → the set given with it is not published by it
        let wrong = [0, 1].map(|j| ClaimLeaf::new(leaves[j].clone(), &sets[0]));
        assert_eq!(
            tree.aggregate_leaves(&wrong, None),
            Err(TreeError::LeafClaims { index: 1 })
        );
        let mut other = s.claims[1];
        other.message[0] ^= 1;
        let pair = XmssBatch::new(2, Rate::MIN).expect("two signatures fit");
        assert_eq!(pair.claim_set(&[s.claims[0], other]), Err(XmssError::Label));
        assert_eq!(
            tree.verify_claims(&root.proof, &firsts[0].claims),
            Err(TreeError::Claims)
        );

        // The claim-set tree and the tree of outputs over the same leaves have sessions of their own.
        let x = xmss_tree();
        assert_ne!(tree.design.session(), x.tree.design.session());
        assert!(matches!(
            x.tree.verify(
                &root.proof,
                &Subtree::balanced(s.statements(), &PAIRS).expect("four leaves")
            ),
            Err(TreeError::Kind { .. } | TreeError::Root(_) | TreeError::Circuit(_))
        ));
    }

    #[test]
    fn a_claim_set_tree_over_sphincs_leaves_states_their_signers() {
        // Invariant: a leanSPHINCS leaf publishes its claims as one group, the set the guest publishes for the same
        // signatures.
        let s = sphincs_signed();
        let tree = Tree::new(s.batch.leaves(), CLAIM_PAIRS).expect("a claim-set tree");
        let sets: Vec<ClaimSet> = (s.claims.iter())
            .map(|c| s.batch.claim_set(&[*c]).expect("one claim"))
            .collect();
        let leaves: Vec<ClaimLeaf<'_>> = (s.leaves().into_iter().zip(&sets))
            .map(|(l, set)| ClaimLeaf::new(l, set))
            .collect();
        let first = tree.aggregate_leaves(&leaves, None).expect("honest leaves");
        let pair = SphincsBatch::new(2, Rate::MIN).expect("two signatures fit");
        let both = pair.claim_set(&s.claims).expect("one message");
        assert_eq!(both.digest(), leansphincs_host::batch(2).set.digest());
        assert_eq!(first.claims, ClaimSet::from_claims(both.claims()));
        tree.verify_claims(&first.proof, &first.claims)
            .expect("the root of both signers");
    }

    #[test]
    fn a_four_to_one_xmss_tree_verifies() {
        let s = signed();
        let shape = TreeShape {
            arity_0: 4,
            arity: 4,
            rate: Rate::MIN,
            claims: None,
        };
        let tree = Tree::new(s.batch.leaves(), shape).expect("a tree");
        let first = tree.prove_first(&s.leaves()).expect("honest leaves");
        let leaves = Subtree::First(s.statements());
        tree.verify(&first, &leaves).expect("a first-level root");
        let node = tree.prove_node(&vec![first; 4]).expect("honest children");
        tree.verify(&node, &Subtree::Node(vec![leaves; 4])).expect("the node");
    }

    // An honest first-level node's rows over a leaf circuit the tree does not have hold, and only the root's settlement of the
    // leaves' fixed polynomial refuses it: its leaves state forged claims no signature backs.
    #[test]
    fn a_fake_leaf_circuit_is_refused_at_the_root() {
        let (s, x) = (signed(), xmss_tree());
        let d = &x.tree.design;
        let Family::Circuit(family) = &d.family else {
            panic!("a tree of leanXMSS proofs")
        };
        let leaf = &family.leaf;
        let position = 0;

        // The honest leaves' rows build the tree's circuit.
        let honest: Vec<CircuitWitness<'_>> = (s.claims[..2].iter().zip(&s.proofs))
            .map(|(c, p)| {
                let Leaf(LeafProof::Circuit { statement, proof, .. }) = s.batch.leaf(&[*c], p).expect("one claim")
                else {
                    panic!("a circuit's leaf")
                };
                CircuitWitness {
                    openings: (leaf.key.verify(&statement, &leaf.session, leaf.rate, proof)).expect("an honest leaf"),
                    statement,
                    proof,
                    columns: leaf.columns(),
                }
            })
            .collect();
        let inputs = NodeInputs::Prove {
            items: &honest,
            tables: &x.tree.tables,
            union: None,
        };
        assert!(
            &proven_circuit(&x.tree, d.first_circuit_rows(family, &inputs)) == x.tree.circuit(position),
            "the leaves build another circuit"
        );

        // A fake circuit of the leaves' heights stating a forged claim.
        let mut forged = s.claims[0];
        forged.merkle_root[0] ^= 1;
        let statement = s.batch.statement(&[forged]).expect("one claim");
        let LeafStatement(Stated::Circuit { words, .. }) = &statement else {
            panic!("a circuit's statement")
        };
        let mut b = Builder::new();
        for w in words {
            let wire = b.free_e(F192::new(w[0], w[1], w[2]));
            b.expose(wire);
        }
        let Finished {
            mut circuit,
            assignment,
            failures,
        } = b.finish();
        assert!(failures.is_empty(), "{failures:?}");
        circuit.floor = leaf.circuit().heights();
        assert_eq!(
            circuit.heights(),
            leaf.circuit().heights(),
            "the fake has the leaves' heights"
        );
        let fake = CircuitKey::new(circuit).expect("the fake fits");
        let proof = fake.prove(&assignment, &leaf.session, leaf.rate);
        assert!(
            (leaf.key.verify(words, &leaf.session, leaf.rate, &proof)).is_err(),
            "natively, the fake is no leanXMSS proof"
        );
        let columns = fake.fixed();
        let openings = fake
            .verify(words, &leaf.session, leaf.rate, &proof)
            .expect("the fake proves its own circuit");
        let items: Vec<CircuitWitness<'_>> = (0..2)
            .map(|_| CircuitWitness {
                statement: words.clone(),
                proof: &proof,
                openings: openings.clone(),
                columns,
            })
            .collect();
        let mut tables = x.tree.tables.clone();
        tables.0[DensePoly::Leaf as usize] = family.leaf_polynomial(columns);
        let inputs = |tables| NodeInputs::Prove {
            items: &items,
            tables,
            union: None,
        };

        // An honest reduction over the tree's polynomials fails on the fake's hints.
        let honest = x.tree.prove_rows(d.first_circuit_rows(family, &inputs(&x.tree.tables)));
        assert!(
            matches!(&honest, Err(TreeError::Unsatisfied(check)) if check.scope()[0] == "reduction"),
            "{:?}",
            honest.map(|p| p.kind())
        );

        // Reduced over the forged polynomial, every row holds and the root's proof verifies.
        let root = proven_over(
            &x.tree,
            position,
            d.first_circuit_rows(family, &inputs(&tables)),
            &tables,
        );
        x.tree
            .read(&root, position)
            .expect("the root's recursion proof verifies");
        let expected = Subtree::First(vec![statement.clone(), statement]);
        assert_eq!(
            x.tree.verify(&root, &expected),
            Err(TreeError::Claim(FalseClaim::Dense(DensePoly::Leaf)))
        );
        // A node carrying the fake's claims cannot reduce them honestly.
        assert!(matches!(
            x.tree.prove_node(&[root, x.firsts[1].clone()]),
            Err(TreeError::Unsatisfied(check)) if check.scope()[0] == "reduction"
        ));
    }

    // Two leanSPHINCS signers' claims, one signature per batch, and each one's proof.
    struct SphincsSigned {
        batch: SphincsBatch,
        claims: Vec<SphincsClaim>,
        proofs: Vec<SphincsProof>,
    }

    fn sphincs_signed() -> &'static SphincsSigned {
        static SIGNED: LazyLock<SphincsSigned> = LazyLock::new(|| {
            let batch = SphincsBatch::new(1, Rate::MIN).expect("one signature fits");
            let (claims, signatures) = crate::rec::sphincs::tests::signed(2);
            let proofs = (claims.iter().zip(signatures))
                .map(|(c, s)| batch.prove(&[*c], &[s]).expect("an honest signature"))
                .collect();
            SphincsSigned { batch, claims, proofs }
        });
        &SIGNED
    }

    impl SphincsSigned {
        fn leaves(&self) -> Vec<Leaf<'_>> {
            (self.claims.iter().zip(&self.proofs))
                .map(|(c, p)| self.batch.leaf(&[*c], p).expect("one claim"))
                .collect()
        }

        fn statements(&self) -> Vec<LeafStatement> {
            (self.claims.iter())
                .map(|c| self.batch.statement(&[*c]).expect("one claim"))
                .collect()
        }
    }

    // A 2 to 1 tree over the leanSPHINCS proofs, its first-level node and a node over two copies of it.
    struct SphincsTree {
        tree: Tree<'static>,
        first: TreeProof,
        node: TreeProof,
    }

    fn sphincs_tree() -> &'static SphincsTree {
        static TREE: LazyLock<SphincsTree> = LazyLock::new(|| {
            let s = sphincs_signed();
            let tree = Tree::new(s.batch.leaves(), PAIRS).expect("a tree");
            let first = tree.prove_first(&s.leaves()).expect("honest leaves");
            let node = tree
                .prove_node(&[first.clone(), first.clone()])
                .expect("honest children");
            SphincsTree { tree, first, node }
        });
        &TREE
    }

    // A tree proof's recursion proof, verified against its own tree's circuit under this session.
    fn under(tree: &Tree<'_>, session: &SessionId, p: &TreeProof) -> Result<(), RecError> {
        let position = tree.known(p).expect("a proof of one of the tree's circuits");
        (tree.keys[position])
            .verify(&p.limbs(), session, tree.design.rate, &p.proof)
            .map(drop)
    }

    // Trees of leanXMSS proofs, of leanSPHINCS proofs and of RISC-V proofs: each tree's session names its leaf family, so no
    // tree takes another's proofs, and nothing but the session and the statement refuses them.
    //
    //     the leanXMSS and leanSPHINCS trees share their heights and statement layout: their proofs have one shape
    //     a proof against its own tree's circuit under the other tree's session fails at its first stage, flock's zerocheck
    //     → as a child of the other tree's node, or as its root, it fails with that same error
    //     a RISC-V tree's statement has another length than a circuit-leaf tree's
    //     → each refuses the other's proofs at the statement's length, as of no circuit of its own
    #[test]
    fn a_tree_refuses_another_familys_tree_proofs() {
        let (f, s, x) = (fixture(), signed(), xmss_tree());
        let (p, y) = (sphincs_signed(), sphincs_tree());
        let xmss_first = Subtree::First(s.statements()[..2].to_vec());
        let xmss_node = Subtree::balanced(s.statements(), &PAIRS).expect("four leaves");
        let sphincs_first = Subtree::First(p.statements());
        let sphincs_node = Subtree::Node(vec![sphincs_first.clone(); 2]);
        let runs_first = Subtree::First(f.statements()[..2].to_vec());
        y.tree.verify(&y.first, &sphincs_first).expect("a first-level root");
        y.tree.verify(&y.node, &sphincs_node).expect("the node");
        let sessions = [&f.tree, &x.tree, &y.tree].map(|t| t.design.session());
        assert!(
            sessions[0] != sessions[1] && sessions[1] != sessions[2] && sessions[0] != sessions[2],
            "each family has its session"
        );
        assert_eq!(
            (x.tree.design.tiers[SMALL].taus, x.tree.design.statement),
            (y.tree.design.tiers[SMALL].taus, y.tree.design.statement),
            "the leanXMSS and leanSPHINCS trees' proofs have one shape"
        );

        // The session alone: each proof against its own tree's circuit, under the other tree's session.
        let session_refusal = |tree: &Tree<'_>, other: &Tree<'_>, p: &TreeProof| {
            under(tree, &tree.design.session(), p).expect("its own session");
            let refused = under(tree, &other.design.session(), p).expect_err("the other tree's session");
            assert!(
                matches!(
                    refused,
                    RecError::Flock(FlockError::Zerocheck(ZerocheckError::TerminalMismatch))
                ),
                "{refused:?}"
            );
            VerifyError::from(refused)
        };

        // Each kind of one circuit-leaf tree's proofs as the second child of the other's node, and as its root, given an
        // expected tree of its own leaves whose top is the proof's kind.
        for (what, tree, own, other, other_tree, expected) in [
            (
                "leanSPHINCS first-level",
                &x.tree,
                &x.firsts[0],
                &y.first,
                &y.tree,
                &xmss_first,
            ),
            ("leanSPHINCS node", &x.tree, &x.firsts[0], &y.node, &y.tree, &xmss_node),
            (
                "leanXMSS first-level",
                &y.tree,
                &y.first,
                &x.firsts[0],
                &x.tree,
                &sphincs_first,
            ),
            ("leanXMSS node", &y.tree, &y.first, &x.node, &x.tree, &sphincs_node),
        ] {
            let error = session_refusal(other_tree, tree, other);
            assert_eq!(
                tree.prove_node(&[own.clone(), other.clone()]),
                Err(TreeError::Child {
                    index: 1,
                    error: error.clone()
                }),
                "{what} as a child"
            );
            assert_eq!(
                tree.verify(other, expected),
                Err(TreeError::Root(error)),
                "{what} as a root"
            );
        }

        // A RISC-V tree and a leanXMSS tree, each given the other's first-level node: its statement has another length
        // than the tree's statements, so it is of no circuit of the tree.
        assert_ne!(f.tree.design.statement.len(), x.tree.design.statement.len());
        for (what, tree, own, other, expected) in [
            (
                "leanXMSS in a RISC-V tree",
                &f.tree,
                &f.firsts[0],
                &x.firsts[0],
                &runs_first,
            ),
            (
                "RISC-V in a leanXMSS tree",
                &x.tree,
                &x.firsts[0],
                &f.firsts[0],
                &xmss_first,
            ),
        ] {
            let error = TreeError::Circuit(0);
            assert_eq!(
                tree.prove_node(&[own.clone(), other.clone()]),
                Err(error.clone()),
                "{what} as a child"
            );
            assert_eq!(tree.verify(other, expected), Err(error), "{what} as a root");
        }
    }

    // A first-level node whose reduction a cheating prover forged: its rows hold, its claims are false.
    fn forged_first(f: &Fixture, forge: Forge) -> TreeProof {
        let d = &f.tree.design;
        let items: Vec<LeafWitness> = (f.leaves[..2].iter())
            .map(|(proof, output)| LeafWitness {
                proof: &proof.0,
                openings: program().verify_recording(*output, proof).expect("an honest leaf"),
                output: *output.words(),
                set: [0; 4],
            })
            .collect();
        let Family::Runs(shape) = &d.family else {
            panic!("a tree of RISC-V proofs")
        };
        let rows = d.first_runs_rows(
            shape,
            &NodeInputs::Prove {
                items: &items,
                tables: &f.tree.tables,
                union: None,
            },
        );
        let reduction = forged_reduction(&d.session(), &d.vars, &f.tree.tables, &rows.claim_values(), forge);
        let Finished {
            assignment, failures, ..
        } = rows.reduce(d, ProofSource::Proof(&reduction, &[]));
        assert!(failures.is_empty(), "{forge:?}: {failures:?}");
        tree_proof(&f.tree, 0, &f.tree.keys[0], &assignment)
    }

    // Reduced claims that satisfy every row and are false: the root refuses them, and an honest node cannot carry them.
    #[test]
    fn forged_reduced_claims_are_refused() {
        let f = fixture();
        let outputs = balanced(&f.outputs()[..2], &PAIRS).expect("two leaves");
        for (forge, refusal) in [
            (Forge::Dense, FalseClaim::Dense(DensePoly::Bytecode)),
            (
                Forge::Matrix,
                FalseClaim::Matrix {
                    table: TableId::ALU.name(),
                    part: Part::Class,
                },
            ),
        ] {
            let forged = forged_first(f, forge);
            assert_eq!(
                f.tree.verify(&forged, &outputs),
                Err(TreeError::Claim(refusal)),
                "{forge:?}"
            );
            let carried = f.tree.prove_node(&[forged, f.firsts[1].clone()]);
            assert!(
                matches!(&carried, Err(TreeError::Unsatisfied(check)) if check.scope()[0] == "reduction"),
                "{forge:?}: {:?}",
                carried.map(|p| p.kind())
            );
        }
    }

    #[test]
    fn tree_proof_bytes_round_trip() {
        let f = fixture();
        let bytes = f.root.to_bytes();
        assert_eq!(TreeProof::from_bytes(&bytes).as_ref(), Ok(&f.root));

        // Cuts inside the header, inside the body's prefix, and inside the recursion proof.
        for cut in [0, 1, 5, 6, 11, 35, bytes.len() / 2, bytes.len() - 1] {
            assert_eq!(
                TreeProof::from_bytes(&bytes[..cut]),
                Err(DecodeError::Malformed),
                "cut at {cut}"
            );
        }
        assert_eq!(
            TreeProof::from_bytes(&[&bytes[..], &[0]].concat()),
            Err(DecodeError::Malformed)
        );

        // The body starts after the 6-byte header.
        //
        //     | header: 6 | rate: 1 | n_words: 4 | kind word ...
        //     byte 6 = the rate, byte 11 = the kind word's low byte, byte 19 its second limb's
        let mut kind = bytes.clone();
        kind[11] = 0;
        assert_eq!(
            TreeProof::from_bytes(&kind).map(|p| p.kind()),
            Ok(Kind::First),
            "the other kind's code decodes"
        );
        kind[11] = 2;
        let foreign = TreeProof::from_bytes(&kind).expect("a kind is any index");
        let expected = balanced(&f.outputs(), &PAIRS).expect("four leaves");
        assert_eq!(
            f.tree.verify(&foreign, &expected),
            Err(TreeError::Circuit(2)),
            "an index of no circuit"
        );
        let mut wide = bytes.clone();
        wide[19] = 1;
        assert_eq!(
            TreeProof::from_bytes(&wide),
            Err(DecodeError::Malformed),
            "a kind that is no index"
        );
        let mut rate = bytes;
        rate[6] = 0;
        assert_eq!(
            TreeProof::from_bytes(&rate),
            Err(DecodeError::Malformed),
            "a rate out of range"
        );
    }

    // A tree of outputs keeps the heights and statement layout of protocol version `leanvm-tree-12`, before the tiers, the
    // absent STEP and LINK tables aside. Its session tag also names its leaf family, so it is pinned here as it is now.
    #[test]
    fn a_tree_of_outputs_keeps_tree_12s_heights_and_layout() {
        let d = &fixture().tree.design;
        assert_eq!(d.tiers.len(), 1);
        let heights = [Some(16), Some(16), Some(14), Some(10), Some(14), None, None, Some(10)];
        assert_eq!(d.tiers[SMALL].taus.into_values(), heights);
        assert_eq!(d.statement.len(), 97);
        let sections = [
            Section::Kind,
            Section::Digest,
            Section::DensePoint,
            Section::DenseValues,
            Section::Rows,
            Section::Cols,
            Section::Matrices,
        ];
        assert_eq!(
            sections.map(|s| d.statement.range(s)),
            [0..1, 1..3, 3..24, 24..27, 27..41, 41..55, 55..97]
        );
        assert_eq!(
            d.session_under(b"leanvm-tree-12").0,
            [
                175, 244, 77, 226, 2, 53, 216, 225, 108, 105, 36, 89, 227, 32, 16, 198, 75, 141, 243, 78, 198, 200, 59,
                193, 25, 116, 199, 81, 72, 118, 40, 11
            ]
        );
    }

    #[test]
    fn a_tree_over_zero_knowledge_leaves_verifies() {
        // Two zero-knowledge leaves of distinct advice under one first-level node, which is the root.
        //
        // The leaves hide their advice; the node holds only their proofs, so it need not be zero knowledge itself.
        let leaves: Vec<(Proof, Output)> = [7, 8]
            .map(|advice| {
                let run = Prover::new(Rate::MIN)
                    .zero_knowledge(Randomness::Fixed([advice as u8; 32]))
                    .prove(program(), &[advice])
                    .expect("the run halts");
                (run.proof, run.output)
            })
            .into();
        let shape = LeafShape::of(&leaves[0].0).expect("a canonical announcement");
        assert!(shape.is_zero_knowledge());
        let tree = Tree::new(runs(shape), PAIRS).expect("a tree");
        let pair: Vec<Leaf<'_>> = leaves.iter().map(|(p, o)| Leaf::new(p, *o)).collect();
        let root = tree.prove_first(&pair).expect("honest leaves");
        let outputs: Vec<Output> = leaves.iter().map(|l| l.1).collect();
        tree.verify(&root, &balanced(&outputs, &PAIRS).expect("two leaves"))
            .expect("the root");

        // A plain leaf of the same run has another shape: the tree refuses it.
        let plain = Prover::new(Rate::MIN).prove(program(), &[7]).expect("the run halts");
        let mixed = [Leaf::new(&plain.proof, plain.output), pair[1].clone()];
        assert_eq!(
            tree.prove_first(&mixed).err(),
            Some(TreeError::ForeignLeaf { index: 0 })
        );
    }

    mod claim_sets {
        //! Claim-set trees: proofs anyone combines, each declaring the union of its children's sets or part of it.

        use crate::cpu::Prover;
        use crate::rec::circuit::Builder;
        use crate::rec::tree::design::{ChildWitness, LARGE, Level, NodeInputs, Place, SMALL};
        use crate::rec::tree::statement::Section;
        use crate::rec::tree::union::tests::{absent_at, unbacked};
        use crate::rec::tree::*;
        use crate::rv::Region;
        use crate::rv::asm::*;
        use std::sync::LazyLock;

        // A program whose output is its four advice words, after a loop of `rounds` that reads every framework block: a leaf
        // that publishes whatever set the advice names, which the tree's mechanics need and no more. Another round count is
        // another program, of the same shape.
        fn looping(rounds: u64) -> Program {
            let text = Asm::new()
                .li(Reg::T0, Region::ADVICE.base())
                .load(Ld, Reg::A0, 0, Reg::T0)
                .load(Ld, Reg::A1, 8, Reg::T0)
                .load(Ld, Reg::A2, 16, Reg::T0)
                .load(Ld, Reg::A3, 24, Reg::T0)
                .li(Reg::T1, rounds)
                .label("loop")
                .i(Addi, Reg::T1, Reg::T1, -1)
                .branch(Bne, Reg::T1, Reg::ZERO, "loop")
                .exit()
                .finish();
            Program::new(&text, Region::TEXT.base(), vec![3, 5], 2, 2).expect("a valid program")
        }

        static PROGRAM: LazyLock<Program> = LazyLock::new(|| looping(9));

        fn program() -> &'static Program {
            &PROGRAM
        }

        fn member(i: u64) -> [u64; 4] {
            [i, 7 * i + 1, i << 9, 0x5eed ^ i]
        }

        fn label(tag: u64, word: u64) -> [u64; 6] {
            [tag, word, 0, 0, 0, 1]
        }

        fn group(tag: u64, word: u64, members: &[u64]) -> ClaimGroup {
            ClaimGroup {
                label: label(tag, word),
                members: members.iter().map(|&i| member(i)).collect(),
            }
        }

        fn set(groups: Vec<ClaimGroup>) -> ClaimSet {
            ClaimSet { groups }
        }

        /// Three leaves' sets, overlapping, in the order their programs wrote them (not canonical), of two label tags.
        fn sets() -> [ClaimSet; 3] {
            [
                set(vec![group(1, 9, &[3, 1]), group(1, 2, &[1])]),
                set(vec![group(1, 9, &[1, 4]), group(2, 0, &[5])]),
                set(vec![group(1, 8, &[1]), group(2, 0, &[6, 5])]),
            ]
        }

        const CAPACITY: Capacity = Capacity { claims: 12, groups: 4 };

        fn union(sets: &[&ClaimSet]) -> ClaimSet {
            ClaimSet::from_claims(sets.iter().flat_map(|s| s.claims()))
        }

        struct Fixture {
            tree: Tree<'static>,
            sets: [ClaimSet; 3],
            leaves: Vec<(Proof, Output)>,
            /// Each leaf's first-level proof, declaring its set.
            firsts: Vec<Aggregate>,
            /// The first two firsts' union.
            pair: Aggregate,
        }

        fn shape(claims: Option<ClaimShape>) -> TreeShape {
            TreeShape {
                arity_0: 1,
                arity: 3,
                rate: Rate::MIN,
                claims,
            }
        }

        fn runs(shape: LeafShape) -> Leaves<'static> {
            Leaves::Runs {
                program: program(),
                shape,
            }
        }

        fn leaf_proof(set: &ClaimSet) -> (Proof, Output) {
            leaf_proof_of(program(), set)
        }

        fn leaf_proof_of(program: &Program, set: &ClaimSet) -> (Proof, Output) {
            let run = Prover::new(Rate::MIN)
                .prove(program, &chain(&set.digest()))
                .expect("the run halts");
            (run.proof, run.output)
        }

        static FIXTURE: LazyLock<Fixture> = LazyLock::new(|| {
            let sets = sets();
            let leaves: Vec<(Proof, Output)> = sets.iter().map(leaf_proof).collect();
            let leaf = LeafShape::of(&leaves[0].0).expect("a canonical announcement");
            let tree = Tree::new(runs(leaf), shape(Some(ClaimShape::new(CAPACITY)))).expect("a tree");
            let firsts: Vec<Aggregate> = (sets.iter().zip(&leaves))
                .map(|(set, (proof, output))| {
                    let leaf = ClaimLeaf::new(Leaf::new(proof, *output), set);
                    tree.aggregate_leaves(&[leaf], None).expect("an honest leaf")
                })
                .collect();
            let pair = tree
                .aggregate(&[&firsts[0], &firsts[1]], None)
                .expect("honest children");
            Fixture {
                tree,
                sets,
                leaves,
                firsts,
                pair,
            }
        });

        fn fixture() -> &'static Fixture {
            &FIXTURE
        }

        #[test]
        fn a_tree_has_a_node_circuit_for_each_arity() {
            let f = fixture();
            let nodes = [Level::First, Level::Node(2), Level::Node(3)];
            let places: Vec<Place> = nodes.map(|level| Place { tier: SMALL, level }).into();
            assert_eq!(f.tree.design.places, places);
            let d = &f.tree.design;
            assert!(d.place(SMALL, Level::Node(3)).is_some() && d.place(SMALL, Level::Node(4)).is_none());
        }

        #[test]
        fn the_union_of_overlapping_children_of_any_kind_verifies() {
            let f = fixture();
            for (first, set) in f.firsts.iter().zip(&f.sets) {
                assert_eq!(first.claims, union(&[set]), "a leaf's set, made canonical");
                f.tree
                    .verify_claims(&first.proof, &first.claims)
                    .expect("a first-level root");
            }
            assert_eq!(f.pair.claims, union(&[&f.sets[0], &f.sets[1]]));
            f.tree
                .verify_claims(&f.pair.proof, &f.pair.claims)
                .expect("a root of two");
            // Three children: a node, a first-level proof, and a repeat of claims the node holds.
            let all = (f.tree.aggregate(&[&f.pair, &f.firsts[2], &f.firsts[0]], None)).expect("honest children");
            let expected = union(&[&f.sets[0], &f.sets[1], &f.sets[2]]);
            assert_eq!(all.claims, expected);
            assert!(expected.n_claims() < f.sets.iter().map(ClaimSet::n_claims).sum::<usize>());
            assert_eq!(all.proof.kind(), Kind::Node);
            f.tree
                .verify_claims(&all.proof, &expected)
                .expect("the root of all three");
        }

        #[test]
        fn a_child_given_twice_or_alone_is_its_own_union() {
            let f = fixture();
            let twice = f
                .tree
                .aggregate(&[&f.firsts[1], &f.firsts[1]], None)
                .expect("duplicates");
            assert_eq!(twice.claims, f.firsts[1].claims);
            let alone = f.tree.aggregate(&[&f.pair], None).expect("one child");
            assert_eq!(alone.claims, f.pair.claims);
            f.tree
                .verify_claims(&alone.proof, &alone.claims)
                .expect("a republished root");
        }

        #[test]
        fn a_node_may_omit_groups_and_declare_part_of_one() {
            let f = fixture();
            // Of the pair's groups, one member of (1, 9) only: (1, 2) and (2, 0) are omitted.
            let part = set(vec![group(1, 9, &[4])]);
            let narrowed = f
                .tree
                .aggregate(&[&f.pair], Some(&part))
                .expect("a covered declaration");
            assert_eq!(narrowed.claims, part);
            f.tree.verify_claims(&narrowed.proof, &part).expect("a narrowed root");
            // And nothing at all.
            let empty = f
                .tree
                .aggregate(&[&f.pair], Some(&ClaimSet::new()))
                .expect("an empty declaration");
            f.tree
                .verify_claims(&empty.proof, &ClaimSet::new())
                .expect("an empty root");
        }

        #[test]
        fn an_uncovered_declaration_is_refused() {
            let f = fixture();
            // (1, 8) is the third leaf's, and a member at another label is another claim, of either tag.
            for declared in [
                union(&[&f.sets[2]]),
                set(vec![group(1, 2, &[3])]),
                set(vec![group(2, 1, &[5])]),
            ] {
                assert!(
                    matches!(
                        f.tree.aggregate(&[&f.firsts[0], &f.firsts[1]], Some(&declared)),
                        Err(TreeError::NotCovered(_))
                    ),
                    "{declared:?}"
                );
            }
            // A member under the other tag.
            let claim = Claim {
                label: label(2, 2),
                member: member(1),
            };
            assert_eq!(
                f.tree.aggregate(&[&f.firsts[0]], Some(&ClaimSet::from_claims([claim]))),
                Err(TreeError::NotCovered(claim))
            );
        }

        #[test]
        fn forged_coverage_is_refused() {
            let f = fixture();
            // In rows: the pair's union and a claim no child holds, the rest selected honestly.
            let d = &f.tree.design;
            let kind = d.place(SMALL, Level::Node(2)).expect("a node of two");
            let mut declared = f.pair.claims.clone();
            declared.groups[0].members.push(member(99));
            let proofs = [&f.firsts[0].proof, &f.firsts[1].proof];
            let statements: Vec<TreeStatement> = (proofs.iter()).map(|p| p.statement(d.statement)).collect();
            let items = f
                .tree
                .child_witnesses(SMALL, &proofs, &statements)
                .expect("honest children");
            let shape = d.union_shape(kind).expect("a claim-set tree");
            let fill = unbacked(&shape, &[&f.firsts[0].claims, &f.firsts[1].claims], &declared);
            let inputs = NodeInputs::Prove {
                items: &items,
                tables: &f.tree.tables,
                union: Some(&fill),
            };
            let forged = f.tree.prove_rows(d.node_rows(&inputs, kind));
            assert!(
                matches!(&forged, Err(TreeError::Unsatisfied(check)) if check.scope().iter().any(|s| s == "coverage")),
                "{forged:?}"
            );

            // Natively: a child handed with another set than its statement's, a leaf whose output is not its set's.
            let lying = Aggregate {
                proof: f.firsts[0].proof.clone(),
                claims: f.pair.claims.clone(),
            };
            assert_eq!(
                f.tree.aggregate(&[&f.firsts[1], &lying], None),
                Err(TreeError::ChildClaims { index: 1 })
            );
            let (proof, output) = &f.leaves[0];
            let leaf = ClaimLeaf::new(Leaf::new(proof, *output), &f.sets[1]);
            assert_eq!(
                f.tree.aggregate_leaves(&[leaf], None),
                Err(TreeError::LeafClaims { index: 0 })
            );
        }

        #[test]
        fn a_root_with_another_or_noncanonical_set_is_refused() {
            let f = fixture();
            let root = &f.pair;
            // The same claims in another order: not canonical.
            let mut shuffled = root.claims.clone();
            shuffled.groups.reverse();
            assert_eq!(
                f.tree.verify_claims(&root.proof, &shuffled),
                Err(TreeError::ClaimSet(ClaimSetError::UnsortedGroups))
            );
            assert_eq!(
                f.tree.verify_claims(&root.proof, &f.firsts[0].claims),
                Err(TreeError::Claims)
            );
            let mut over = root.claims.clone();
            over.groups.push(group(3, 0, &(0..12).collect::<Vec<_>>()));
            assert!(matches!(
                f.tree.verify_claims(&root.proof, &over),
                Err(TreeError::ClaimSet(ClaimSetError::TooManyClaims { .. }))
            ));
        }

        #[test]
        fn a_narrowed_proof_cannot_be_widened_again() {
            let f = fixture();
            let part = union(&[&f.sets[0]]);
            let narrowed = f
                .tree
                .aggregate(&[&f.pair], Some(&part))
                .expect("a covered declaration");
            // Its parent sees the narrowed set only.
            assert!(matches!(
                f.tree.aggregate(&[&narrowed], Some(&f.pair.claims)),
                Err(TreeError::NotCovered(_))
            ));
            let widened = Aggregate {
                proof: narrowed.proof.clone(),
                claims: f.pair.claims.clone(),
            };
            assert_eq!(
                f.tree.aggregate(&[&widened], None),
                Err(TreeError::ChildClaims { index: 0 })
            );
            assert_eq!(
                f.tree.verify_claims(&narrowed.proof, &f.pair.claims),
                Err(TreeError::Claims)
            );
        }

        #[test]
        fn positional_and_claim_set_proofs_are_not_confused() {
            let f = fixture();
            let leaf = LeafShape::of(&f.leaves[0].0).expect("a canonical announcement");
            let outputs_tree = Tree::new(runs(leaf), shape(None)).expect("a tree of outputs");
            let (proof, output) = &f.leaves[0];
            let positional = outputs_tree
                .prove_first(&[Leaf::new(proof, *output)])
                .expect("an honest leaf");
            let positional_leaves = Subtree::First(vec![(*output).into()]);
            (outputs_tree.verify(&positional, &positional_leaves)).expect("a positional root");

            // Each tree refuses the other's operations.
            let claims = TreeError::Semantics { claims: true };
            let outputs = TreeError::Semantics { claims: false };
            assert_eq!(f.tree.prove_first(&[Leaf::new(proof, *output)]), Err(claims.clone()));
            assert_eq!(f.tree.verify(&positional, &positional_leaves), Err(claims));
            let set_leaf = ClaimLeaf::new(Leaf::new(proof, *output), &f.sets[0]);
            assert_eq!(outputs_tree.aggregate_leaves(&[set_leaf], None), Err(outputs.clone()));
            assert_eq!(
                outputs_tree.verify_claims(&f.firsts[0].proof, &f.firsts[0].claims),
                Err(outputs)
            );

            // A positional root's statement read as a claim set: another session, so its proof does not verify.
            let as_claims = Aggregate {
                proof: positional.clone(),
                claims: f.firsts[0].claims.clone(),
            };
            assert!(matches!(
                f.tree.verify_claims(&positional, &f.firsts[0].claims),
                Err(TreeError::Root(_) | TreeError::Circuit(_))
            ));
            assert!(matches!(
                f.tree.aggregate(&[&as_claims], None),
                Err(TreeError::Child { index: 0, .. } | TreeError::Circuit(_))
            ));
            assert!(matches!(
                outputs_tree.verify(&f.firsts[0].proof, &positional_leaves),
                Err(TreeError::Root(_) | TreeError::Circuit(_))
            ));
        }

        #[test]
        fn aggregates_from_different_provers_combine() {
            let f = fixture();
            // Another party builds the tree from the same program and shape, and proves the third leaf.
            let leaf = LeafShape::of(&f.leaves[0].0).expect("a canonical announcement");
            let theirs = Tree::new(runs(leaf), shape(Some(ClaimShape::new(CAPACITY)))).expect("the same tree");
            let (proof, output) = &f.leaves[2];
            let third = (theirs.aggregate_leaves(&[ClaimLeaf::new(Leaf::new(proof, *output), &f.sets[2])], None))
                .expect("an honest leaf");
            let received = Aggregate {
                proof: TreeProof::from_bytes(&third.proof.to_bytes()).expect("a tree proof"),
                claims: ClaimSet::from_bytes(&third.claims.to_bytes()).expect("a set"),
            };
            let combined = f
                .tree
                .aggregate(&[&f.pair, &received], None)
                .expect("their proof is ours");
            theirs
                .verify_claims(&combined.proof, &combined.claims)
                .expect("our root is theirs");
        }

        #[test]
        fn trees_of_different_leaf_programs_do_not_combine() {
            let f = fixture();
            // Another leaf program, of the same shape and publishing the same sets: a tree is its leaf program's, so the
            // other's tree is another tree, and neither takes the other's leaves, aggregates or roots.
            let other = looping(10);
            let leaves: Vec<(Proof, Output)> = f.sets[..2].iter().map(|set| leaf_proof_of(&other, set)).collect();
            let leaf = LeafShape::of(&leaves[0].0).expect("a canonical announcement");
            assert_eq!(Some(leaf), LeafShape::of(&f.leaves[0].0).ok(), "one leaf shape");
            let theirs = Tree::new(
                Leaves::Runs {
                    program: &other,
                    shape: leaf,
                },
                shape(Some(ClaimShape::new(CAPACITY))),
            )
            .expect("a tree");
            let firsts: Vec<Aggregate> = (f.sets.iter().zip(&leaves))
                .map(|(set, (proof, output))| {
                    let leaf = ClaimLeaf::new(Leaf::new(proof, *output), set);
                    theirs.aggregate_leaves(&[leaf], None).expect("an honest leaf")
                })
                .collect();
            let pair = theirs
                .aggregate(&[&firsts[0], &firsts[1]], None)
                .expect("honest children");
            // Each tree's aggregates state the same sets: only the leaf program tells them apart.
            assert_eq!(pair.claims, f.pair.claims);

            for (tree, own, foreign_leaves, foreign) in [
                (&f.tree, &f.firsts[0], &leaves, [&firsts[0], &pair]),
                (&theirs, &firsts[0], &f.leaves, [&f.firsts[0], &f.pair]),
            ] {
                // A leaf of the other program does not verify as this tree's leaf.
                let (proof, output) = &foreign_leaves[0];
                let leaf = ClaimLeaf::new(Leaf::new(proof, *output), &f.sets[0]);
                assert!(matches!(
                    tree.aggregate_leaves(&[leaf], None),
                    Err(TreeError::Leaf { index: 0, .. })
                ));
                // The other tree's first-level aggregate and node, alone or beside one of this tree's, are not children,
                // and do not verify as this tree's roots.
                for child in foreign {
                    let refused = tree.aggregate(&[child], None);
                    assert!(matches!(refused, Err(TreeError::Child { index: 0, .. })), "{refused:?}");
                    let refused = tree.aggregate(&[own, child], None);
                    assert!(matches!(refused, Err(TreeError::Child { index: 1, .. })), "{refused:?}");
                    let refused = tree.verify_claims(&child.proof, &child.claims);
                    assert!(matches!(refused, Err(TreeError::Root(_))), "{refused:?}");
                }
            }
        }

        #[test]
        fn sets_past_the_capacity_are_refused() {
            let f = fixture();
            let big = set(vec![group(1, 1, &(0..11).collect::<Vec<_>>())]);
            let (proof, output) = leaf_proof(&big);
            let first = (f
                .tree
                .aggregate_leaves(&[ClaimLeaf::new(Leaf::new(&proof, output), &big)], None))
            .expect("a set within the capacity");
            assert_eq!(f.tree.aggregate(&[&first, &f.pair], None), Err(TreeError::Capacity));
        }

        /// The small tier of the tiered fixture: nodes of two children declaring fewer than five claims in at most two groups.
        const SMALL_TIER: Tier = Tier {
            arity: 2,
            capacity: Capacity { claims: 5, groups: 2 },
        };

        /// The fixture's leaves in a tree of two tiers.
        struct Tiered {
            tree: Tree<'static>,
            /// Each leaf's first-level proof, of the small tier.
            firsts: Vec<Aggregate>,
            /// The first two firsts' union, five claims in three groups: of the large tier.
            pair: Aggregate,
        }

        // Whether a proof is of a claim-set tree's large tier.
        fn is_large(tree: &Tree<'_>, proof: &TreeProof) -> bool {
            tree.known(proof).is_ok_and(|p| tree.design.places[p].tier == LARGE)
        }

        fn tiered_tree() -> Tree<'static> {
            let leaf = LeafShape::of(&fixture().leaves[0].0).expect("a canonical announcement");
            let claims = ClaimShape {
                capacity: CAPACITY,
                small: Some(SMALL_TIER),
            };
            Tree::new(runs(leaf), shape(Some(claims))).expect("a tree of two tiers")
        }

        static TIERED: LazyLock<Tiered> = LazyLock::new(|| {
            let f = fixture();
            let tree = tiered_tree();
            let firsts: Vec<Aggregate> = (f.sets.iter().zip(&f.leaves))
                .map(|(set, (proof, output))| {
                    let leaf = ClaimLeaf::new(Leaf::new(proof, *output), set);
                    tree.aggregate_leaves(&[leaf], None).expect("an honest leaf")
                })
                .collect();
            let pair = tree
                .aggregate(&[&firsts[0], &firsts[1]], None)
                .expect("honest children");
            Tiered { tree, firsts, pair }
        });

        fn tiered() -> &'static Tiered {
            &TIERED
        }

        #[test]
        fn a_tree_of_two_tiers_has_a_wrap_and_heights_per_tier() {
            let t = tiered();
            let d = &t.tree.design;
            let small = |level| Place { tier: SMALL, level };
            let large = |level| Place { tier: LARGE, level };
            assert_eq!(
                d.places,
                [
                    small(Level::First),
                    small(Level::Node(2)),
                    small(Level::Wrap),
                    large(Level::Node(3)),
                ]
            );
            let d = &t.tree.design;
            assert!(d.place(SMALL, Level::Node(3)).is_none() && d.place(SMALL, Level::Wrap).is_some());
            assert!(d.place(LARGE, Level::Node(3)).is_some() && d.place(LARGE, Level::Node(2)).is_none());
            // Each tier's circuits are at its own heights.
            for (p, place) in d.places.iter().enumerate() {
                assert_eq!(t.tree.circuit(p).heights(), d.tiers[place.tier].taus, "{place:?}");
            }
            // A kind names one circuit, whose proofs state it.
            for p in 0..d.places.len() {
                assert_eq!(d.position(d.code(p)), Some(p));
            }
        }

        #[test]
        fn small_unions_stay_small_and_large_proofs_are_wrapped_to_combine() {
            let (t, f) = (tiered(), fixture());
            for first in &t.firsts {
                assert!(!is_large(&t.tree, &first.proof));
                (t.tree)
                    .verify_claims(&first.proof, &first.claims)
                    .expect("a small root");
            }
            assert!(is_large(&t.tree, &t.pair.proof));
            assert_eq!(t.pair.claims, union(&[&f.sets[0], &f.sets[1]]));
            (t.tree)
                .verify_claims(&t.pair.proof, &t.pair.claims)
                .expect("a large root");
            let twice = (t.tree.aggregate(&[&t.firsts[2], &t.firsts[2]], None)).expect("duplicates");
            assert!(!is_large(&t.tree, &twice.proof));
            assert_eq!(twice.claims, t.firsts[2].claims);

            // Three children, one large: wrapped, then the large tier's node of three.
            let all = (t.tree.aggregate(&[&t.pair, &t.firsts[2], &t.firsts[0]], None)).expect("a large child");
            assert!(is_large(&t.tree, &all.proof));
            assert_eq!(all.claims, union(&[&f.sets[0], &f.sets[1], &f.sets[2]]));
            (t.tree)
                .verify_claims(&all.proof, &all.claims)
                .expect("the root of all three");

            // The large pair narrowed to what the small tier holds: wrapped, then a small node; and not widened again.
            let part = set(vec![group(1, 9, &[1, 3, 4])]);
            let narrowed = (t.tree.aggregate(&[&t.pair], Some(&part))).expect("a covered declaration");
            assert!(!is_large(&t.tree, &narrowed.proof));
            t.tree.verify_claims(&narrowed.proof, &part).expect("a narrowed root");
            assert!(matches!(
                t.tree.aggregate(&[&narrowed], Some(&t.pair.claims)),
                Err(TreeError::NotCovered(_))
            ));
            let mut shuffled = all.claims.clone();
            shuffled.groups.reverse();
            assert_eq!(
                t.tree.verify_claims(&all.proof, &shuffled),
                Err(TreeError::ClaimSet(ClaimSetError::UnsortedGroups))
            );
        }

        #[test]
        fn a_wrap_states_its_childs_set_only() {
            let t = tiered();
            let d = &t.tree.design;
            // Natively: a large child handed with another set is refused, before its wrap.
            let lying = Aggregate {
                proof: t.pair.proof.clone(),
                claims: t.firsts[0].claims.clone(),
            };
            assert_eq!(
                t.tree.aggregate(&[&t.firsts[2], &lying], None),
                Err(TreeError::ChildClaims { index: 1 })
            );
            // A large proof is no child of a node's rows, which verify small ones.
            let honest = [t.pair.proof.statement(d.statement)];
            assert_eq!(
                (t.tree.child_witnesses(SMALL, &[&t.pair.proof], &honest)).err(),
                Some(TreeError::Circuit(t.pair.proof.circuit))
            );

            // In rows: the wrap's child stating another digest than its proof's does not verify.
            let position = d.place(SMALL, Level::Wrap).expect("a wrap");
            let items = (t.tree.child_witnesses(LARGE, &[&t.pair.proof], &honest)).expect("an honest child");
            let mut words = t.pair.proof.words.clone();
            let digest = d.statement.range(Section::Digest).start;
            words[digest] = F192::new(words[digest].c0 ^ 1, words[digest].c1, words[digest].c2);
            let forged = TreeStatement::new(d.statement, words);
            let items = [ChildWitness {
                statement: &forged,
                proof: &t.pair.proof.proof,
                openings: items[0].openings.clone(),
                columns: items[0].columns,
            }];
            let inputs = NodeInputs::Prove {
                items: &items,
                tables: &t.tree.tables,
                union: None,
            };
            let wrapped = t.tree.prove_rows(d.node_rows(&inputs, position));
            assert!(matches!(wrapped, Err(TreeError::Unsatisfied(_))), "{wrapped:?}");
        }

        #[test]
        fn a_tiered_first_level_and_union_stay_within_their_capacities() {
            let t = tiered();
            // The first level is the small tier's: a leaf of five claims is past it.
            let five = set(vec![group(1, 1, &[0, 1, 2, 3, 4])]);
            let (proof, output) = leaf_proof(&five);
            assert_eq!(
                t.tree
                    .aggregate_leaves(&[ClaimLeaf::new(Leaf::new(&proof, output), &five)], None),
                Err(TreeError::Capacity)
            );
            // And the large tier's capacity bounds every union.
            let four = set(vec![group(3, 1, &[0, 1, 2, 3])]);
            let (proof, output) = leaf_proof(&four);
            let first = (t
                .tree
                .aggregate_leaves(&[ClaimLeaf::new(Leaf::new(&proof, output), &four)], None))
            .expect("a set within the small tier");
            // A lone child whose set is past the small tier's (a large proof, wrapped) is taken by the large node, the rest of
            // its places absent.
            let lone = (t.tree.aggregate(&[&t.pair], None)).expect("a lone child");
            assert!(is_large(&t.tree, &lone.proof));
            assert_eq!(lone.claims, t.pair.claims);
            (t.tree)
                .verify_claims(&lone.proof, &lone.claims)
                .expect("a large root of one child");
            let big = (t.tree.aggregate(&[&first, &t.pair], None)).expect("nine claims within the tree's capacity");
            assert!(is_large(&t.tree, &big.proof));
            assert_eq!(t.tree.aggregate(&[&big, &t.firsts[2]], None), Err(TreeError::Capacity));
        }

        #[test]
        fn tiered_aggregates_from_different_provers_combine() {
            let (t, f) = (tiered(), fixture());
            let theirs = tiered_tree();
            let (proof, output) = &f.leaves[2];
            let third = (theirs.aggregate_leaves(&[ClaimLeaf::new(Leaf::new(proof, *output), &f.sets[2])], None))
                .expect("an honest leaf");
            let both = (theirs.aggregate(&[&third, &t.pair], None)).expect("our large proof is theirs");
            let received = Aggregate {
                proof: TreeProof::from_bytes(&both.proof.to_bytes()).expect("a tree proof"),
                claims: ClaimSet::from_bytes(&both.claims.to_bytes()).expect("a set"),
            };
            let again = (t.tree.aggregate(&[&received, &t.firsts[0]], None)).expect("their large proof is ours");
            theirs
                .verify_claims(&again.proof, &again.claims)
                .expect("our root is theirs");
            // A one-tier tree of the same capacity is another tree.
            assert!(matches!(
                f.tree.verify_claims(&t.pair.proof, &t.pair.claims),
                Err(TreeError::Root(_) | TreeError::Circuit(_))
            ));
        }

        #[test]
        fn a_small_tier_past_the_trees_is_refused() {
            let leaf = || LeafShape::of(&fixture().leaves[0].0).expect("a canonical announcement");
            let refused = [
                Tier { arity: 1, ..SMALL_TIER },
                Tier { arity: 4, ..SMALL_TIER },
                Tier {
                    capacity: Capacity { claims: 13, groups: 2 },
                    ..SMALL_TIER
                },
                Tier {
                    capacity: Capacity { claims: 5, groups: 5 },
                    ..SMALL_TIER
                },
            ];
            for small in refused {
                let claims = ClaimShape {
                    capacity: CAPACITY,
                    small: Some(small),
                };
                assert_eq!(
                    Tree::new(runs(leaf()), shape(Some(claims))).err(),
                    Some(TreeError::SmallTier {
                        arity: small.arity,
                        capacity: small.capacity
                    })
                );
            }
        }

        #[test]
        fn trees_of_another_small_tier_refuse_each_others_proofs() {
            let t = tiered();
            let leaf = LeafShape::of(&fixture().leaves[0].0).expect("a canonical announcement");
            let others = [
                Tier { arity: 3, ..SMALL_TIER },
                Tier {
                    capacity: Capacity { claims: 6, groups: 2 },
                    ..SMALL_TIER
                },
            ];
            for small in others {
                let claims = ClaimShape {
                    capacity: CAPACITY,
                    small: Some(small),
                };
                let other = Tree::new(runs(leaf), shape(Some(claims))).expect("a tree of two tiers");
                assert_ne!(other.design.session(), t.tree.design.session(), "{small:?}");
                for ours in [&t.firsts[0], &t.pair] {
                    assert!(
                        matches!(
                            other.verify_claims(&ours.proof, &ours.claims),
                            Err(TreeError::Root(_) | TreeError::Circuit(_))
                        ),
                        "{small:?}"
                    );
                    assert!(
                        matches!(
                            other.aggregate(&[ours, &t.firsts[1]], None),
                            Err(TreeError::Child { index: 0, .. } | TreeError::Circuit(_))
                        ),
                        "{small:?}"
                    );
                }
            }
        }

        /// The rows of the circuit at `position` over `proofs`, the first stating `kind` rather than its own, and `sets` the
        /// union's children's sets: refused by the rows holding the first child's kind to its tier's.
        fn kind_refused(t: &Tiered, position: usize, proofs: &[&TreeProof], sets: &[&ClaimSet], kind: usize) {
            let d = &t.tree.design;
            let tier = if d.places[position].level == Level::Wrap {
                LARGE
            } else {
                SMALL
            };
            let statements: Vec<TreeStatement> = (proofs.iter()).map(|p| p.statement(d.statement)).collect();
            let honest = (t.tree.child_witnesses(tier, proofs, &statements)).expect("honest children");
            let mut words = proofs[0].words.clone();
            words[d.statement.range(Section::Kind).start] = F192::new(kind as u64, 0, 0);
            let forged = TreeStatement::new(d.statement, words);
            let items: Vec<ChildWitness<'_>> = (honest.iter().enumerate())
                .map(|(i, w)| ChildWitness {
                    statement: if i == 0 { &forged } else { w.statement },
                    proof: w.proof,
                    openings: w.openings.clone(),
                    columns: w.columns,
                })
                .collect();
            let union = (!sets.is_empty()).then(|| t.tree.fill(position, sets, None).expect("honest sets").0);
            let inputs = NodeInputs::Prove {
                items: &items,
                tables: &t.tree.tables,
                union: union.as_ref(),
            };
            let rows = t.tree.prove_rows(d.node_rows(&inputs, position));
            assert!(
                matches!(&rows, Err(TreeError::Unsatisfied(check)) if check.scope().iter().any(|s| s == "child 0 kind")),
                "{:?} over kind {kind}: {rows:?}",
                d.places[position]
            );
        }

        #[test]
        fn a_child_of_the_other_tiers_kind_is_refused_in_rows() {
            let t = tiered();
            let d = &t.tree.design;
            let small = d.place(SMALL, Level::Node(2)).expect("a small node");
            let large = d.place(LARGE, Level::Node(3)).expect("the large node");
            let wrap = d.place(SMALL, Level::Wrap).expect("a wrap");
            let (first, other) = (&t.firsts[2], &t.firsts[0]);
            // A small proof stating the large node's kind, under a small node and under the large node.
            kind_refused(
                t,
                small,
                &[&first.proof, &first.proof],
                &[&first.claims, &first.claims],
                d.code(large),
            );
            kind_refused(
                t,
                large,
                &[&first.proof, &other.proof, &first.proof],
                &[&first.claims, &other.claims],
                d.code(large),
            );
            // A large proof stating a small kind under a wrap.
            for kind in [0, small, wrap] {
                kind_refused(t, wrap, &[&t.pair.proof], &[], d.code(kind));
            }
        }

        #[test]
        fn a_present_child_read_as_absent_is_refused_in_rows() {
            let t = tiered();
            let d = &t.tree.design;
            let large = d.place(LARGE, Level::Node(3)).expect("the large node");
            let proofs = [&t.firsts[0].proof, &t.firsts[1].proof, &t.firsts[0].proof];
            let statements: Vec<TreeStatement> = (proofs.iter()).map(|p| p.statement(d.statement)).collect();
            let items = (t.tree.child_witnesses(SMALL, &proofs, &statements)).expect("honest children");
            let (fill, _) = (t.tree)
                .fill(large, &[&t.firsts[0].claims, &t.firsts[1].claims], None)
                .expect("the pair's union");
            // The second child's run left as it was, its set read as the empty set's.
            let dropped = absent_at(fill, 1);
            let inputs = NodeInputs::Prove {
                items: &items,
                tables: &t.tree.tables,
                union: Some(&dropped),
            };
            let forged = t.tree.prove_rows(d.node_rows(&inputs, large));
            assert!(
                matches!(&forged, Err(TreeError::Unsatisfied(check)) if check.scope().iter().any(|s| s == "children's pool")),
                "{forged:?}"
            );
        }

        // A fake circuit at the large tier's heights stating a set no leaf published, under an honest wrap's rows: the rows
        // hold over a forged wide polynomial, and only the root's settlement of the large tier's fixed polynomial refuses it.
        #[test]
        fn a_fake_large_circuit_under_a_wrap_is_refused_at_the_root() {
            let t = tiered();
            let d = &t.tree.design;
            let large = d.place(LARGE, Level::Node(3)).expect("the large node");
            let wrap = d.place(SMALL, Level::Wrap).expect("a wrap");
            let taus = d.tiers[LARGE].taus;
            let forged_set = set(vec![group(7, 7, &[1, 2, 3])]);
            let digest = forged_set.digest();
            let halves = [F192::new(digest[0], digest[1], 0), F192::new(digest[2], digest[3], 0)];
            let rest = d.statement.range(Section::Digest).end;
            // The fake: the large node's kind, the forged set's digest, then an honest large proof's claims but for the wide
            // polynomial's value, which the fake's own stack decides.
            let fake = |wide_value: F192| {
                let mut b = Builder::new();
                let mut words = vec![b.e_const(F192::new(d.code(large) as u64, 0, 0))];
                words.extend(halves.map(|h| b.free_e(h)));
                let mut claims = TreeStatement::new(d.statement, t.pair.proof.words.clone());
                *claims.dense_value_mut(DensePoly::Wide) = wide_value;
                words.extend(claims.words()[rest..].iter().map(|&w| b.free_e(w)));
                for w in words {
                    b.expose(w);
                }
                let Finished {
                    mut circuit,
                    assignment,
                    failures,
                } = b.finish();
                assert!(failures.is_empty(), "{failures:?}");
                circuit.floor = taus;
                (circuit, assignment)
            };
            let columns = FixedColumns::new(&fake(F192::ZERO).0);
            let mut tables = t.tree.tables.clone();
            tables.0[DensePoly::Wide as usize] = d.tiers[LARGE].fixed.polynomial(&[&columns]);
            let point = &t.pair.proof.words[d.statement.range(Section::DensePoint)];
            let value = mle_eval_par(
                &tables.0[DensePoly::Wide as usize],
                &point[..d.vars.0[DensePoly::Wide as usize]],
            );
            let (circuit, assignment) = fake(value);
            assert_eq!(circuit.heights(), taus, "the fake has the large tier's heights");
            let circuit = CircuitKey::new(circuit).expect("the fake fits");
            let child = TreeProof::new(
                d.code(large),
                &assignment,
                circuit.prove(&assignment, &d.session(), d.rate),
                d.rate,
            );
            assert!(
                t.tree.read(&child, large).is_err(),
                "natively, the fake is no large node"
            );
            let limbs = child.limbs();
            let openings =
                (circuit.verify(&limbs, &d.session(), d.rate, &child.proof)).expect("the fake proves its own circuit");
            let statement = child.statement(d.statement);
            let items = [ChildWitness {
                statement: &statement,
                proof: &child.proof,
                openings,
                columns: &columns,
            }];
            let inputs = |tables| NodeInputs::Prove {
                items: &items,
                tables,
                union: None,
            };

            // An honest reduction over the tree's polynomials fails on the fake's hints.
            let honest = t.tree.prove_rows(d.node_rows(&inputs(&t.tree.tables), wrap));
            assert!(
                matches!(&honest, Err(TreeError::Unsatisfied(check)) if check.scope()[0] == "reduction"),
                "{honest:?}"
            );

            // Reduced over the forged polynomial, every row holds and the wrap's proof verifies, stating the forged set.
            let rows = d.node_rows(&inputs(&tables), wrap);
            let reduction = rows.claim_values().prove(&d.session(), &d.vars, &tables);
            let Finished {
                assignment, failures, ..
            } = rows.reduce(d, ProofSource::Proof(&reduction, &[]));
            assert!(failures.is_empty(), "{failures:?}");
            let root = TreeProof::new(
                d.code(wrap),
                &assignment,
                t.tree.keys[wrap].prove(&assignment, &d.session(), d.rate),
                d.rate,
            );
            t.tree.read(&root, wrap).expect("the wrap's recursion proof verifies");
            assert_eq!(
                t.tree.verify_claims(&root, &forged_set),
                Err(TreeError::Claim(FalseClaim::Dense(DensePoly::Wide)))
            );
        }

        // At a capacity of many chunks, a lone child of more than half of it is narrowed and republished: its set needs room in
        // the pool of a node of two once, its other place absent.
        #[test]
        fn a_lone_child_past_half_the_capacity_is_narrowed_and_republished() {
            let wide = Capacity { claims: 401, groups: 2 };
            let leaf = LeafShape::of(&fixture().leaves[0].0).expect("a canonical announcement");
            let tree = Tree::new(runs(leaf), shape(Some(ClaimShape::new(wide)))).expect("a tree");
            let d = &tree.design;
            let pool = (d.union_shape(d.place(SMALL, Level::Node(2)).expect("a node of two"))).expect("a union");
            let big = set(vec![group(4, 4, &(0..400).collect::<Vec<_>>())]);
            assert!(
                2 * big.items().len() > pool.children.items(),
                "twice, it does not fit the pool"
            );
            let (proof, output) = leaf_proof(&big);
            let first = (tree.aggregate_leaves(&[ClaimLeaf::new(Leaf::new(&proof, output), &big)], None))
                .expect("a set within the capacity");
            let republished = (tree.aggregate(&[&first], None)).expect("a lone child");
            assert_eq!(republished.claims, big);
            (tree.verify_claims(&republished.proof, &big)).expect("a republished root");
            let part = set(vec![group(4, 4, &(0..300).collect::<Vec<_>>())]);
            let narrowed = (tree.aggregate(&[&first], Some(&part))).expect("a covered declaration");
            (tree.verify_claims(&narrowed.proof, &part)).expect("a narrowed root");
        }

        // A claim-set tree of one tier keeps the heights and statement layout of protocol version `leanvm-tree-12`, before the
        // tiers, the absent STEP and LINK tables aside; its nodes' circuits add the absent places. Its session tag also names
        // its leaf family, so it is pinned here as it is now.
        #[test]
        fn a_claim_set_tree_of_one_tier_keeps_tree_12s_heights_and_layout() {
            let d = &fixture().tree.design;
            let sections = [
                Section::Kind,
                Section::Digest,
                Section::DensePoint,
                Section::DenseValues,
                Section::Rows,
                Section::Cols,
                Section::Matrices,
            ];
            assert_eq!(d.tiers.len(), 1);
            let heights = [Some(17), Some(17), Some(15), Some(11), Some(14), None, None, Some(10)];
            assert_eq!(d.tiers[SMALL].taus.into_values(), heights);
            assert_eq!(d.statement.len(), 99);
            assert_eq!(
                sections.map(|s| d.statement.range(s)),
                [0..1, 1..3, 3..26, 26..29, 29..43, 43..57, 57..99]
            );
            assert_eq!(
                d.session_under(b"leanvm-tree-12").0,
                [
                    154, 84, 34, 6, 227, 175, 120, 53, 34, 100, 15, 157, 66, 36, 149, 151, 175, 236, 58, 53, 72, 185,
                    96, 134, 27, 250, 102, 1, 254, 237, 123, 51
                ]
            );
        }
    }
}
