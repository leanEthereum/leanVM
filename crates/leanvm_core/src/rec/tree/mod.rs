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

use crate::cpu::{CpuError, Lookup, Program, Proof};
use crate::pcs::Rate;
use crate::rec::RecError;
use crate::rec::circuit::{Circuit, Finished};
use crate::rec::fixed::FixedColumns;
use crate::rec::layout::RecLayout;
use crate::rec::table::Table;
use crate::rec::transcript::ProofSource;
use crate::rec::verifier::ProofShape;
use crate::tables::{ClassSpec, N_TABLES, Part};
use design::{ChildWitness, Design, LeafWitness, NodeRows, Witness};
use fiat_shamir::transcript::RawProof;
use primitives::field::{F64, F192};
use primitives::multilinear::{eq_table, mle_eval_par};
use reduce::DenseTables;
use statement::TreeStatement;
use thiserror::Error;

mod claims;
mod design;
mod fixed;
mod reduce;
mod statement;
#[cfg(test)]
mod tests;

pub use claims::DensePoly;
pub use statement::Kind;

/// The most rounds the search for the nodes' heights takes: each round at least doubles a table.
const MAX_ROUNDS: usize = 8;

/// The shape of a tree's leaves: each table's height and the rate, as a RISC-V proof announces them.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct LeafShape {
    /// Each table's base-two logarithm of rows.
    taus: [usize; N_TABLES],
    /// The commitment's rate.
    rate: Rate,
}

/// A leaf of a tree: a RISC-V proof, and the output it proves.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Leaf<'a> {
    /// The proof.
    proof: &'a Proof,
    /// `a0..a3` at the run's exit.
    output: [u64; 4],
}

/// A tree's verifying key and its prover's tables: its two circuits, their fixed columns, and the dense polynomials.
pub struct Tree<'p> {
    /// What fixes the circuits.
    design: Design<'p>,
    /// Each kind's circuit, the first level's first.
    circuits: [Circuit; 2],
    /// Each kind's circuit's fixed columns, the first level's first.
    columns: [FixedColumns; 2],
    /// The dense polynomials the root's claims are settled against.
    tables: DenseTables,
}

/// A recursion proof of a tree: its statement's words, its proof, and the rate it is proven at.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TreeProof {
    /// What its circuit verifies, its statement's first word.
    kind: Kind,
    /// Its statement's words.
    words: Vec<F192>,
    /// The recursion proof.
    proof: Proof,
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
        /// Which of its two circuits.
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
    LeafShape(CpuError),
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
    #[error("leaf {index} does not verify: {error}")]
    Leaf {
        /// The leaf's index among its node's.
        index: usize,
        /// Why its verifier refuses it.
        error: CpuError,
    },
    /// A child proof does not verify.
    #[error("child {index} does not verify: {error}")]
    Child {
        /// The child's index among its node's.
        index: usize,
        /// Why its verifier refuses it.
        error: RecError,
    },
    /// The circuit's rows do not hold on the prover's values: a check, named by its scope, fails.
    #[error("the circuit does not hold: {0}")]
    Unsatisfied(String),
    /// A proof at another rate than the tree's.
    #[error("a proof at log-inv-rate {got}, and the tree's is {expected}")]
    Rate {
        /// The tree's.
        expected: u8,
        /// The proof's.
        got: u8,
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
    #[error("the root does not verify: {0}")]
    Root(RecError),
    /// The root's digest is not that of the given leaves' outputs.
    #[error("the root does not state these leaf outputs")]
    Outputs,
    /// A claim the root carries is false.
    #[error("the root's claim {0} is false")]
    Claim(FalseClaim),
}

impl LeafShape {
    /// The shape of proofs with these table heights at this rate.
    pub const fn new(taus: [usize; N_TABLES], rate: Rate) -> Self {
        Self { taus, rate }
    }

    /// The shape a RISC-V proof announces, if its announcement is canonical.
    pub fn of(proof: &Proof) -> Option<Self> {
        let size = |x: &F192| (x.c1 == 0 && x.c2 == 0).then(|| usize::try_from(x.c0).ok()).flatten();
        let announced = proof.stream.get(..=N_TABLES)?;
        let mut taus = [0; N_TABLES];
        for (tau, x) in taus.iter_mut().zip(announced) {
            *tau = size(x)?;
        }
        let rate = Rate::new(u8::try_from(size(&announced[N_TABLES])?).ok()?).ok()?;
        Some(Self { taus, rate })
    }
}

impl<'a> Leaf<'a> {
    /// The leaf of this proof of this output.
    pub const fn new(proof: &'a Proof, output: [u64; 4]) -> Self {
        Self { proof, output }
    }
}

impl TreeProof {
    /// What the proof's circuit verifies.
    pub const fn kind(&self) -> Kind {
        self.kind
    }

    /// The proof's bytes: its rate, its statement's words, then the recursion proof.
    ///
    /// ```text
    /// | log_inv_rate: u8 | n_words: u32 | words: 24 bytes each | proof |
    /// ```
    pub fn to_bytes(&self) -> Vec<u8> {
        let n_words = u32::try_from(self.words.len()).expect("a statement of a few hundred words");
        let mut bytes = vec![self.rate.log_inv_rate()];
        bytes.extend(n_words.to_le_bytes());
        for w in &self.words {
            bytes.extend([w.c0, w.c1, w.c2].iter().flat_map(|l| l.to_le_bytes()));
        }
        bytes.extend(self.proof.to_bytes());
        bytes
    }

    /// The proof these bytes encode, if they encode one and nothing more.
    pub fn from_bytes(bytes: &[u8]) -> Option<Self> {
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
            proof: Proof::from_bytes(proof)?,
            rate: Rate::new(rate).ok()?,
        })
    }
}

impl<'p> Tree<'p> {
    /// The tree over proofs of a program of the given shape, a first-level node verifying `n_0` of them and a node `n` tree proofs.
    ///
    /// Every tree proof is at the given rate.
    ///
    /// The circuits are built from the shapes alone, so a verifier needs no proof to build its key.
    ///
    /// # Errors
    ///
    /// - Arities that make no tree: a first level of no leaf, or nodes of fewer than two children.
    /// - A leaf shape no proof of the program has.
    /// - Circuits that fit no commitment.
    pub fn new(
        program: &'p Program,
        leaves: LeafShape,
        arity_0: usize,
        arity: usize,
        rate: Rate,
    ) -> Result<Self, TreeError> {
        if arity_0 == 0 || arity < 2 {
            return Err(TreeError::Arity { arity_0, arity });
        }
        let leaf = || ProofShape::new(program, leaves.taus, leaves.rate).map_err(TreeError::LeafShape);
        let (design, circuits) = Self::converge(|taus| Design::new(leaf()?, arity_0, arity, rate, taus))?;
        let columns = circuits.each_ref().map(|c| FixedColumns::of(c, &design.taus));
        let fixed = design.fixed.polynomial([&columns[0], &columns[1]]);
        let rv = program.rv();
        let mut image: Vec<F64> = rv.image().iter().map(|&w| F64(w)).collect();
        image.resize(1 << design.vars.0[DensePoly::Image as usize], F64::ZERO);
        let tables = DenseTables([Lookup::Bytecode.table(rv), image, fixed]);
        Ok(Self {
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
        design: impl Fn([usize; Table::COUNT]) -> Result<Design<'p>, TreeError>,
    ) -> Result<(Design<'p>, [Circuit; 2]), TreeError> {
        let mut taus = design([0; Table::COUNT])?.shape(Kind::First).circuit.heights();
        for _ in 0..MAX_ROUNDS {
            let d = design(taus)?;
            let built = Kind::ALL.map(|kind| d.shape(kind).circuit);
            let next = std::array::from_fn(|t| built.iter().map(|c| c.heights()[t]).fold(taus[t], usize::max));
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
    pub const fn circuit(&self, kind: Kind) -> &Circuit {
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
                if LeafShape::of(proof) != Some(shape) {
                    return Err(TreeError::ForeignLeaf { index });
                }
                let raw = (program.verify_to_raw(&output, proof)).map_err(|error| TreeError::Leaf { index, error })?;
                Ok(LeafWitness { raw, output })
            })
            .collect::<Result<Vec<_>, _>>()?;
        let witness = Witness::Prove {
            items: &items,
            tables: &self.tables,
        };
        let rows = crate::stage!("Build circuit", || d.first(&witness));
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
        let raws = (children.iter().enumerate())
            .map(|(index, c)| self.read(c).map_err(|error| TreeError::Child { index, error }))
            .collect::<Result<Vec<_>, _>>()?;
        let statements: Vec<TreeStatement> = (children.iter())
            .map(|c| TreeStatement::new(d.statement, c.words.clone()))
            .collect();
        let items: Vec<ChildWitness<'_>> = (children.iter().zip(&statements).zip(raws))
            .map(|((c, statement), raw)| ChildWitness {
                statement,
                raw,
                columns: &self.columns[c.kind as usize],
            })
            .collect();
        let witness = Witness::Prove {
            items: &items,
            tables: &self.tables,
        };
        let rows = crate::stage!("Build circuit", || d.node(&witness));
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
        self.levels(leaves.len())?;
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
    pub fn verify(&self, root: &TreeProof, outputs: &[[u64; 4]]) -> Result<(), TreeError> {
        let d = &self.design;
        if root.rate != d.rate {
            return Err(TreeError::Rate {
                expected: d.rate.log_inv_rate(),
                got: root.rate.log_inv_rate(),
            });
        }
        let expected = self.levels(outputs.len())?;
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

    /// The kind of the root over this many leaves: a first-level node over `n_0`, a node over `n_0 n^d`.
    fn levels(&self, leaves: usize) -> Result<Kind, TreeError> {
        let (arity_0, arity) = (self.design.arity_0, self.design.arity);
        let count = TreeError::LeafCount { leaves, arity_0, arity };
        if leaves == 0 || !leaves.is_multiple_of(arity_0) {
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

    /// The digest the root over these leaf outputs states.
    fn digest(&self, outputs: &[[u64; 4]]) -> [u64; 4] {
        let (arity_0, arity) = (self.design.arity_0, self.design.arity);
        let mut level: Vec<[u64; 4]> = outputs.chunks(arity_0).map(|o| Kind::First.digest(o)).collect();
        while level.len() > 1 {
            level = level.chunks(arity).map(|c| Kind::Node.digest(c)).collect();
        }
        level[0]
    }

    /// Verify a tree proof's recursion proof, short of its claims, returning it as its verifier read it.
    fn read(&self, p: &TreeProof) -> Result<RawProof, RecError> {
        let limbs: Vec<[u64; 4]> = p.words.iter().map(|w| [w.c0, w.c1, w.c2, 0]).collect();
        self.circuit(p.kind)
            .verify_to_raw(&limbs, self.design.iv, self.design.rate, &p.proof)
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
        } = crate::stage!("Reduce in rows", || rows.reduce(d, ProofSource::Proof(&raw)));
        if let Some(first) = failures.into_iter().next() {
            return Err(TreeError::Unsatisfied(first));
        }
        let proof = (self.circuit(kind))
            .prove(&assignment, d.iv, d.rate)
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
        let held = parallel::map_collect(crate::class_flock::N_FLOCKS, |f| {
            let circuit = crate::class_flock::circuit(f);
            let k = circuit.k_log();
            let (ra, rb) = circuit.row_values(&eq_table(&s.cols()[..k]));
            let u = eq_table(&s.rows()[..k]);
            let dot = |r: &[F192]| u.iter().zip(r).fold(F192::ZERO, |acc, (&x, &y)| acc + x * y);
            [dot(&ra), dot(&rb)] == s.matrices(f)
        });
        held.iter().position(|&h| !h).map_or(Ok(()), |f| {
            let (t, part) = crate::class_flock::flock(f);
            Err(TreeError::Claim(FalseClaim::Matrix {
                table: ClassSpec::ALL[t].name,
                part,
            }))
        })
    }
}
