//! leanVM: a minimal zkVM for RISC-V (rv64im).
//!
//! A program is a guest's ELF executable (see `programs/`) or a text written by hand with the assembler.
//! A prover runs it and proves the run; the verifier checks the proof against the program and the output the run claims, `a0..a3` when it called `exit`.
//!
//! A run also takes its advice, the words the program finds at the advice base.
//!
//! The statement says nothing about them beyond how many the program's region holds.
//!
//! So a proof shows that some advice makes the program exit with the output: what a program reads there it has to check itself.
//!
//! End to end in [`crates/leanvm/tests/api.rs`](https://github.com/leanEthereum/leanVM/blob/main/crates/leanvm/tests/api.rs).

use aggregate::{TreeError, TreeProof};
use leanvm_core::cpu::{CpuError, Proof as TranscriptProof, ProveError};
use std::fmt::{Debug, Formatter, Result as FmtResult};
use thiserror::Error;

pub use leanvm_core::{
    cpu::{Program, Stats},
    pcs::{InvalidRate, Rate},
    rv::{ElfError, ProgramError, Region, RiscvProgram, Trap, asm},
};

/// The process's proving setup: the worker pool and, unless declined, the proving arena.
///
/// The arena is one per process, so one proof runs at a time in a process: prove in parallel from separate processes.
/// Once a process has engaged the arena, it stays engaged.
#[derive(Debug)]
pub struct Prover(());

impl Prover {
    /// A prover with the arena, which recycles the prover's buffers across proofs.
    #[must_use]
    pub fn new() -> Self {
        leanvm_core::init_prover();
        Self(())
    }

    /// A prover on the system allocator, for a host whose memory the arena's peak does not fit.
    #[must_use]
    pub fn without_arena() -> Self {
        leanvm_core::init_prover_pool();
        Self(())
    }

    /// Run the program on `advice`, the advice region's first words, and prove the run.
    ///
    /// # Errors
    ///
    /// The run's trap, a run longer than one proof holds, or more advice than the program's region holds.
    pub fn prove(&self, program: &Program, advice: &[u64], rate: Rate) -> Result<Proved, LeanVmError> {
        let (proof, output, stats) = program.prove(advice, rate)?;
        Ok(Proved {
            proof: Proof(proof),
            output,
            stats,
        })
    }
}

impl Default for Prover {
    fn default() -> Self {
        Self::new()
    }
}

/// What proving a run gives: the proof, the output it proves, and what the run cost.
#[derive(Clone, Debug)]
#[non_exhaustive]
pub struct Proved {
    /// The proof of the run.
    pub proof: Proof,
    /// `a0..a3` at the run's `exit`.
    pub output: [u64; 4],
    /// What the run cost: its cycles, its table heights and its committed words.
    pub stats: Stats,
}

/// What a proof of this run would cost, without proving it: one execution.
///
/// # Errors
///
/// What would refuse the proof itself.
pub fn measure(program: &Program, advice: &[u64]) -> Result<Stats, LeanVmError> {
    Ok(program.measure(advice)?)
}

/// Check that the program, run on some advice, exits with `output`.
///
/// # Errors
///
/// The proof does not verify against this program and this output.
pub fn verify(program: &Program, output: &[u64; 4], proof: &Proof) -> Result<(), LeanVmError> {
    Ok(program.verify(output, &proof.0).map_err(LeanVmVerifyError)?)
}

/// A proof of a run.
///
/// Its bytes start with a magic and the protocol's version, so a proof of another protocol is refused rather than misread.
///
/// ```text
/// | "LVMP" | version: u16, little-endian | body |
/// ```
#[derive(Clone, PartialEq, Eq)]
pub struct Proof(TranscriptProof);

impl Debug for Proof {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        f.debug_struct("Proof").finish_non_exhaustive()
    }
}

impl Proof {
    const MAGIC: [u8; 4] = *b"LVMP";

    /// The protocol version, bumped by every change to what a proof says.
    const VERSION: u16 = 6;

    /// The proof's bytes.
    #[must_use]
    pub fn to_bytes(&self) -> Vec<u8> {
        [&Self::MAGIC[..], &Self::VERSION.to_le_bytes(), &self.0.to_bytes()].concat()
    }

    /// The proof these bytes encode.
    ///
    /// # Errors
    ///
    /// Bytes that are no proof, or a proof of another protocol version.
    pub fn from_bytes(bytes: &[u8]) -> Result<Self, LeanVmError> {
        let (magic, rest) = bytes.split_first_chunk::<4>().ok_or(LeanVmError::MalformedProof)?;
        let (version, body) = rest.split_first_chunk::<2>().ok_or(LeanVmError::MalformedProof)?;
        if *magic != Self::MAGIC {
            return Err(LeanVmError::MalformedProof);
        }
        let version = u16::from_le_bytes(*version);
        if version != Self::VERSION {
            return Err(LeanVmError::UnsupportedVersion { found: version });
        }
        TranscriptProof::from_bytes(body)
            .map(Self)
            .ok_or(LeanVmError::MalformedProof)
    }
}

/// Everything that can go wrong in loading, proving or verifying.
#[derive(Clone, Debug, PartialEq, Eq, Error)]
#[non_exhaustive]
pub enum LeanVmError {
    /// The file is not a guest.
    #[error(transparent)]
    Elf(#[from] ElfError),
    /// The text and RAM form no program.
    #[error(transparent)]
    Program(#[from] ProgramError),
    /// The run trapped, so it has no proof.
    #[error("the run traps: {0}")]
    Trap(Trap),
    /// The run is longer than one proof holds.
    #[error("the run is longer than one proof holds")]
    TooLong,
    /// More advice words than the program's region holds.
    #[error("the advice has {got} words, and the program's region holds {max}")]
    AdviceTooLong { max: usize, got: usize },
    /// A rate the commitment does not support.
    #[error(transparent)]
    InvalidRate(#[from] InvalidRate),
    /// Bytes that are no proof.
    #[error("the bytes are no proof")]
    MalformedProof,
    /// A proof of another protocol version.
    #[error(
        "a proof of protocol version {found}, and this verifier reads version {}",
        Proof::VERSION
    )]
    UnsupportedVersion { found: u16 },
    /// The proof does not verify.
    #[error(transparent)]
    Verify(#[from] LeanVmVerifyError),
    /// A tree proof of another protocol version.
    #[error(
        "a tree proof of protocol version {found}, and this verifier reads version {}",
        TreeProof::VERSION
    )]
    UnsupportedTreeVersion { found: u16 },
    /// An aggregation tree cannot be built, a tree proof cannot be made, or a root is refused.
    #[error(transparent)]
    Tree(#[from] TreeError),
}

impl From<ProveError> for LeanVmError {
    fn from(error: ProveError) -> Self {
        match error {
            ProveError::Trap(trap) => Self::Trap(trap),
            ProveError::TooLong => Self::TooLong,
            ProveError::AdviceTooLong { max, got } => Self::AdviceTooLong { max, got },
        }
    }
}

/// Why a proof does not verify: which stage of the verifier refused it.
#[derive(Clone, Debug, PartialEq, Eq, Error)]
#[error("the proof does not verify: {0}")]
pub struct LeanVmVerifyError(CpuError);

/// Aggregation trees: many proofs of one program, verified as one.
///
/// ```text
///                 node                  verifies `arity` tree proofs of either kind
///               /      \
///        first-level   first-level      each verifies `arity_0` proofs of the program
///          /  \          /  \
///       leaf  leaf    leaf  leaf
/// ```
///
/// Every tree proof states the same few hundred words: a digest of its leaves' outputs, and claims only the root's verifier evaluates.
/// A tree over one leaf, `arity_0` one, is a single proof's recursion.
pub mod aggregate {
    use super::{LeanVmError, Program, Proof, Proved, Rate};
    use leanvm_core::rec::table::Table;
    use leanvm_core::rec::tree::{
        Leaf as CoreLeaf, LeafShape as CoreLeafShape, Tree as CoreTree, TreeProof as CoreTreeProof,
    };
    use std::fmt::{Debug, Formatter, Result as FmtResult};

    pub use leanvm_core::rec::tree::{DensePoly, FalseClaim, Kind, TreeError};

    /// The shape of a tree's leaves: each table's height and the commitment's rate, as a proof announces them.
    #[derive(Clone, Copy, Debug, PartialEq, Eq)]
    pub struct LeafShape(CoreLeafShape);

    /// A leaf of a tree: a proof, and the output it proves.
    #[derive(Clone, Copy, Debug)]
    pub struct Leaf<'a> {
        /// The proof.
        proof: &'a Proof,
        /// `a0..a3` at the run's exit.
        output: [u64; 4],
    }

    /// A tree's verifying key, and what its prover needs: built from the program and the shapes alone.
    pub struct Tree<'p>(CoreTree<'p>);

    /// A proof of a tree: a first-level node's or a node's, the root's included.
    ///
    /// Its bytes start with a magic and the protocol's version.
    ///
    /// ```text
    /// | "LVMT" | version: u16, little-endian | body |
    /// ```
    #[derive(Clone, PartialEq, Eq)]
    pub struct TreeProof(CoreTreeProof);

    /// What one of a tree's circuits costs: each table's rows, and the words a proof commits.
    #[derive(Clone, Debug, PartialEq, Eq)]
    #[non_exhaustive]
    pub struct CircuitStats {
        /// Each table of the recursion machine, in order.
        pub tables: Vec<TableStats>,
        /// The words a proof commits.
        pub committed: usize,
    }

    /// One table of a tree's circuit: its rows, and the height they are padded to.
    #[derive(Clone, Copy, Debug, PartialEq, Eq)]
    #[non_exhaustive]
    pub struct TableStats {
        /// The table's name.
        pub name: &'static str,
        /// The rows the circuit puts in it.
        pub rows: usize,
        /// The base-two logarithm of its height, a power of two at least its rows.
        pub height_log: usize,
    }

    impl LeafShape {
        /// The shape `proof` announces.
        ///
        /// # Errors
        ///
        /// A proof whose announcement is malformed.
        pub fn of(proof: &Proof) -> Result<Self, LeanVmError> {
            CoreLeafShape::of(&proof.0).map(Self).ok_or(LeanVmError::MalformedProof)
        }
    }

    impl<'a> Leaf<'a> {
        /// The leaf of this proof of this output.
        #[must_use]
        pub const fn new(proof: &'a Proof, output: [u64; 4]) -> Self {
            Self { proof, output }
        }

        /// The leaf as the tree's core takes it.
        const fn inner(self) -> CoreLeaf<'a> {
            CoreLeaf::new(&self.proof.0, self.output)
        }
    }

    impl<'a> From<&'a Proved> for Leaf<'a> {
        fn from(proved: &'a Proved) -> Self {
            Self::new(&proved.proof, proved.output)
        }
    }

    impl<'p> Tree<'p> {
        /// The tree over proofs of `program` shaped `leaves`: each first-level node verifies `arity_0` of them, each node `arity` tree proofs, every tree proof at `rate`.
        ///
        /// # Errors
        ///
        /// A first-level arity of zero, a node arity below two, a shape no proof of the program has, or circuits too large to prove.
        pub fn new(
            program: &'p Program,
            leaves: LeafShape,
            arity_0: usize,
            arity: usize,
            rate: Rate,
        ) -> Result<Self, LeanVmError> {
            Ok(Self(CoreTree::new(program, leaves.0, arity_0, arity, rate)?))
        }

        /// Prove a first-level node over `arity_0` leaves, each a proof and its output, in order.
        ///
        /// # Errors
        ///
        /// The wrong number of leaves, a leaf of another shape, or one that does not verify.
        pub fn prove_first(&self, leaves: &[Leaf<'_>]) -> Result<TreeProof, LeanVmError> {
            let leaves: Vec<_> = leaves.iter().map(|l| l.inner()).collect();
            Ok(TreeProof(self.0.prove_first(&leaves)?))
        }

        /// Prove a node over `arity` tree proofs, in order.
        ///
        /// # Errors
        ///
        /// The wrong number of children, or one that does not verify.
        pub fn prove_node(&self, children: &[TreeProof]) -> Result<TreeProof, LeanVmError> {
            let children: Vec<_> = children.iter().map(|c| c.0.clone()).collect();
            Ok(TreeProof(self.0.prove_node(&children)?))
        }

        /// Prove the whole tree over `leaves`, each a proof and its output, in order.
        ///
        /// # Errors
        ///
        /// A number of leaves that is not `arity_0` times a power of `arity`, or a leaf the first level refuses.
        pub fn prove(&self, leaves: &[Leaf<'_>]) -> Result<TreeProof, LeanVmError> {
            let leaves: Vec<_> = leaves.iter().map(|l| l.inner()).collect();
            Ok(TreeProof(self.0.prove(&leaves)?))
        }

        /// Check that `root` proves that every leaf of a tree verifies and outputs `outputs`, in order.
        ///
        /// # Errors
        ///
        /// The first check that refuses: the root's kind or rate, its proof, its digest of the outputs, or a claim it carries.
        pub fn verify(&self, root: &TreeProof, outputs: &[[u64; 4]]) -> Result<(), LeanVmError> {
            Ok(self.0.verify(&root.0, outputs)?)
        }

        /// What the circuit of a proof of this kind costs.
        pub fn stats(&self, kind: Kind) -> CircuitStats {
            let circuit = self.0.circuit(kind);
            let (rows, heights) = (circuit.row_counts(), circuit.heights());
            CircuitStats {
                tables: (Table::ALL.iter())
                    .map(|&t| TableStats {
                        name: t.name(),
                        rows: rows[t as usize],
                        height_log: heights[t as usize],
                    })
                    .collect(),
                committed: circuit.committed_words().expect("a tree's circuits fit one commitment"),
            }
        }
    }

    impl Debug for TreeProof {
        fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
            f.debug_struct("TreeProof")
                .field("kind", &self.kind())
                .finish_non_exhaustive()
        }
    }

    impl TreeProof {
        const MAGIC: [u8; 4] = *b"LVMT";

        /// The tree protocol's version, bumped by every change to what a tree proof says.
        pub(super) const VERSION: u16 = 1;

        /// What the proof's circuit verifies.
        #[must_use]
        pub const fn kind(&self) -> Kind {
            self.0.kind()
        }

        /// The proof's bytes.
        #[must_use]
        pub fn to_bytes(&self) -> Vec<u8> {
            [&Self::MAGIC[..], &Self::VERSION.to_le_bytes(), &self.0.to_bytes()].concat()
        }

        /// The proof these bytes encode.
        ///
        /// # Errors
        ///
        /// Bytes that are no tree proof, or a tree proof of another protocol version.
        pub fn from_bytes(bytes: &[u8]) -> Result<Self, LeanVmError> {
            let (magic, rest) = bytes.split_first_chunk::<4>().ok_or(LeanVmError::MalformedProof)?;
            let (version, body) = rest.split_first_chunk::<2>().ok_or(LeanVmError::MalformedProof)?;
            if *magic != Self::MAGIC {
                return Err(LeanVmError::MalformedProof);
            }
            let version = u16::from_le_bytes(*version);
            if version != Self::VERSION {
                return Err(LeanVmError::UnsupportedTreeVersion { found: version });
            }
            CoreTreeProof::from_bytes(body)
                .map(Self)
                .ok_or(LeanVmError::MalformedProof)
        }
    }
}
