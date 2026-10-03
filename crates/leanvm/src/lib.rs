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

use std::fmt;

use leanvm_core::cpu::{self, CpuError, ProveError};

pub use leanvm_core::{
    cpu::{Program, Stats},
    pcs::{InvalidRate, Rate},
    rv::{ElfError, ProgramError, Region, Trap, asm},
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
    pub fn prove(&self, program: &Program, advice: &[u64], rate: Rate) -> Result<Proved, Error> {
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
pub fn measure(program: &Program, advice: &[u64]) -> Result<Stats, Error> {
    Ok(program.measure(advice)?)
}

/// Check that the program, run on some advice, exits with `output`.
///
/// # Errors
///
/// The proof does not verify against this program and this output.
pub fn verify(program: &Program, output: &[u64; 4], proof: &Proof) -> Result<(), Error> {
    Ok(program.verify(output, &proof.0).map_err(VerifyError)?)
}

/// A proof of a run.
///
/// Its bytes start with a magic and the protocol's version, so a proof of another protocol is refused rather than misread.
///
/// ```text
/// | "LVMP" | version: u16, little-endian | body |
/// ```
#[derive(Clone, PartialEq, Eq)]
pub struct Proof(cpu::Proof);

impl fmt::Debug for Proof {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("Proof").finish_non_exhaustive()
    }
}

impl Proof {
    const MAGIC: [u8; 4] = *b"LVMP";

    /// The protocol version, bumped by every change to what a proof says.
    const VERSION: u16 = 5;

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
    pub fn from_bytes(bytes: &[u8]) -> Result<Self, Error> {
        let (magic, rest) = bytes.split_first_chunk::<4>().ok_or(Error::MalformedProof)?;
        let (version, body) = rest.split_first_chunk::<2>().ok_or(Error::MalformedProof)?;
        if *magic != Self::MAGIC {
            return Err(Error::MalformedProof);
        }
        let version = u16::from_le_bytes(*version);
        if version != Self::VERSION {
            return Err(Error::UnsupportedVersion { found: version });
        }
        cpu::Proof::from_bytes(body).map(Self).ok_or(Error::MalformedProof)
    }
}

/// Everything that can go wrong in loading, proving or verifying.
#[derive(Clone, Debug, PartialEq, Eq, thiserror::Error)]
#[non_exhaustive]
pub enum Error {
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
    Verify(#[from] VerifyError),
    /// Recursion refused: an inner proof does not verify, or the outer proof does not.
    #[error(transparent)]
    Recursion(#[from] recursion::RecursionError),
    /// Aggregation refused: a leaf or a child does not verify, or the root does not.
    #[error(transparent)]
    Aggregate(#[from] aggregate::TreeError),
}

impl From<ProveError> for Error {
    fn from(error: ProveError) -> Self {
        match error {
            ProveError::Trap(trap) => Self::Trap(trap),
            ProveError::TooLong => Self::TooLong,
            ProveError::AdviceTooLong { max, got } => Self::AdviceTooLong { max, got },
        }
    }
}

/// Why a proof does not verify: which stage of the verifier refused it.
#[derive(Clone, Debug, PartialEq, Eq, thiserror::Error)]
#[error("the proof does not verify: {0}")]
pub struct VerifyError(CpuError);

/// One proof that leanVM proofs verify: a recursion machine runs the verifier's core on each inner proof as a
/// fixed list of rows, and its statement is each inner proof's output, shape and deferred claims, which
/// [`recursion::verify`] settles against the programs after the outer proof.
pub mod recursion {
    use super::{Error, Program, Proof, Prover, Rate};
    use leanvm_core::rec::{self, InnerProof, circuit::N_TABLES};
    pub use leanvm_core::rec::{InnerStatement, RecursionError, RecursionProof};

    /// A proof to recurse on: its program, the proof, and the output it proves.
    #[derive(Clone, Copy)]
    pub struct Inner<'a> {
        pub program: &'a Program,
        pub proof: &'a Proof,
        pub output: [u64; 4],
    }

    /// The recursion circuit's size: each table's rows and height, and the committed words.
    #[derive(Clone, Debug, PartialEq, Eq)]
    #[non_exhaustive]
    pub struct CircuitStats {
        pub rows: [usize; N_TABLES],
        pub log_rows: [usize; N_TABLES],
        pub committed: usize,
    }

    /// Prove that every inner proof verifies, the outer proof at `rate`.
    ///
    /// # Errors
    ///
    /// An inner proof that does not verify.
    pub fn prove(_prover: &Prover, inners: &[Inner], rate: Rate) -> Result<RecursionProof, Error> {
        let inners = inners
            .iter()
            .map(|i| InnerProof::new(i.program, &i.proof.0, i.output).map_err(super::VerifyError))
            .collect::<Result<Vec<_>, _>>()?;
        Ok(rec::prove(&inners, rate)?)
    }

    /// Check that proofs of `programs` verify to the outputs `proof` states, the outer proof at `rate`.
    ///
    /// # Errors
    ///
    /// The first check that refuses.
    pub fn verify(programs: &[&Program], proof: &RecursionProof, rate: Rate) -> Result<(), Error> {
        Ok(rec::verify(programs, proof, rate.log_inv_rate().into())?)
    }

    /// The size of the circuit verifying proofs of these programs and shapes.
    ///
    /// # Errors
    ///
    /// A shape no proof can have.
    pub fn stats(programs: &[&Program], inners: &[InnerStatement]) -> Result<CircuitStats, Error> {
        let circuit = rec::circuit_for(programs, inners)?;
        Ok(CircuitStats {
            rows: circuit.row_counts(),
            log_rows: rec::proof::Layout::new(&circuit).taus,
            committed: rec::proof::committed_words(&circuit),
        })
    }
}

/// Aggregation trees: leanVM proofs of one program at the leaves, a lift node verifying each in a recursion proof,
/// a first level of nodes each verifying `arity` lifts, and nodes above it each verifying `arity` nodes with one
/// circuit, up to a root [`aggregate::Tree::verify`] checks against the leaves' outputs. Every proof of a tree
/// carries constant-size claims on the program and the circuits, which each node reduces and only the root's
/// verifier evaluates.
pub mod aggregate {
    use super::{Error, Program, Proof, Prover, Rate, VerifyError};
    pub use leanvm_core::rec::tree::{Kind, TreeError, TreeProof, TreeStatement, tree_digest};
    use leanvm_core::rec::{self, InnerProof, tree};

    /// A tree's circuits and what its prover and verifier need: fixed by the leaves' program and shape, the arity
    /// and the rate.
    pub struct Tree<'p>(tree::Tree<'p>);

    /// A tree proof's circuit: each table's rows, and the words its proof commits.
    #[derive(Clone, Debug, PartialEq, Eq)]
    #[non_exhaustive]
    pub struct CircuitStats {
        pub rows: [usize; rec::circuit::N_TABLES],
        pub log_rows: [usize; rec::circuit::N_TABLES],
        pub committed: usize,
    }

    impl<'p> Tree<'p> {
        /// The tree over proofs of `program` shaped like `leaf`, each node verifying `arity` children, every
        /// recursion proof at `rate`.
        ///
        /// # Errors
        ///
        /// A leaf shape no proof of `program` can have, or a zero arity.
        pub fn new(program: &'p Program, leaf: &Proof, arity: usize, rate: Rate) -> Result<Self, Error> {
            let (taus, log_inv_rate) = rec::announced_shape(&leaf.0.stream).ok_or(TreeError::Shape)?;
            Ok(Self(tree::Tree::new(program, taus, log_inv_rate, arity, rate)?))
        }

        fn inner(&self, proof: &Proof, output: [u64; 4]) -> Result<InnerProof<'p>, Error> {
            Ok(InnerProof::new(self.0.program(), &proof.0, output).map_err(VerifyError)?)
        }

        /// Prove a lift node over one leaf.
        ///
        /// # Errors
        ///
        /// A leaf of another shape, or one that does not verify.
        pub fn prove_lift(&self, _prover: &Prover, leaf: &Proof, output: [u64; 4]) -> Result<TreeProof, Error> {
            Ok(self.0.prove_lift(&self.inner(leaf, output)?)?)
        }

        /// Prove a node over `arity` children, in order: lifts, or nodes of either kind.
        ///
        /// # Errors
        ///
        /// The wrong number of children, children of two levels, or a child that does not verify.
        pub fn prove_node(&self, _prover: &Prover, children: &[TreeProof]) -> Result<TreeProof, Error> {
            Ok(self.0.prove_node(children)?)
        }

        /// Prove the whole tree over `leaves`, each a proof and its output, in order.
        ///
        /// # Errors
        ///
        /// Leaves that are no power of the arity, or a leaf that does not verify.
        pub fn prove(&self, _prover: &Prover, leaves: &[(&Proof, [u64; 4])]) -> Result<TreeProof, Error> {
            let leaves = leaves
                .iter()
                .map(|&(proof, output)| self.inner(proof, output))
                .collect::<Result<Vec<_>, _>>()?;
            Ok(self.0.prove_tree(&leaves)?)
        }

        /// Check that `root` is the root of a tree whose leaves prove `outputs`, in order: its recursion proof,
        /// its digest of the outputs, and the claims it carries.
        ///
        /// # Errors
        ///
        /// The first check that refuses.
        pub fn verify(&self, root: &TreeProof, outputs: &[[u64; 4]]) -> Result<(), Error> {
            Ok(self.0.verify(root, outputs)?)
        }

        /// Check a tree proof's recursion proof alone, short of its claims and its leaves.
        ///
        /// # Errors
        ///
        /// The recursion proof does not verify.
        pub fn verify_proof(&self, proof: &TreeProof) -> Result<(), Error> {
            Ok(self.0.verify_proof(proof)?)
        }

        /// The circuit of a proof of this kind.
        pub fn stats(&self, kind: Kind) -> CircuitStats {
            let circuit = self.0.circuit(kind);
            CircuitStats {
                rows: circuit.row_counts(),
                log_rows: rec::proof::heights(circuit),
                committed: rec::proof::committed_words(circuit),
            }
        }
    }
}
