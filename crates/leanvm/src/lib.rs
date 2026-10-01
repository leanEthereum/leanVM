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
    rv::{ADVICE_BASE, ElfError, ProgramError, RAM_BASE, TEXT_BASE, Trap, asm},
};

/// The commitment's rate, as the base-two logarithm of its inverse.
///
/// A larger value, a lower rate, makes a smaller proof and a slower prover.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct Rate(u8);

impl Rate {
    /// The fastest prover, and the largest proof.
    pub const MIN: Self = Self(leanvm_core::pcs::MIN_LOG_INV_RATE as u8);

    /// The smallest proof, and the slowest prover.
    pub const MAX: Self = Self(leanvm_core::pcs::MAX_LOG_INV_RATE as u8);

    /// The rate `2^-log_inv_rate`.
    ///
    /// # Errors
    ///
    /// A rate the commitment does not support.
    pub fn new(log_inv_rate: u8) -> Result<Self, Error> {
        if (Self::MIN.0..=Self::MAX.0).contains(&log_inv_rate) {
            Ok(Self(log_inv_rate))
        } else {
            Err(Error::InvalidRate {
                log_inv_rate: log_inv_rate.into(),
            })
        }
    }

    /// The base-two logarithm of the inverse rate.
    #[must_use]
    pub fn log_inv_rate(self) -> u8 {
        self.0
    }
}

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
        let (proof, output, stats) = cpu::prove(program, advice, rate.0.into())?;
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
    Ok(cpu::measure(program, advice)?)
}

/// Check that the program, run on some advice, exits with `output`.
///
/// # Errors
///
/// The proof does not verify against this program and this output.
pub fn verify(program: &Program, output: &[u64; 4], proof: &Proof) -> Result<(), Error> {
    cpu::verify(program, output, &proof.0).map_err(|error| Error::Verify(VerifyError(error)))
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
    const VERSION: u16 = 1;

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
#[derive(Clone, Debug, PartialEq, Eq)]
#[non_exhaustive]
pub enum Error {
    /// The file is not a guest.
    Elf(ElfError),
    /// The text and RAM form no program.
    Program(ProgramError),
    /// The run trapped, so it has no proof.
    Trap(Trap),
    /// The run is longer than one proof holds.
    TooLong,
    /// More advice words than the program's region holds.
    AdviceTooLong { max: usize, got: usize },
    /// A rate the commitment does not support.
    InvalidRate { log_inv_rate: usize },
    /// Bytes that are no proof.
    MalformedProof,
    /// A proof of another protocol version.
    UnsupportedVersion { found: u16 },
    /// The proof does not verify.
    Verify(VerifyError),
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Elf(error) => error.fmt(f),
            Self::Program(error) => error.fmt(f),
            Self::Trap(trap) => write!(f, "the run traps: {trap}"),
            Self::TooLong => f.write_str("the run is longer than one proof holds"),
            Self::AdviceTooLong { max, got } => {
                write!(f, "the advice has {got} words, and the program's region holds {max}")
            }
            Self::InvalidRate { log_inv_rate } => write!(
                f,
                "log_inv_rate {log_inv_rate} is not in {}..={}",
                Rate::MIN.0,
                Rate::MAX.0
            ),
            Self::MalformedProof => f.write_str("the bytes are no proof"),
            Self::UnsupportedVersion { found } => write!(
                f,
                "a proof of protocol version {found}, and this verifier reads version {}",
                Proof::VERSION
            ),
            Self::Verify(error) => error.fmt(f),
        }
    }
}

impl std::error::Error for Error {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        match self {
            Self::Elf(error) => error.source(),
            Self::Program(error) => error.source(),
            _ => None,
        }
    }
}

impl From<ElfError> for Error {
    fn from(error: ElfError) -> Self {
        Self::Elf(error)
    }
}

impl From<ProgramError> for Error {
    fn from(error: ProgramError) -> Self {
        Self::Program(error)
    }
}

impl From<ProveError> for Error {
    fn from(error: ProveError) -> Self {
        match error {
            ProveError::Trap(trap) => Self::Trap(trap),
            ProveError::TooLong => Self::TooLong,
            ProveError::AdviceTooLong { max, got } => Self::AdviceTooLong { max, got },
            ProveError::InvalidRate { log_inv_rate } => Self::InvalidRate { log_inv_rate },
        }
    }
}

/// Why a proof does not verify: which stage of the verifier refused it.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct VerifyError(CpuError);

impl fmt::Display for VerifyError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "the proof does not verify: {}", self.0)
    }
}

impl std::error::Error for VerifyError {}
