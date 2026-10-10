//! The prover: it runs a program and proves the run.

use super::{Output, Program, Proof, ProveError, Stats};
use crate::pcs::Rate;
use tracing::info_span;

/// A prover: it proves runs at one commitment rate.
///
/// The rate trades proving time for proof size.
///
/// The verifier needs no rate: each proof announces its own.
///
/// # Performance
///
/// A proof touches gigabytes of memory, and frees it before returning.
///
/// So its speed depends on the process's global allocator:
///
/// - one that keeps freed pages mapped serves the next proof from them, with no page fault;
/// - jemalloc with dirty pages that never decay does this, and the CLI installs it;
/// - glibc's default unmaps a large block on free, which is the slow case.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Prover {
    /// The commitment rate every proof is made at.
    rate: Rate,
}

impl Prover {
    /// A prover at this commitment rate.
    ///
    /// It also spawns the process's worker pool, which every prover shares.
    #[must_use]
    pub fn new(rate: Rate) -> Self {
        // Spawning up front keeps the spawn cost out of the first proof.
        crate::init_prover();
        Self { rate }
    }

    /// The commitment rate every proof is made at.
    #[must_use]
    pub const fn rate(&self) -> Rate {
        self.rate
    }

    /// Run the program on the advice, and prove the run.
    ///
    /// # Arguments
    ///
    /// - `program`: what runs.
    /// - `advice`: the advice region's first words, the rest being zero.
    ///
    /// # Errors
    ///
    /// - The run traps.
    /// - The run is longer than one proof holds.
    /// - The advice is longer than the program's region.
    #[tracing::instrument(name = "Prove", skip_all, fields(log_inv_rate = self.rate.log_inv_rate()))]
    pub fn prove(&self, program: &Program, advice: &[u64]) -> Result<ProvenRun, ProveError> {
        let exec = info_span!("Execute program").in_scope(|| program.execute(advice))?;
        program.committed_size(exec.trace.row_counts(), exec.trace.registers.live)?;
        let (proof, stats) = program.prove_execution(&exec, self.rate);
        Ok(ProvenRun {
            proof,
            output: Output::new(exec.output),
            stats,
        })
    }
}

/// A proven run: the proof, the output it proves, and what the run cost.
#[derive(Clone, Debug)]
#[non_exhaustive]
pub struct ProvenRun {
    /// The proof of the run.
    pub proof: Proof,
    /// The registers `a0..a3` at the run's exit.
    pub output: Output,
    /// The run's cost: its cycles, its table heights and its committed words.
    pub stats: Stats,
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::rv::Region;
    use crate::rv::asm::{Addi, Asm, Reg};

    #[test]
    fn a_second_proof_leaves_the_first_intact() {
        // Fixture state: `a0 = 5; exit`, proven once.
        let text = Asm::new().i(Addi, Reg::A0, Reg::ZERO, 5).exit().finish();
        let program = Program::new(&text, Region::TEXT.base(), vec![], 0, 0).expect("a program");
        let prover = Prover::new(Rate::MIN);
        let first = prover.prove(&program, &[]).expect("the run exits");
        assert_eq!(first.output, [5, 0, 0, 0]);

        // A second proof reuses the pool and the pages the first freed.
        let second = prover.prove(&program, &[]).expect("the run exits");

        // Both still verify: no buffer of the first was shared with the second.
        program.verify(second.output, &second.proof).unwrap();
        program.verify(first.output, &first.proof).unwrap();
    }

    #[test]
    fn more_advice_than_the_region_holds_is_refused() {
        // Fixture state: an advice region of 2^0 = 1 word.
        let text = Asm::new().exit().finish();
        let program = Program::new(&text, Region::TEXT.base(), vec![], 0, 0).expect("a program");

        // Two words do not fit: an error, not a panic.
        assert_eq!(
            Prover::new(Rate::MIN).prove(&program, &[1, 2]).map(|_| ()),
            Err(ProveError::AdviceTooLong { max: 1, got: 2 })
        );
    }
}
