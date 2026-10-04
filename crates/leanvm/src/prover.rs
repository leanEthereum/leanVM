//! The prover: it runs a program and proves the run.

use crate::{Output, Program, Proof, ProveError, Rate, Stats};

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
        leanvm_core::init_prover();
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
    pub fn prove(&self, program: &Program, advice: &[u64]) -> Result<ProvenRun, ProveError> {
        let (proof, output, stats) = program.0.prove(advice, self.rate)?;
        Ok(ProvenRun {
            proof: Proof(proof),
            output: Output::new(output),
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
    use crate::asm::Asm;
    use crate::{Region, fixtures};

    #[test]
    fn a_run_proves_its_output() {
        // a0 holds F(90) mod 2^64, and the program clears a1 and a2 before exit.
        assert_eq!(fixtures::fibonacci_run().output, [2_880_067_194_370_816_120, 0, 0, 0]);
    }

    #[test]
    fn the_advice_is_hidden_from_the_verifier() {
        let prover = Prover::new(Rate::MIN);

        // Two messages; the empty one makes the guest read a length of zero, then no word.
        for message in [b"leanVM".as_slice(), b""] {
            let (guest, advice, digest) = fixtures::preimage(message);
            let run = prover.prove(&guest, &advice).expect("the run exits");
            assert_eq!(run.output, digest, "the guest hashed the advice");

            // The verifier gets the program and the output, never the advice.
            guest.verify(run.output, &run.proof).unwrap();
        }
    }

    #[test]
    fn a_second_proof_leaves_the_first_intact() {
        // Fixture state: a first proof, made earlier and shared.
        let (program, first) = (fixtures::fibonacci(90), fixtures::fibonacci_run());

        // A second proof of the same run reuses the pool and the freed pages.
        let second = Prover::new(Rate::MIN).prove(&program, &[]).expect("the run exits");

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
