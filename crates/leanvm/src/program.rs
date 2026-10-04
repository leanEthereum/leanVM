//! A program: what a proof is about, and what checks it.

use crate::{ElfError, Output, ProgramError, Proof, ProveError, Stats, VerifyError};
use leanvm_core::cpu;
use std::fmt::{self, Debug, Formatter};

/// A validated RISC-V program.
///
/// It carries a digest of everything public about it:
///
/// - the decoded text and the entry point,
/// - the RAM image,
/// - the sizes of RAM and of the advice.
///
/// The digest seeds every proof's transcript.
///
/// So a proof of one program is refused by any other.
#[derive(Clone)]
pub struct Program(pub(crate) cpu::Program);

impl Program {
    /// The program of a guest's ELF executable.
    ///
    /// # Errors
    ///
    /// - A file that is no guest.
    /// - A guest whose text and RAM form no program.
    pub fn from_elf(elf: &[u8]) -> Result<Self, ElfError> {
        cpu::Program::from_elf(elf).map(Self)
    }

    /// The program of a hand-written text.
    ///
    /// # Arguments
    ///
    /// - `text`: the instruction words, placed at the text region's base.
    /// - `entry_pc`: the first instruction's address, inside the text.
    /// - `image`: RAM's first words, the rest being zero.
    /// - `log_ram`: RAM holds `2^log_ram` words.
    /// - `log_advice`: the advice region holds `2^log_advice` words.
    ///
    /// # Errors
    ///
    /// - An entry outside the text.
    /// - Sizes beyond the machine's regions.
    pub fn new(
        text: &[u32],
        entry_pc: u64,
        image: Vec<u64>,
        log_ram: usize,
        log_advice: usize,
    ) -> Result<Self, ProgramError> {
        cpu::Program::new(text, entry_pc, image, log_ram, log_advice).map(Self)
    }

    /// What a proof of a run on this advice would cost.
    ///
    /// It takes one execution and no proof.
    ///
    /// # Errors
    ///
    /// What would refuse the proof itself: a trap, a run too long for one proof, or too much advice.
    pub fn measure(&self, advice: &[u64]) -> Result<Stats, ProveError> {
        self.0.measure(advice)
    }

    /// Check that the proof shows this program, run on some advice, exiting with this output.
    ///
    /// # Errors
    ///
    /// The proof is not one of this program and this output.
    pub fn verify(&self, output: Output, proof: &Proof) -> Result<(), VerifyError> {
        Ok(self.0.verify(output.words(), &proof.0)?)
    }
}

impl Debug for Program {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        // The decoded text and the image are thousands of words, which say nothing to a reader.
        f.debug_struct("Program").finish_non_exhaustive()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::fixtures;

    #[test]
    fn a_proof_binds_its_program_and_its_output() {
        // Fixture state: a proof that F(90) mod 2^64 is the output.
        let (program, run) = (fixtures::fibonacci(90), fixtures::fibonacci_run());
        program.verify(run.output, &run.proof).unwrap();

        // Mutation: the same text with another image word, n = 91.
        //
        //     another image  →  another digest  →  another transcript
        let other = fixtures::fibonacci(91);
        assert!(other.verify(run.output, &run.proof).is_err());

        // Mutation: the claimed a0 is off by one.
        let mut words = *run.output.words();
        words[0] += 1;
        assert!(program.verify(Output::new(words), &run.proof).is_err());
    }

    #[test]
    fn measuring_a_run_announces_the_proofs_cost() {
        // Measuring executes without proving, and must agree with what the proof reported.
        let run = fixtures::fibonacci_run();
        assert_eq!(fixtures::fibonacci(90).measure(&[]).as_ref(), Ok(&run.stats));
    }

    #[test]
    fn a_file_that_is_no_guest_is_refused() {
        // The four bytes of the ELF magic, and nothing after them.
        assert!(matches!(Program::from_elf(b"\x7fELF"), Err(ElfError::Truncated)));
    }
}
