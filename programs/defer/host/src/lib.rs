//! The defer program off the VM: the advice for the next Fibonacci number from two proven ones, the runs it assumes,
//! and the output the guest must give.

use leanvm_guest::{PublicValues, Run};

/// The guest (`../guest`), built by `programs/build.sh`.
pub const ELF: &[u8] = include_bytes!("../../defer.elf");
/// The Fibonacci guest (`programs/fibonacci/guest`), whose runs the defer guest assumes.
pub const FIBONACCI_ELF: &[u8] = include_bytes!("../../../fibonacci/fibonacci.elf");

/// One run of the guest: what it is given and must output, what it assumes, and what it states once they are proven.
pub struct Assuming {
    /// The advice, and the output: the digest of the committed values, folded with the assumptions.
    pub run: Run,
    /// The assumptions the run makes, in order: each a program's digest and the output of a run of it.
    pub assumed: [([u64; 4], [u64; 4]); 2],
    /// The digest of the committed values: what the run states once its assumptions are proven.
    pub committed: [u64; 4],
}

/// The run giving `F(n + 2)` from `F(n)` and `F(n + 1)`, `fibonacci` the Fibonacci program's digest.
pub fn run(fibonacci: [u64; 4], n: u64) -> Assuming {
    let (mut f0, mut f1) = (0u64, 1u64);
    for _ in 0..n {
        (f0, f1) = (f1, f0.wrapping_add(f1));
    }
    let assumed = [
        (fibonacci, defer::fibonacci_output(n, f0)),
        (fibonacci, defer::fibonacci_output(n + 1, f1)),
    ];
    let mut public = PublicValues::new();
    for (program, output) in &assumed {
        public.verify_proof(program, output);
    }
    public.commit(&fibonacci).commit(&defer::next(n, f0, f1));
    let mut advice = fibonacci.to_vec();
    advice.extend([n, f0, f1]);
    Assuming {
        run: Run {
            advice,
            expected: public.clone().digest(),
        },
        assumed,
        committed: public.committed(),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use leanvm_core::{Assumption, Machine, Output, Program, Trap};

    /// A guest on the interpreter, with no proof: its output, or the trap.
    fn on_the_vm(elf: &[u8], advice: &[u64]) -> Result<[u64; 4], Trap> {
        let program = Program::from_elf(elf).expect("the guest's ELF file");
        Machine::new(program.rv(), advice).run()
    }

    fn fibonacci() -> [u64; 4] {
        Program::from_elf(FIBONACCI_ELF)
            .expect("the guest's ELF file")
            .digest_words()
    }

    fn assumptions(assumed: [([u64; 4], [u64; 4]); 2]) -> [Assumption; 2] {
        assumed.map(|(program, output)| Assumption::new(program, Output::new(output)))
    }

    #[test]
    fn the_guest_folds_its_assumptions_as_the_core_does() {
        // Invariant: the guest exits with its committed digest folded with its assumptions, as the SDK computes it off
        // the VM and as the core's `Output::assuming`, which a verifier checks against, computes it.
        let assuming = run(fibonacci(), 90);
        assert_eq!(
            Output::new(assuming.committed).assuming(&assumptions(assuming.assumed)),
            assuming.run.expected
        );
        assert_eq!(on_the_vm(ELF, &assuming.run.advice), Ok(assuming.run.expected));
    }

    #[test]
    fn each_assumption_is_a_run_of_the_fibonacci_guest() {
        // Invariant: what the guest assumes is the Fibonacci guest's digest and the output of its real run on `n` and
        // on `n + 1`, so proofs of those runs resolve the assumptions.
        let (fibonacci, n) = (fibonacci(), 90);
        for (i, (program, output)) in run(fibonacci, n).assumed.into_iter().enumerate() {
            assert_eq!(program, fibonacci);
            assert_eq!(
                on_the_vm(FIBONACCI_ELF, &[n + i as u64]),
                Ok(output),
                "the run on n + {i}"
            );
        }
    }

    #[test]
    fn a_wrong_fibonacci_number_moves_the_output() {
        // Mutation: `F(n)` one more and `F(n + 1)` one less in the advice.
        //
        //     the committed values are unchanged (the sum is), the assumed outputs are not
        //     → the guest exits, as it checks nothing, but its output folds the wrong assumptions
        let assuming = run(fibonacci(), 90);
        let mut advice = assuming.run.advice.clone();
        advice[5] = advice[5].wrapping_add(1);
        advice[6] = advice[6].wrapping_sub(1);
        let wrong = [
            (assuming.assumed[0].0, defer::fibonacci_output(90, advice[5])),
            (assuming.assumed[1].0, defer::fibonacci_output(91, advice[6])),
        ];
        let output = on_the_vm(ELF, &advice).expect("the guest checks nothing itself");
        assert_ne!(output, assuming.run.expected);
        assert_eq!(Output::new(assuming.committed).assuming(&assumptions(wrong)), output);
    }
}
