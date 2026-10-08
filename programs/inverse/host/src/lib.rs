//! The `inverse` program off the VM: the advice that asks the guest for inverses, and the output it must give, from the
//! guest's library run natively, where a hint is its closure run in place.

use inverse::{from_canonical, inverse_by_hint, to_canonical};
use leanvm_guest::{PublicValues, Run};

pub use inverse::{BY_EXPONENT, BY_HINT, BY_WRONG_HINT};

/// The guest (`../guest`), built by `programs/build.sh`.
pub const ELF: &[u8] = include_bytes!("../../inverse.elf");

/// The guest inverting `elements`, each nonzero and below `p`, the way `how` says (`BY_EXPONENT`, `BY_HINT`, ...).
pub fn run(how: u64, elements: &[[u64; 4]]) -> Run {
    let mut advice = vec![how, elements.len() as u64];
    let mut public = PublicValues::new();
    for x in elements {
        advice.extend(x);
        public.commit(&to_canonical(&inverse_by_hint(&from_canonical(x))));
    }
    Run {
        advice,
        expected: public.digest(),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use inverse::inverse;
    use leanvm_core::asm::{ImmOp, Instruction, Op, Reg};
    use leanvm_core::{Guest, Machine, Program, ProveError, Prover, Rate, Trap};
    use primitives::test_util::Rng;

    /// `n` elements below `p`, from a seed.
    fn elements(n: usize) -> Vec<[u64; 4]> {
        let mut rng = Rng::new(0x1a7e);
        (0..n)
            .map(|_| std::array::from_fn(|i| rng.next_u64() >> if i == 3 { 4 } else { 0 }))
            .collect()
    }

    #[test]
    fn the_field_is_bn254s() {
        // Fixture: 2, whose inverse is (p + 1) / 2, and the elements the other tests invert.
        let half = [
            0x9e10_460b_6c3e_7ea4,
            0xcbc0_b548_b438_e546,
            0xdc28_22db_40c0_ac2e,
            0x1832_2739_7098_d014,
        ];
        assert_eq!(to_canonical(&inverse(&from_canonical(&[2, 0, 0, 0]))), half);
        for x in elements(8) {
            assert_eq!(to_canonical(&from_canonical(&x)), x);
        }
    }

    #[test]
    fn the_vm_hints_what_the_native_code_computes() {
        // Invariant: on the VM a hint is its closure run unproven, so each hinted word is what the closure computes
        // natively, and the hinted inverses commit what the proven exponentiations do.
        let xs = elements(3);
        let program = Program::from_elf(ELF).unwrap();
        let mut by_hint = Machine::new(program.rv(), &run(BY_HINT, &xs).advice);
        assert_eq!(by_hint.run(), Ok(run(BY_HINT, &xs).expected));
        assert_eq!(
            Machine::new(program.rv(), &run(BY_EXPONENT, &xs).advice).run(),
            Ok(run(BY_HINT, &xs).expected)
        );

        // The hints take the advice's end, from the top down, each in its words' order.
        let top = 1 << program.rv().log_advice();
        let expected: Vec<(usize, u64)> = (xs.iter().enumerate())
            .flat_map(|(k, x)| {
                let inv = inverse(&from_canonical(x));
                (0..4).map(move |i| (top - 4 * (k + 1) + i, inv[i]))
            })
            .collect();
        assert_eq!(by_hint.hints(), expected);
    }

    /// `text` as the proof decodes it: each `hint.enter rd` the `addi rd, x0, 0` it decodes to, each `hint.exit` an
    /// illegal word.
    fn without_markers(text: &[u32]) -> Vec<u32> {
        let plain = |word: u32| match Instruction::from_bits(word).decode() {
            Some(Op::HintEnter { rd }) => Op::Imm {
                op: ImmOp::Addi,
                rd,
                rs1: Reg::ZERO,
                imm: 0,
            }
            .encode()
            .bits(),
            Some(Op::HintExit { .. }) => 0,
            _ => word,
        };
        text.iter().map(|&word| plain(word)).collect()
    }

    #[test]
    fn a_hinted_run_proves_and_a_wrong_hint_does_not() {
        // A hinted run proves its output, and the proof is of the program the proof decodes: the same proof verifies
        // against the program with no hint at all, its markers replaced by what they decode to.
        let program = Program::from_elf(ELF).unwrap();
        let run_ = run(BY_HINT, &elements(2));
        let proven = Prover::new(Rate::MIN)
            .prove(&program, &run_.advice)
            .expect("the run halts");
        assert_eq!(proven.output, run_.expected);
        program
            .verify(proven.output, &proven.proof)
            .expect("an honest proof verifies");

        let guest = Guest::from_elf(ELF).unwrap();
        let text = without_markers(&guest.text);
        assert_ne!(text, guest.text);
        let plain = Program::new(&text, guest.entry_pc, guest.image, guest.log_ram, guest.log_advice).unwrap();
        plain
            .verify(proven.output, &proven.proof)
            .expect("the proof is of the decoded program");

        // Mutation: the hint, its every word flipped in its lowest bit.
        //
        //     the guest's check fails → it panics → an illegal instruction → no proof
        let wrong = run(BY_WRONG_HINT, &elements(2));
        assert!(matches!(
            Prover::new(Rate::MIN).prove(&program, &wrong.advice),
            Err(ProveError::Trap(Trap::Illegal { .. }))
        ));
    }
}
