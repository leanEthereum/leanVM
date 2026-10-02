//! What each instruction class computes.
//!
//! A class is a type whose value is one instance: the flag word and the operands the class reads.
//!
//! The flag word stays a `u64`.
//!
//! It is the bytecode word the proof commits, and its bits are the circuit's selectors.
//!
//! Every class implements one trait, so code over all classes is written once.
//!
//! These functions are the reference.
//!
//! The interpreter runs them, and each class's circuit is tested against them.
//!
//! Each one is defined on its class's legal flag words only.

mod alu;
mod divide;
mod ext;
mod hash;
mod memory;
mod multiply;
mod shift;

pub use alu::Alu;
pub use divide::Div;
pub use ext::{Ext, ExtResult, Limb};
pub use hash::{BlockAccess, Hash, blake2s_witness};
pub use memory::{Load, Store, WordAccess};
pub use multiply::{Mul, Mulh};
pub use shift::Shift;

use super::circuits::ClassCircuit;
use super::entry::Class;

/// An instruction class: its flag words, its function, and the circuit that proves it.
///
/// The circuit's ports are the instance's input words, then the result's output words.
///
/// The reference function and the circuit agree on every instance with a legal flag word.
pub trait InstructionClass: ClassCircuit {
    /// The class an entry of this kind names.
    const CLASS: Class;

    /// The flag words the class defines.
    const LEGAL: &'static [u64];

    /// What the class computes.
    type Output;

    /// What the class computes on this instance.
    fn eval(&self) -> Self::Output;

    /// The circuit's input words for this instance, in port order.
    fn input_words(&self) -> Vec<u64>;

    /// The circuit's output words for a result, in port order.
    fn output_words(output: &Self::Output) -> Vec<u64>;
}

/// What an entry computes from the values it reads.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Outcome {
    /// The class's result.
    pub out: u64,
    /// Whether the class takes the jump.
    pub taken: bool,
    /// A load's or a store's cell access.
    pub access: Option<WordAccess>,
}

/// Sign-extend the low 32 bits of `x`.
const fn sext32(x: u64) -> u64 {
    x as u32 as i32 as i64 as u64
}

#[cfg(test)]
pub(super) mod tests {
    use super::*;
    use flock::circuit::Circuit;
    use proptest::prelude::*;
    use proptest::sample::select;
    use proptest::test_runner::{Config, TestRunner};
    use std::fmt::Debug;

    /// The words arithmetic most often gets wrong: zero, one, all ones, and the sign bits.
    const EDGES: [u64; 8] = [
        0,
        1,
        u64::MAX,
        1 << 63,
        (1 << 63) - 1,
        1 << 31,
        (1 << 31) - 1,
        0xffff_ffff,
    ];

    /// A 64-bit word biased toward edge values.
    ///
    /// - Edge words reach the carries, signs and overflows.
    /// - Zero- and sign-extended 32-bit values reach the word forms.
    /// - Small values reach the shift amounts and small divisors.
    /// - Any word covers the rest.
    pub(crate) fn edge_word() -> impl Strategy<Value = u64> {
        prop_oneof![
            1 => select(&EDGES[..]),
            1 => any::<u32>().prop_map(u64::from),
            1 => any::<i32>().prop_map(|x| x as i64 as u64),
            1 => 0u64..65,
            4 => any::<u64>(),
        ]
    }

    proptest! {
        #[test]
        fn word_forms_compute_on_32_bits(v1 in edge_word(), v2 in edge_word()) {
            // Each word form is the 32-bit operation, sign-extended.
            let w = |x: u32| x as i32 as i64 as u64;
            let (a, b) = (v1 as u32, v2 as u32);
            let shift = |flags| Shift { flags, v1, v2, imm: 0 }.eval();
            prop_assert_eq!(Alu { flags: Alu::WORD, v1, v2, imm: 0 }.eval().0, w(a.wrapping_add(b)));
            prop_assert_eq!(Mul { flags: Mul::WORD, v1, v2 }.eval(), w(a.wrapping_mul(b)));
            prop_assert_eq!(shift(Shift::WORD), w(a << (b & 31)));
            prop_assert_eq!(shift(Shift::WORD | Shift::RIGHT), w(a >> (b & 31)));
            prop_assert_eq!(shift(Shift::WORD | Shift::RIGHT | Shift::ARITH), w(((a as i32) >> (b & 31)) as u32));
            if let (Some(q), Some(r)) = (a.checked_div(b), a.checked_rem(b)) {
                prop_assert_eq!(Div { flags: Div::WORD, v1, v2 }.eval(), w(q));
                prop_assert_eq!(Div { flags: Div::WORD | Div::REM, v1, v2 }.eval(), w(r));
            }
        }
    }

    /// The circuit's first `n` output words on `inputs`, read off the witness the gate walk writes.
    pub(super) fn run(circuit: &Circuit, inputs: &[u64], n: usize) -> Vec<u64> {
        // One instance's tables, zeroed.
        let words = 1 << (circuit.k_log() - 6);
        let (mut z, mut az, mut bz) = (vec![0; words], vec![0; words], vec![0; words]);

        // The output ports follow the input ports in the instance's words.
        circuit.witness_instance(inputs, &mut z, &mut az, &mut bz);
        let first = circuit.n_input_words();
        z[first..first + n].to_vec()
    }

    /// Check a class: its dispatch, then `cases` random instances on which its circuit computes its reference function.
    pub(super) fn circuit_matches_reference<C: InstructionClass + Arbitrary + Debug>(cases: u32) {
        let circuit = C::circuit();

        // The runtime dispatch on the class names this type's flags and circuit.
        assert_eq!(C::CLASS.legal_flags(), C::LEGAL);
        assert_eq!(C::CLASS.circuit().useful_bits(), circuit.useful_bits());

        let mut runner = TestRunner::new(Config::with_cases(cases));
        runner
            .run(&any::<C>(), |instance| {
                // The reference's output words, against the circuit's on the instance's input words.
                let expected = C::output_words(&instance.eval());
                prop_assert_eq!(run(&circuit, &instance.input_words(), expected.len()), expected);
                Ok(())
            })
            .unwrap();
    }
}
