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
mod hash;
mod memory;
mod multiply;
mod shift;

pub use alu::Alu;
pub use divide::Div;
pub use hash::{BlockAccess, Hash};
pub use memory::{Load, Store, WordAccess};
pub use multiply::{Mul, Mulh};
pub use shift::Shift;

use super::circuits::ClassCircuit;
use super::entry::{Class, Entry};

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

impl Entry {
    /// What this entry computes from its registers and, for a load or a store, the cell it names.
    ///
    /// The result holds whether or not a run could make the access.
    ///
    /// A hash computes nothing here: its block is the machine's to read.
    pub fn evaluate(&self, v1: u64, v2: u64, cell: u64) -> Outcome {
        let (flags, imm) = (self.flags, self.imm);
        let (out, taken, access) = match self.class {
            Class::Alu => {
                let (out, taken) = Alu { flags, v1, v2, imm }.eval();
                (out, taken, None)
            }
            Class::Shift => (Shift { flags, v1, v2, imm }.eval(), false, None),
            Class::Mul => (Mul { flags, v1, v2 }.eval(), false, None),
            Class::Mulh => (Mulh { flags, v1, v2 }.eval(), false, None),
            Class::Div => (Div { flags, v1, v2 }.eval(), false, None),
            // A load leaves its cell as it was.
            Class::Load => {
                let (address, value) = Load { flags, v1, imm, cell }.eval();
                let access = WordAccess {
                    address,
                    old: cell,
                    new: cell,
                };
                (value, false, Some(access))
            }
            // A store's result is the cell it leaves.
            Class::Store => {
                let (address, new) = Store {
                    flags,
                    v1,
                    v2,
                    imm,
                    cell,
                }
                .eval();
                let access = WordAccess {
                    address,
                    old: cell,
                    new,
                };
                (0, false, Some(access))
            }
            Class::Hash | Class::Illegal => (0, false, None),
        };
        Outcome { out, taken, access }
    }
}

/// Sign-extend the low 32 bits of `x`.
const fn sext32(x: u64) -> u64 {
    x as u32 as i32 as i64 as u64
}

#[cfg(test)]
pub(super) mod tests {
    use super::*;
    use proptest::prelude::*;
    use proptest::sample::select;

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
}
