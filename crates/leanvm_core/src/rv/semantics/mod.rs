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
pub use ext::Ext;
pub use hash::{BlockAccess, Hash, blake2s_witness};
pub use memory::{Ld, Load, Sd, Store, WordAccess};
pub use multiply::{Mul, Mulh};
pub use shift::Shift;

use super::circuits::ClassCircuit;

/// An instruction class: its flag words, its function, and the circuit that proves it.
///
/// The reference function and the circuit agree on every instance with a legal flag word.
pub trait InstructionClass: ClassCircuit {
    /// The flag words the class defines.
    const LEGAL: &'static [u64];

    /// What the class computes.
    type Output;

    /// What the class computes on this instance.
    fn eval(&self) -> Self::Output;
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
    use crate::rv::Class;
    use crate::tables::spec::InstanceWitness;
    use flock::circuit::Circuit;
    use proptest::prelude::*;
    use proptest::sample::select;
    use proptest::strategy::ValueTree;
    use proptest::test_runner::{Config, TestRunner};
    use std::fmt::Debug;

    /// The words arithmetic most often gets wrong: zero, one, all ones, and the sign bits.
    pub(super) const EDGES: [u64; 8] = [
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
            prop_assert_eq!(Alu { flags: Alu::WORD, v1, v2, imm: 0, dt: 0, pc4: 0 }.eval().0, w(a.wrapping_add(b)));
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

    // A class's circuit ports: the instance's input words, then the result's output words.
    pub(super) trait Ports: InstructionClass {
        // The class an entry of this kind names.
        const CLASS: Class;

        fn input_words(&self) -> Vec<u64>;

        fn output_words(&self, output: &Self::Output) -> Vec<u64>;
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
    pub(super) fn circuit_matches_reference<C: Ports + Arbitrary + Debug>(cases: u32) {
        let circuit = C::circuit();

        // The runtime dispatch on the class names this type's flags and circuit.
        assert_eq!(C::CLASS.legal_flags(), C::LEGAL);
        assert_eq!(C::CLASS.circuit().useful_bits(), circuit.useful_bits());

        let mut runner = TestRunner::new(Config::with_cases(cases));
        runner
            .run(&any::<C>(), |instance| {
                // The reference's output words, against the circuit's on the instance's input words.
                let expected = instance.output_words(&instance.eval());
                prop_assert_eq!(run(&circuit, &instance.input_words(), expected.len()), expected);
                Ok(())
            })
            .unwrap();
    }

    /// Every combination of one word per input port, the first port varying fastest.
    pub(super) fn grid(ports: &[&[u64]]) -> Vec<Vec<u64>> {
        ports.iter().fold(vec![vec![]], |rows, port| {
            port.iter()
                .flat_map(|&word| {
                    rows.iter().map(move |row| {
                        let mut row = row.clone();
                        row.push(word);
                        row
                    })
                })
                .collect()
        })
    }

    /// Check a class's word-level witness: on every instance, the tables it writes are the ones the walk of the circuit's gate list writes.
    ///
    /// The instances are `edges`, then 4096 random ones: every other one an instance the decoder can make, the rest edge-biased words in every input port, flags included.
    /// Each instance is checked alone against the bit-by-bit walk, then the whole batch's packed tables and lincheck stripes against the 64-lane walk.
    pub(super) fn word_witness_is_the_walk<C: Ports + Arbitrary>(witness: InstanceWitness, edges: Vec<Vec<u64>>) {
        let circuit = C::circuit();
        let n_in = circuit.n_input_words();
        let mut runner = TestRunner::deterministic();
        let random = (0..4096).map(|i| {
            if i % 2 == 0 {
                any::<C>().new_tree(&mut runner).unwrap().current().input_words()
            } else {
                (0..n_in)
                    .map(|_| edge_word().new_tree(&mut runner).unwrap().current())
                    .collect()
            }
        });
        let rows: Vec<Vec<u64>> = edges.into_iter().chain(random).collect();

        let words = 1 << (circuit.k_log() - 6);
        let tables = || [vec![0u64; words], vec![0; words], vec![0; words]];
        for row in &rows {
            assert_eq!(row.len(), n_in, "an edge instance has the wrong number of input words");
            let [mut z, mut az, mut bz] = tables();
            circuit.witness_instance(row, &mut z, &mut az, &mut bz);
            let walk = [z, az, bz];
            let [mut z, mut az, mut bz] = tables();
            witness(row, &mut z, &mut az, &mut bz);
            for (name, (walk, word)) in ["z", "A·z", "B·z"].into_iter().zip(walk.iter().zip([z, az, bz])) {
                let at = walk.iter().zip(&word).position(|(a, b)| a != b);
                assert!(at.is_none(), "{name} word {at:?} on inputs {row:#x?}");
            }
        }

        let n_log = rows.len().next_power_of_two().trailing_zeros() as usize;
        let walk = circuit.generate_witness_from(&rows, &rows[0], n_log, |row, words| words.copy_from_slice(row));
        let words = circuit.generate_witness_with(&rows, &rows[0], n_log, |row, z, az, bz| witness(row, z, az, bz));
        assert!(walk.z == words.z, "z");
        assert!(walk.az == words.az, "A·z");
        assert!(walk.bz == words.bz, "B·z");
        assert!(walk.stripes == words.stripes, "lincheck stripes");
    }
}
