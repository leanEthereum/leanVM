//! Shared word gadgets and the instruction circuit interface.
//!
//! Rust and Python agree on the port layout and the order products are made in.
//! Only products are committed; XOR, NOT and copying are free.

pub use super::semantics::blake2s_witness;

use flock::circuit::{Builder, Circuit, Wire};

/// A class's circuit: its function as a gate list over the words its table puts on the bus.
///
/// The gate list reads the input words, then writes the output words, in the order the class declares them.
pub trait ClassCircuit {
    /// The class's gate list.
    fn circuit() -> Circuit;
}

/// A word of wires, low bit first.
pub(super) type Word = Vec<Wire>;

/// Word operations on a gate builder.
///
/// A gadget makes its products in a fixed order.
///
/// The Python verifier mirrors that order, so a gadget's loop order is part of the circuit.
pub(super) trait WordGadgets {
    /// `x ^ y`, bit by bit; no product.
    fn xor_word(&mut self, x: &[Wire], y: &[Wire]) -> Word;

    /// `s * x`, bit by bit; one product per bit.
    fn and_word(&mut self, s: Wire, x: &[Wire]) -> Word;

    /// Whether any bit of `x` is set; one product per OR.
    fn any(&mut self, x: &[Wire]) -> Wire;

    /// `x + y + carry_in`, and the carry out of the top bit; one product per bit.
    fn add_with_carry(&mut self, x: &[Wire], y: &[Wire], carry_in: Wire) -> (Word, Wire);

    /// `x + y` modulo `2^width`; one product per bit but the top.
    fn add_wrapping(&mut self, x: &[Wire], y: &[Wire]) -> Word;

    /// `-x` if `negative`, else `x`; one product per bit.
    fn negate_if(&mut self, negative: Wire, x: &[Wire]) -> Word;

    /// `x`, bits 32 to 63 replaced by bit 31 when `word` is set; one product per high bit.
    fn sext32_if(&mut self, word: Wire, x: &[Wire]) -> Word;

    /// Commit `x` as output port `port`.
    fn output_word(&mut self, port: usize, x: &[Wire]);

    /// `x` bit-reversed unless `right` is set; one product per bit.
    fn reverse_unless(&mut self, right: Wire, x: &[Wire]) -> Word;

    /// The width thresholds, from the two bits of the width's logarithm: at least 2, at least 4.
    ///
    /// A double word is LD's or SD's, so the two bits are never both set, and their OR is their XOR.
    fn width_thresholds(&mut self, log_width: &[Wire]) -> [Wire; 2];

    /// The bus address: the address, its low two bits kept only where they misalign the access.
    ///
    /// It is the reference's bus address, bit by bit. Bit 2 never misaligns, no width here reaching 8 bytes, so it is cleared.
    fn bus_address(&mut self, address: &[Wire], thresholds: [Wire; 2]) -> Word;

    /// `x` shifted by `8 * amount` bits, left or right; `amount` has three bits.
    ///
    /// Only the low `bits` bits of the result are made, the ones the caller reads.
    fn shift_bytes(&mut self, x: &[Wire], amount: &[Wire], left: bool, bits: usize) -> Word;
}

impl WordGadgets for Builder {
    fn xor_word(&mut self, x: &[Wire], y: &[Wire]) -> Word {
        x.iter().zip(y).map(|(&x, &y)| self.xor(x, y)).collect()
    }

    fn and_word(&mut self, s: Wire, x: &[Wire]) -> Word {
        x.iter().map(|&x| self.and(s, x)).collect()
    }

    fn any(&mut self, x: &[Wire]) -> Wire {
        x.iter().fold(None, |acc, &bit| self.or(acc, bit))
    }

    fn add_with_carry(&mut self, x: &[Wire], y: &[Wire], carry_in: Wire) -> (Word, Wire) {
        let mut carry = carry_in;
        let mut sum = Vec::with_capacity(x.len());
        for (&x, &y) in x.iter().zip(y) {
            // The sum bit is x ^ y ^ c.
            let xc = self.xor(x, carry);
            let yc = self.xor(y, carry);
            sum.push(self.xor(xc, y));

            // The carry out is maj(x, y, c) = ((x ^ c)(y ^ c)) ^ c.
            let maj = self.and(xc, yc);
            carry = self.xor(maj, carry);
        }
        (sum, carry)
    }

    fn add_wrapping(&mut self, x: &[Wire], y: &[Wire]) -> Word {
        let (mut carry, width) = (None, x.len());
        let mut sum = Vec::with_capacity(width);
        for (i, (&x, &y)) in x.iter().zip(y).enumerate() {
            // The sum bit is x ^ y ^ c.
            let xc = self.xor(x, carry);
            let yc = self.xor(y, carry);
            sum.push(self.xor(xc, y));

            // The carry out of the top bit falls off the modulus, so it is never made.
            if i + 1 < width {
                let maj = self.and(xc, yc);
                carry = self.xor(maj, carry);
            }
        }
        sum
    }

    fn negate_if(&mut self, negative: Wire, x: &[Wire]) -> Word {
        // Two's complement: (x ^ negative) + negative.
        let flipped: Word = x.iter().map(|&bit| self.xor(bit, negative)).collect();
        self.add_with_carry(&flipped, &[None; 64], negative).0
    }

    fn sext32_if(&mut self, word: Wire, x: &[Wire]) -> Word {
        (0..64)
            .map(|i| if i < 32 { x[i] } else { self.mux(word, x[31], x[i]) })
            .collect()
    }

    fn output_word(&mut self, port: usize, x: &[Wire]) {
        for (bit, &wire) in x.iter().enumerate() {
            self.output(port, bit, wire);
        }
    }

    fn reverse_unless(&mut self, right: Wire, x: &[Wire]) -> Word {
        (0..64).map(|i| self.mux(right, x[i], x[63 - i])).collect()
    }

    fn width_thresholds(&mut self, log_width: &[Wire]) -> [Wire; 2] {
        [self.xor(log_width[0], log_width[1]), log_width[1]]
    }

    fn bus_address(&mut self, address: &[Wire], thresholds: [Wire; 2]) -> Word {
        (0..64)
            .map(|i| match i {
                0 | 1 => self.and(address[i], thresholds[i]),
                2 => None,
                _ => address[i],
            })
            .collect()
    }

    fn shift_bytes(&mut self, x: &[Wire], amount: &[Wire], left: bool, bits: usize) -> Word {
        let mut x = x.to_vec();
        for (stage, &bit) in amount.iter().enumerate() {
            // Stage k moves by 8 * 2^k bits when bit k is set; a vacated bit is zero.
            let by = 8 << stage;
            let from = |x: &[Wire], i: usize| {
                if left {
                    i.checked_sub(by).and_then(|j| x[j])
                } else {
                    x.get(i + by).copied().flatten()
                }
            };
            let made = if stage + 1 == amount.len() { bits } else { 64 };
            x = (0..made).map(|i| self.mux(bit, from(&x, i), x[i])).collect();
        }
        x
    }
}

#[cfg(test)]
mod tests {
    use crate::rv::entry::Class;
    use crate::rv::semantics::tests::edge_word;
    use proptest::strategy::{Strategy, ValueTree};
    use proptest::test_runner::TestRunner;

    /// Every class with a circuit.
    const CLASSES: [Class; 11] = [
        Class::Alu,
        Class::Shift,
        Class::Load,
        Class::Store,
        Class::Ld,
        Class::Sd,
        Class::Mul,
        Class::Mulh,
        Class::Div,
        Class::Hash,
        Class::Ext,
    ];

    #[test]
    fn instance_sizes_are_pinned() {
        // The log of each instance's bits, which the tables fix before any circuit is built.
        let sizes = CLASSES.map(|class| class.circuit().k_log());
        assert_eq!(sizes, [10, 10, 10, 10, 8, 8, 12, 13, 13, 14, 13]);
    }

    #[test]
    fn every_bitsliced_witness_is_the_one_instance_walk() {
        // Invariant: the 64-lane walk the prover runs writes what the one-instance walk writes.
        //
        // Fixture: 128 instances per circuit, so two 64-lane walks.
        let n_log = 7;
        let mut runner = TestRunner::deterministic();
        for circuit in CLASSES.map(Class::circuit) {
            // Edge-biased words drive every carry and comparison.
            let mut draw = || edge_word().new_tree(&mut runner).unwrap().current();
            let rows: Vec<Vec<u64>> = (0..1 << n_log)
                .map(|_| (0..circuit.n_input_words()).map(|_| draw()).collect())
                .collect();

            // The same batch through both generators, every table compared.
            let walk = circuit.generate_witness_with(&rows, &rows[0], 1 << n_log, &mut [], |row, z, az, bz| {
                circuit.witness_instance(row, z, az, bz);
            });
            let sliced = circuit.generate_witness_from(&rows, &rows[0], 1 << n_log, &mut [], |row, words| {
                words.copy_from_slice(row);
            });
            assert!(walk.0[..] == sliced.0[..], "z");
            assert!(walk.1[..] == sliced.1[..], "A*z");
            assert!(walk.2[..] == sliced.2[..], "B*z");
            assert!(walk.3[..] == sliced.3[..], "lincheck stripes");
        }
    }
}
