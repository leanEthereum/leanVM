//! Shared word gadgets and the instruction circuit interface.
//!
//! Port layout and product order define the circuit.
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

/// Word operations on a gate builder.
///
/// A word is an array of wires, low bit first, so its width is part of its type.
///
/// Two words combined bit by bit must then have the same width, or the circuit does not compile.
///
/// A gadget makes its products in a fixed order.
///
/// A gadget's loop order is part of the circuit.
pub(super) trait WordGadgets {
    /// `x ^ y`, bit by bit; no product.
    fn xor_word<const N: usize>(&mut self, x: &[Wire; N], y: &[Wire; N]) -> [Wire; N];

    /// Whether any bit of `x` is set; one product per OR.
    fn any(&mut self, x: &[Wire]) -> Wire;

    /// `-x` if `negative`, else `x`; one product per bit.
    fn negate_if(&mut self, negative: Wire, x: &[Wire; 64]) -> [Wire; 64];

    /// `x`, bits 32 to 63 replaced by bit 31 when `word` is set; one product per high bit.
    fn sext32_if(&mut self, word: Wire, x: &[Wire; 64]) -> [Wire; 64];

    /// Commit `x` as output port `port`.
    fn output_word(&mut self, port: usize, x: &[Wire; 64]);
}

impl WordGadgets for Builder {
    fn xor_word<const N: usize>(&mut self, x: &[Wire; N], y: &[Wire; N]) -> [Wire; N] {
        std::array::from_fn(|i| self.xor(x[i], y[i]))
    }

    fn any(&mut self, x: &[Wire]) -> Wire {
        x.iter().fold(Wire::ZERO, |acc, &bit| self.or(acc, bit))
    }

    fn negate_if(&mut self, negative: Wire, x: &[Wire; 64]) -> [Wire; 64] {
        // Two's complement: (x ^ negative) + negative.
        let flipped = x.map(|bit| self.xor(bit, negative));
        flock::clean::add_with_carry64(self, &flipped, &[Wire::ZERO; 64], negative).0
    }

    fn sext32_if(&mut self, word: Wire, x: &[Wire; 64]) -> [Wire; 64] {
        std::array::from_fn(|i| if i < 32 { x[i] } else { self.mux(word, x[31], x[i]) })
    }

    fn output_word(&mut self, port: usize, x: &[Wire; 64]) {
        for (bit, &wire) in x.iter().enumerate() {
            self.output(port, bit, wire);
        }
    }
}

/// The rows of `z`, `A·z` and `B·z` from a word on, written in order: each row `A·z = a`, `B·z = b`, `z = a·b`.
///
/// A word is stored once it is full, so the tables are written, never read.
pub(crate) struct Products<'a> {
    tables: [&'a mut [u64]; 3],
    word: usize,
    /// Bits of `pending` taken.
    used: u32,
    /// The rows of each table's current word so far.
    pending: [u64; 3],
}

impl<'a> Products<'a> {
    pub(crate) const fn new(tables: [&'a mut [u64]; 3], word: usize) -> Self {
        Self {
            tables,
            word,
            used: 0,
            pending: [0; 3],
        }
    }

    /// The next `bits` rows, at most 64, their `A·z` and `B·z` the low bits of `a` and `b`, which hold no others.
    #[inline(always)]
    pub(crate) fn push(&mut self, a: u64, b: u64, bits: u32) {
        let rows = [a & b, a, b];
        let at = self.used;
        for (pending, row) in self.pending.iter_mut().zip(rows) {
            *pending |= row << at;
        }
        self.used += bits;
        if self.used >= 64 {
            for ((table, pending), row) in self.tables.iter_mut().zip(&mut self.pending).zip(rows) {
                table[self.word] = *pending;
                // `(row >> 1) >> (63 - at)` is `row >> (64 - at)`, the rows that did not fit, with no overflowing shift at `at = 0`.
                *pending = (row >> 1) >> (63 - at);
            }
            self.word += 1;
            self.used -= 64;
        }
    }

    /// The next 192 rows, three per bit of three words: row `3i + k` has `A·z` bit `i` of `a[k]` and `B·z` bit `i` of `b[k]`.
    #[inline(always)]
    pub(crate) fn push_interleaved3(&mut self, a: [u64; 3], b: [u64; 3]) {
        for (a, b) in interleave3(a).into_iter().zip(interleave3(b)) {
            self.push(a, b, 64);
        }
    }

    /// The tables, the last word stored.
    pub(crate) fn finish(mut self) -> [&'a mut [u64]; 3] {
        if self.used > 0 {
            for (table, pending) in self.tables.iter_mut().zip(self.pending) {
                table[self.word] = pending;
            }
        }
        self.tables
    }
}

/// The 192 bits `x0_0, x1_0, x2_0, x0_1, ...` of three words, as three words.
#[inline(always)]
fn interleave3([x, y, w]: [u64; 3]) -> [u64; 3] {
    // Word `j` starts at bit 64j of the sequence, which is bit `64j / 3` of the word at `64j mod 3`.
    [
        spread3(x) | spread3(y) << 1 | spread3(w) << 2,
        spread3(y >> 21) | spread3(w >> 21) << 1 | spread3(x >> 22) << 2,
        spread3(w >> 42) | spread3(x >> 43) << 1 | spread3(y >> 43) << 2,
    ]
}

/// The low 22 bits of `x` at every third bit, from bit 0.
#[cfg_attr(
    not(all(target_arch = "x86_64", target_feature = "bmi2")),
    expect(clippy::missing_const_for_fn, reason = "BMI2's bit deposit is a runtime intrinsic.")
)]
#[inline(always)]
fn spread3(x: u64) -> u64 {
    #[cfg(all(target_arch = "x86_64", target_feature = "bmi2"))]
    {
        // SAFETY: BMI2 is enabled at compile time.
        unsafe { std::arch::x86_64::_pdep_u64(x, 0x9249_2492_4924_9249) }
    }
    // Without it, bits 0 to 20 spread by halving strides, and bit 21 goes to bit 63.
    #[cfg(not(all(target_arch = "x86_64", target_feature = "bmi2")))]
    {
        let top = (x >> 21 & 1) << 63;
        let mut x = x & 0x1f_ffff;
        x = (x | x << 32) & 0x001f_0000_0000_ffff;
        x = (x | x << 16) & 0x001f_0000_ff00_00ff;
        x = (x | x << 8) & 0x100f_00f0_0f00_f00f;
        x = (x | x << 4) & 0x10c3_0c30_c30c_30c3;
        x = (x | x << 2) & 0x1249_2492_4924_9249;
        x | top
    }
}

#[cfg(test)]
mod tests {
    use crate::rv::entry::Class;
    use crate::rv::semantics::tests::edge_word;
    use proptest::strategy::{Strategy, ValueTree};
    use proptest::test_runner::TestRunner;

    /// Every class with a circuit.
    const CLASSES: [Class; 10] = [
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
    ];

    #[test]
    fn instance_sizes_are_pinned() {
        // The log of each instance's bits, which the tables fix before any circuit is built.
        let sizes = CLASSES.map(|class| class.circuit().k_log());
        assert_eq!(sizes, [10, 10, 10, 10, 8, 8, 12, 13, 13, 14]);
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
            let walk = circuit.witness_by_instance(&rows, &rows[0], n_log, |row, z, az, bz| {
                circuit.witness_instance(row, z, az, bz);
            });
            let sliced = circuit.witness_by_walk(&rows, &rows[0], n_log, |row, words| words.copy_from_slice(row));
            assert!(walk == sliced, "the witness tables");
        }
    }
}
