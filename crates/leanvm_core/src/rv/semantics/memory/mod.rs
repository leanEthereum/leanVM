//! Loads and stores: one access to one 64-bit cell.
//!
//! A double word is its whole cell, so `ld` and `sd` are classes of their own, with no byte to select: [`Ld`] and [`Sd`].

use super::InstructionClass;
use crate::rv::circuits::{ClassCircuit, Products, WordGadgets};
use flock::circuit::{Builder, Circuit, Wire};

/// One load instance of 1, 2 or 4 bytes: the width and extension in its flags, the address `v1 + imm`, the cell read there.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Load {
    /// The width, then the extension: one of the legal words.
    pub flags: u64,
    /// The base register's value.
    pub v1: u64,
    /// The offset.
    pub imm: u64,
    /// The 64-bit cell holding the address.
    pub cell: u64,
}

impl Load {
    /// The bits holding the base-two logarithm of the width in bytes.
    pub const LOG_WIDTH: u64 = 0b11;
    /// Sign-extend the value instead of zero-extending it.
    pub const SIGNED: u64 = 1 << 2;
}

impl InstructionClass for Load {
    /// Every width but a double word's, signed or not.
    const LEGAL: &'static [u64] = &[Self::SIGNED, Self::SIGNED | 1, Self::SIGNED | 2, 0, 1, 2];

    /// The bus address, and the value read.
    type Output = (u64, u64);

    fn eval(&self) -> (u64, u64) {
        let address = WordAccess::address(self.v1, self.imm);
        let log_width = self.flags & Self::LOG_WIDTH;
        let bits = 8 << log_width;

        // Bring the addressed byte down to bit 0.
        let x = self.cell >> (8 * (address & 7));

        // Keep the width, extended as the flags say.
        let value = if self.flags & Self::SIGNED != 0 {
            (((x << (64 - bits)) as i64) >> (64 - bits)) as u64
        } else {
            x & ((1 << bits) - 1)
        };
        (WordAccess::bus_address(address, log_width), value)
    }
}

/// One store instance of 1, 2 or 4 bytes: the width in its flags, the address `v1 + imm`, the value `v2`, the cell it lands in.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Store {
    /// The width: one of the legal words.
    pub flags: u64,
    /// The base register's value.
    pub v1: u64,
    /// The value to store.
    pub v2: u64,
    /// The offset.
    pub imm: u64,
    /// The 64-bit cell holding the address.
    pub cell: u64,
}

impl Store {
    /// The bits holding the base-two logarithm of the width in bytes.
    pub const LOG_WIDTH: u64 = 0b11;
}

impl InstructionClass for Store {
    /// Every width but a double word's.
    const LEGAL: &'static [u64] = &[0, 1, 2];

    /// The bus address, and the cell the store leaves.
    ///
    /// A misaligned store names no cell, so its new cell is never read.
    type Output = (u64, u64);

    fn eval(&self) -> (u64, u64) {
        let address = WordAccess::address(self.v1, self.imm);
        let log_width = self.flags & Self::LOG_WIDTH;
        let bits = 8 << log_width;
        let bus = WordAccess::bus_address(address, log_width);

        // Replace the addressed bytes, keep the others.
        let mask = ((1u64 << bits) - 1) << (8 * (address & 7));
        (bus, (self.cell & !mask) | ((self.v2 << (8 * (address & 7))) & mask))
    }
}

/// One `ld` instance: the address `v1 + imm`, and the cell read there, which is the value.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Ld {
    /// The base register's value.
    pub v1: u64,
    /// The offset.
    pub imm: u64,
    /// The 64-bit cell at the address.
    pub cell: u64,
}

impl InstructionClass for Ld {
    /// A double word has no width to select and no extension.
    const LEGAL: &'static [u64] = &[0];

    /// The bus address, and the value read: the cell itself.
    type Output = (u64, u64);

    fn eval(&self) -> (u64, u64) {
        (WordAccess::word_address(self.v1, self.imm), self.cell)
    }
}

/// One `sd` instance: the address `v1 + imm`, and the value `v2`, which is the cell the store leaves.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Sd {
    /// The base register's value.
    pub v1: u64,
    /// The value to store.
    pub v2: u64,
    /// The offset.
    pub imm: u64,
}

impl InstructionClass for Sd {
    /// A double word has no width to select.
    const LEGAL: &'static [u64] = &[0];

    /// The bus address, and the cell the store leaves: `v2` itself.
    type Output = (u64, u64);

    fn eval(&self) -> (u64, u64) {
        (WordAccess::word_address(self.v1, self.imm), self.v2)
    }
}

/// A load's or a store's access to one memory cell.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct WordAccess {
    /// What goes on the memory bus: the cell's byte address, for an aligned access.
    pub address: u64,
    /// The cell before the access.
    pub old: u64,
    /// The cell after the access: the old value for a load.
    pub new: u64,
}

impl WordAccess {
    /// A load's or a store's byte address: `v1 + imm`.
    pub const fn address(v1: u64, imm: u64) -> u64 {
        v1.wrapping_add(imm)
    }

    /// An `ld`'s or an `sd`'s bus address: `v1 + imm` itself, a double word's misalignment bits being all three low ones.
    pub const fn word_address(v1: u64, imm: u64) -> u64 {
        Self::bus_address(Self::address(v1, imm), 3)
    }

    /// What an access of `2^log_width` bytes at `address` puts on the memory bus.
    ///
    /// That is the byte address of its 64-bit cell, with the bits that misalign the access kept.
    ///
    /// A cell's address is a multiple of 8.
    ///
    /// So a misaligned access names no cell at all, and the bus cannot balance.
    ///
    /// For example, a 4-byte load:
    ///
    /// - at `0x...08` puts `0x...08` on the bus, its cell;
    /// - at `0x...0c` also puts `0x...08` on the bus, the same cell's high half;
    /// - at `0x...0a` puts `0x...0a` on the bus, which is no cell.
    pub const fn bus_address(address: u64, log_width: u64) -> u64 {
        (address & !7) | (address & ((1 << log_width) - 1))
    }

    /// Whether an access of `2^log_width` bytes at `address` is naturally aligned.
    pub const fn is_aligned(address: u64, log_width: u64) -> bool {
        address & ((1 << log_width) - 1) == 0
    }
}

impl ClassCircuit for Load {
    /// The load: `(v1, imm, flags, cell) -> (address, out)`.
    ///
    /// The address is what goes on the memory bus, and `cell` is the word read there.
    ///
    /// - The cell shifts right until the addressed byte is at the bottom.
    /// - The output keeps the access's width, extended by its top bit if the load is signed.
    fn circuit() -> Circuit {
        let mut c = Builder::new(&[64, 64, 3, 64], &[64, 64]);
        let (v1, imm, flags, cell) = (c.input(0), c.input(1), c.input(2), c.input(3));
        let address = c.add_wrapping(&v1, &imm);
        let [ge2, ge4] = c.width_thresholds(&flags[..2]);
        let bus = c.bus_address(&address, [ge2, ge4]);

        // At most 4 bytes are loaded, so only the low half of the shifted cell is read.
        let value = c.shift_bytes(&cell, &address[..3], false, 32);

        // The extension: the value's top bit, where the width places it, if the load is signed.
        //
        //     width 1   bit 7
        //     width 2   bit 15
        //     width 4   bit 31
        let (w1, w2, w4) = (c.not(ge2), c.xor(ge2, ge4), ge4);
        let sign = [(w1, 7), (w2, 15), (w4, 31)]
            .into_iter()
            .fold(None, |acc, (width, bit)| {
                let term = c.and(width, value[bit]);
                c.xor(acc, term)
            });
        let extension = c.and(flags[2], sign);
        c.output_word(0, &bus);

        // Each byte of the value above the first is the value's if the width reaches it, else the extension.
        for (i, &bit) in value.iter().enumerate() {
            let wire = match i {
                0..8 => bit,
                8..16 => c.mux(ge2, bit, extension),
                _ => c.mux(ge4, bit, extension),
            };
            c.output(1, i, wire);
        }

        // Above the value, past every width here, is the extension.
        for i in value.len()..64 {
            c.output(1, i, extension);
        }
        c.finish()
    }
}

impl ClassCircuit for Store {
    /// The store: `(v1, v2, imm, flags, cell) -> (address, new cell)`.
    ///
    /// The value shifts up to the addressed bytes, which replace the cell's.
    ///
    /// The cell's other bytes are kept.
    fn circuit() -> Circuit {
        let mut c = Builder::new(&[64, 64, 64, 2, 64], &[64, 64]);
        let (v1, v2, imm, flags, cell) = (c.input(0), c.input(1), c.input(2), c.input(3), c.input(4));
        let address = c.add_wrapping(&v1, &imm);
        let [ge2, ge4] = c.width_thresholds(&flags);
        let bus = c.bus_address(&address, [ge2, ge4]);

        // At most 4 bytes are stored, so the high half of `v2` is never written.
        let low: Vec<Wire> = (0..64).map(|i| if i < 32 { v2[i] } else { None }).collect();
        let value = c.shift_bytes(&low, &address[..3], true, 64);

        // Byte j is written when it shares the access's block of 2^log_width bytes.
        //
        // That is: bit k of j equals bit k of the address, wherever the width does not span both.
        //
        // No width spans bit 2, so there the byte's bit must equal the address's.
        let spans: [[Wire; 2]; 3] = std::array::from_fn(|k| {
            let is_zero = c.not(address[k]);
            match [ge2, ge4].get(k) {
                Some(&threshold) => [c.or(is_zero, threshold), c.or(address[k], threshold)],
                None => [is_zero, address[k]],
            }
        });
        c.output_word(0, &bus);

        // Each byte is the value's if written, else the cell's.
        for j in 0..8 {
            let low = c.and(spans[0][j & 1], spans[1][(j >> 1) & 1]);
            let written = c.and(low, spans[2][j >> 2]);
            for i in 8 * j..8 * j + 8 {
                let wire = c.mux(written, value[i], cell[i]);
                c.output(1, i, wire);
            }
        }
        c.finish()
    }
}

impl ClassCircuit for Ld {
    /// The doubleword access: `(v1, imm) -> address`, the adder alone.
    ///
    /// The value moved is no word of it: the table puts the same column in the register's tuple and in the cell's.
    ///
    /// [`Sd`] shares it.
    fn circuit() -> Circuit {
        let mut c = Builder::new(&[64, 64], &[64]);
        let (v1, imm) = (c.input(0), c.input(1));
        let address = c.add_wrapping(&v1, &imm);
        c.output_word(0, &address);
        c.finish()
    }
}

impl ClassCircuit for Sd {
    /// [`Ld`]'s circuit: a store of a double word names its cell as a load does.
    fn circuit() -> Circuit {
        Ld::circuit()
    }
}

/// All ones if `bit` is set, else zero.
const fn all(bit: u64) -> u64 {
    (bit & 1).wrapping_neg()
}

/// The address `v1 + imm` and the rows of its adder, which makes no carry out of the top bit:
/// `A·z = v1 ^ c`, `B·z = imm ^ c` on bits 0 to 62, `c` the carries.
fn address_rows(v1: u64, imm: u64, rows: &mut Products<'_>) -> u64 {
    let address = v1.wrapping_add(imm);
    let carries = address ^ v1 ^ imm;
    rows.push((v1 ^ carries) & (u64::MAX >> 1), (imm ^ carries) & (u64::MAX >> 1), 63);
    address
}

/// The bus address of a load or a store of `2^log_width` bytes, `ge2` and `ge4` the width's thresholds, and its two rows.
fn bus_rows(address: u64, ge2: u64, ge4: u64, rows: &mut Products<'_>) -> u64 {
    let (a0, a1) = (address & 1, address >> 1 & 1);
    rows.push(a0, ge2, 1);
    rows.push(a1, ge4, 1);
    address & !7 | a0 & ge2 | (a1 & ge4) << 1
}

impl Load {
    /// One instance of the circuit's witness by word arithmetic: what the walk of [`Load::circuit`] writes, into zeroed buffers.
    ///
    /// After the adder and the bus address, the cell's right shift by `8 * (address & 7)` bits, three byte stages of `A·z` the stage's
    /// address bit and `B·z` the shifted and kept words' difference, the sign by width, the extension, and the muxes of bytes 1 to 3.
    pub(crate) fn witness(inputs: &[u64], z: &mut [u64], az: &mut [u64], bz: &mut [u64]) {
        let (v1, imm, flags, cell) = (inputs[0], inputs[1], inputs[2] & 7, inputs[3]);
        let (ge2, ge4) = ((flags ^ flags >> 1) & 1, flags >> 1 & 1);
        let mut rows = Products::new([&mut z[6..], &mut az[6..], &mut bz[6..]], 0);
        rows.push(1, 1, 1);
        let address = address_rows(v1, imm, &mut rows);
        let bus = bus_rows(address, ge2, ge4, &mut rows);

        // The cell, right by whole bytes; the last stage makes only the low 32 bits.
        let mut value = cell;
        for (stage, bits) in [(0, 64), (1, 64), (2, 32)] {
            let (by, s) = (8 << stage, address >> stage & 1);
            let mask = u64::MAX >> (64 - bits);
            let shifted = value >> by;
            rows.push(all(s) & mask, (shifted ^ value) & mask, bits);
            value = (if s == 1 { shifted } else { value }) & mask;
        }

        let (w1, w2, w4) = (ge2 ^ 1, ge2 ^ ge4, ge4);
        let mut sign = 0;
        for (width, bit) in [(w1, 7), (w2, 15), (w4, 31)] {
            let top = value >> bit & 1;
            rows.push(width, top, 1);
            sign ^= width & top;
        }
        let signed = flags >> 2;
        rows.push(signed, sign, 1);
        let extension = all(signed & sign);
        rows.push(all(ge2) & 0xff, (value >> 8 ^ extension) & 0xff, 8);
        rows.push(all(ge4) & 0xffff, (value >> 16 ^ extension) & 0xffff, 16);
        rows.finish();
        let out = value & 0xff
            | (if ge2 == 1 { value } else { extension }) & 0xff00
            | (if ge4 == 1 { value } else { extension }) & 0xffff_0000
            | extension & !0xffff_ffff;

        let ports = [
            (v1, u64::MAX),
            (imm, u64::MAX),
            (flags, 7),
            (cell, u64::MAX),
            (bus, !4),
            (out, u64::MAX),
        ];
        for (i, (word, wired)) in ports.into_iter().enumerate() {
            (z[i], az[i], bz[i]) = (word, word, wired);
        }
    }
}

impl Store {
    /// One instance of the circuit's witness by word arithmetic: what the walk of [`Store::circuit`] writes, into zeroed buffers.
    ///
    /// After the adder and the bus address, the low half of `v2`'s left shift by `8 * (address & 7)` bits (three byte stages,
    /// each making the bits a shifted or a kept bit can reach), the four ORs of the address's low bits with the thresholds,
    /// then per byte whether it is written and its eight muxes.
    pub(crate) fn witness(inputs: &[u64], z: &mut [u64], az: &mut [u64], bz: &mut [u64]) {
        let (v1, v2, imm, flags, cell) = (inputs[0], inputs[1], inputs[2], inputs[3] & 3, inputs[4]);
        let (ge2, ge4) = ((flags ^ flags >> 1) & 1, flags >> 1);
        let mut rows = Products::new([&mut z[7..], &mut az[7..], &mut bz[7..]], 0);
        rows.push(1, 1, 1);
        let address = address_rows(v1, imm, &mut rows);
        let bus = bus_rows(address, ge2, ge4, &mut rows);

        // The low half of `v2`, left by whole bytes: stage `k` makes the bits below `32 + 8 * (2^(k + 1) - 1)`, at most 64.
        let mut value = v2 & 0xffff_ffff;
        for (stage, bits) in [(0, 40), (1, 56), (2, 64)] {
            let (by, s) = (8 << stage, address >> stage & 1);
            let mask = u64::MAX >> (64 - bits);
            let shifted = value << by;
            rows.push(all(s) & mask, (shifted ^ value) & mask, bits);
            value = if s == 1 { shifted } else { value };
        }

        // Bit `k` of a written byte's index is the address's, wherever the width does not span it.
        let (a0, a1, a2) = (address & 1, address >> 1 & 1, address >> 2 & 1);
        let mut spans = [[0; 2]; 3];
        for (k, (a, threshold)) in [(a0, ge2), (a1, ge4)].into_iter().enumerate() {
            rows.push(a ^ 1, threshold, 1);
            rows.push(a, threshold, 1);
            spans[k] = [a ^ 1 | threshold, a | threshold];
        }
        spans[2] = [a2 ^ 1, a2];
        let mut new = 0;
        for j in 0..8 {
            let low = spans[0][j & 1] & spans[1][j >> 1 & 1];
            rows.push(spans[0][j & 1], spans[1][j >> 1 & 1], 1);
            rows.push(low, spans[2][j >> 2], 1);
            let written = all(low & spans[2][j >> 2]);
            let byte = 0xff << (8 * j);
            rows.push(written & 0xff, (value ^ cell) >> (8 * j) & 0xff, 8);
            new |= (written & value | !written & cell) & byte;
        }
        rows.finish();

        let ports = [
            (v1, u64::MAX),
            (v2, u64::MAX),
            (imm, u64::MAX),
            (flags, 3),
            (cell, u64::MAX),
            (bus, !4),
            (new, u64::MAX),
        ];
        for (i, (word, wired)) in ports.into_iter().enumerate() {
            (z[i], az[i], bz[i]) = (word, word, wired);
        }
    }
}

impl Ld {
    /// One instance of the circuit's witness by word arithmetic, [`Sd`]'s too: what the walk of [`Ld::circuit`] writes, into zeroed buffers.
    ///
    /// The ports `v1`, `imm` and the address, the constant, then the adder's rows.
    pub(crate) fn witness(inputs: &[u64], z: &mut [u64], az: &mut [u64], bz: &mut [u64]) {
        let (v1, imm) = (inputs[0], inputs[1]);
        let mut rows = Products::new([&mut z[3..], &mut az[3..], &mut bz[3..]], 0);
        rows.push(1, 1, 1);
        let address = address_rows(v1, imm, &mut rows);
        rows.finish();
        for (i, word) in [v1, imm, address].into_iter().enumerate() {
            (z[i], az[i], bz[i]) = (word, word, u64::MAX);
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::rv::Class;
    use crate::rv::semantics::tests::{
        EDGES, Ports, circuit_matches_reference, edge_word, grid, run, word_witness_is_the_walk,
    };
    use proptest::prelude::*;
    use proptest::sample::select;
    use proptest::strategy::BoxedStrategy;
    use std::sync::LazyLock;

    /// Any load instance, aligned half the time, which a random address seldom is.
    impl Arbitrary for Load {
        type Parameters = ();
        type Strategy = BoxedStrategy<Self>;

        fn arbitrary_with((): ()) -> Self::Strategy {
            (
                select(Self::LEGAL),
                edge_word(),
                0u64..4096,
                any::<u64>(),
                any::<bool>(),
            )
                .prop_map(|(flags, v1, imm, cell, aligned)| {
                    let mask = (1 << (flags & Self::LOG_WIDTH)) - 1;
                    let (v1, imm) = if aligned { (v1 & !mask, imm & !7) } else { (v1, imm) };
                    Self { flags, v1, imm, cell }
                })
                .boxed()
        }
    }

    /// Any aligned store instance.
    ///
    /// A misaligned store names no cell, so its new cell is never read and need not agree.
    impl Arbitrary for Store {
        type Parameters = ();
        type Strategy = BoxedStrategy<Self>;

        fn arbitrary_with((): ()) -> Self::Strategy {
            (select(Self::LEGAL), edge_word(), edge_word(), 0u64..4096, any::<u64>())
                .prop_map(|(flags, v1, v2, imm, cell)| Self {
                    flags,
                    v1: v1 & !((1 << flags) - 1),
                    v2,
                    imm: imm & !7,
                    cell,
                })
                .boxed()
        }
    }

    /// Any `ld` instance: any two words, so the adder is checked whole, carries and misalignment bits included.
    impl Arbitrary for Ld {
        type Parameters = ();
        type Strategy = BoxedStrategy<Self>;

        fn arbitrary_with((): ()) -> Self::Strategy {
            (edge_word(), edge_word(), any::<u64>())
                .prop_map(|(v1, imm, cell)| Self { v1, imm, cell })
                .boxed()
        }
    }

    /// Any `sd` instance: any two words, so the adder is checked whole, carries and misalignment bits included.
    impl Arbitrary for Sd {
        type Parameters = ();
        type Strategy = BoxedStrategy<Self>;

        fn arbitrary_with((): ()) -> Self::Strategy {
            (edge_word(), any::<u64>(), edge_word())
                .prop_map(|(v1, v2, imm)| Self { v1, v2, imm })
                .boxed()
        }
    }

    proptest! {
        #[test]
        fn a_load_reads_back_what_a_store_wrote(cell in any::<u64>(), value in edge_word(), offset in 0u64..8, signed in any::<bool>(), log_width in 0u64..3) {
            // Fixture: an aligned access of 2^log_width bytes in one cell.
            let address = 0x4000_0000 + (offset & !((1 << log_width) - 1));
            let bits = 8u32 << log_width;

            // A store, then a load of the same width at the same address.
            let (_, stored) = Store { flags: log_width, v1: address, v2: value, imm: 0, cell }.eval();
            let flags = if signed { Load::SIGNED | log_width } else { log_width };
            let (_, got) = Load { flags, v1: address, imm: 0, cell: stored }.eval();

            // The load returns the stored bytes, extended as the flags say.
            let expected = if signed {
                ((value << (64 - bits)) as i64 >> (64 - bits)) as u64
            } else {
                value & ((1 << bits) - 1)
            };
            prop_assert_eq!(got, expected);
        }

        #[test]
        fn a_store_keeps_the_bytes_it_does_not_write(cell in any::<u64>(), value in any::<u64>(), offset in 0u64..8, log_width in 0u64..3) {
            // Fixture: an aligned access, and a mask of the bytes it covers.
            let address = offset & !((1 << log_width) - 1);
            let covered = ((1u64 << (8 << log_width)) - 1) << (8 * address);

            // Outside the access, the cell is unchanged.
            let (_, new) = Store { flags: log_width, v1: address, v2: value, imm: 0, cell }.eval();
            prop_assert_eq!(new & !covered, cell & !covered);
        }

        #[test]
        fn the_bus_address_is_the_cell_exactly_when_aligned(address in any::<u64>(), log_width in 0u64..4) {
            // An aligned access names its cell, a misaligned one names no multiple of 8.
            let bus = WordAccess::bus_address(address, log_width);
            prop_assert_eq!(bus.is_multiple_of(8), WordAccess::is_aligned(address, log_width));
            prop_assert_eq!(bus & !7, address & !7);
        }
    }

    static STORE: LazyLock<Circuit> = LazyLock::new(Store::circuit);
    static WORD: LazyLock<Circuit> = LazyLock::new(Ld::circuit);

    #[test]
    fn load_circuit_matches_the_reference() {
        // Legal flags and edge-biased operands pin the gate list to the reference function.
        circuit_matches_reference::<Load>(4096);
    }

    #[test]
    fn store_circuit_matches_the_reference() {
        // Legal flags and edge-biased operands pin the gate list to the reference function.
        circuit_matches_reference::<Store>(4096);
    }

    #[test]
    fn doubleword_circuits_match_the_reference() {
        // Any two words pin the shared adder to the reference's bus address.
        circuit_matches_reference::<Ld>(4096);
        circuit_matches_reference::<Sd>(4096);
    }

    /// Offsets that put an edge base at every byte of its cell, aligned or not, and carry through the whole adder.
    const OFFSETS: [u64; 11] = [0, 1, 2, 3, 4, 5, 6, 7, u64::MAX, u64::MAX - 6, 1 << 63];

    /// Cells and stored values: zero, all ones, every byte's sign bit set or clear, and two words with distinct bytes.
    const BYTES: [u64; 6] = [
        0,
        u64::MAX,
        0x8080_8080_8080_8080,
        0x7f7f_7f7f_7f7f_7f7f,
        0x0123_4567_89ab_cdef,
        0xfedc_ba98_7654_3210,
    ];

    #[test]
    fn the_word_witnesses_are_the_gate_walk() {
        // Every legal flag word at every byte of a cell, signed or not, so each width's misalignments and sign bits are walked.
        word_witness_is_the_walk::<Load>(Load::witness, grid(&[&EDGES, &OFFSETS, Load::LEGAL, &BYTES]));
        word_witness_is_the_walk::<Store>(
            Store::witness,
            grid(&[&EDGES, &BYTES, &OFFSETS, Store::LEGAL, &BYTES[..3]]),
        );
        let addresses = [grid(&[&EDGES, &OFFSETS]), grid(&[&EDGES, &EDGES])].concat();
        word_witness_is_the_walk::<Ld>(Ld::witness, addresses.clone());
        word_witness_is_the_walk::<Sd>(Ld::witness, addresses);
    }

    proptest! {
        #[test]
        fn a_misaligned_store_names_no_cell(store in any::<Store>(), offset in 1u64..8) {
            // Mutation: misalign an aligned store, by an offset its width does not divide.
            let store = Store { v1: store.v1 | offset, ..store };
            let log_width = store.flags & Store::LOG_WIDTH;
            prop_assume!(!WordAccess::is_aligned(store.v1.wrapping_add(store.imm), log_width));

            // The bus address is still the reference's, and names no cell.
            let (address, _) = store.eval();
            prop_assert_eq!(run(&STORE, &store.input_words(), 1), vec![address]);
            prop_assert!(!address.is_multiple_of(8));
        }

        #[test]
        fn a_misaligned_doubleword_names_no_cell(v1 in edge_word(), imm in edge_word()) {
            // Invariant: a double word's misalignment bits are all three low ones, so its bus address is the sum itself.
            let address = WordAccess::address(v1, imm);
            let bus = run(&WORD, &[v1, imm], 1)[0];
            prop_assert_eq!(bus, address);
            prop_assert_eq!(bus.is_multiple_of(8), WordAccess::is_aligned(address, 3));
        }
    }

    impl Ports for Load {
        const CLASS: Class = Class::Load;

        fn input_words(&self) -> Vec<u64> {
            vec![self.v1, self.imm, self.flags, self.cell]
        }

        fn output_words(&self, &(address, value): &(u64, u64)) -> Vec<u64> {
            vec![address, value]
        }
    }

    impl Ports for Store {
        const CLASS: Class = Class::Store;

        fn input_words(&self) -> Vec<u64> {
            vec![self.v1, self.v2, self.imm, self.flags, self.cell]
        }

        fn output_words(&self, &(address, cell): &(u64, u64)) -> Vec<u64> {
            vec![address, cell]
        }
    }

    impl Ports for Ld {
        const CLASS: Class = Class::Ld;

        fn input_words(&self) -> Vec<u64> {
            vec![self.v1, self.imm]
        }

        // The address alone: the value moved is a column of the table, not a circuit word.
        fn output_words(&self, &(address, _): &(u64, u64)) -> Vec<u64> {
            vec![address]
        }
    }

    impl Ports for Sd {
        const CLASS: Class = Class::Sd;

        fn input_words(&self) -> Vec<u64> {
            vec![self.v1, self.imm]
        }

        // The address alone: the value moved is a column of the table, not a circuit word.
        fn output_words(&self, &(address, _): &(u64, u64)) -> Vec<u64> {
            vec![address]
        }
    }
}
