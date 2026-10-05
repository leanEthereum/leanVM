//! Loads and stores: one access to one 64-bit cell.
//!
//! A double word is its whole cell, so `ld` and `sd` are classes of their own, with no byte to select: [`Ld`] and [`Sd`].

use super::InstructionClass;
use crate::rv::circuits::{ClassCircuit, WordGadgets};
use crate::rv::entry::Class;
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
    const CLASS: Class = Class::Load;

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

    fn input_words(&self) -> Vec<u64> {
        vec![self.v1, self.imm, self.flags, self.cell]
    }

    fn output_words(&(address, value): &(u64, u64)) -> Vec<u64> {
        vec![address, value]
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
    const CLASS: Class = Class::Store;

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

    fn input_words(&self) -> Vec<u64> {
        vec![self.v1, self.v2, self.imm, self.flags, self.cell]
    }

    fn output_words(&(address, cell): &(u64, u64)) -> Vec<u64> {
        vec![address, cell]
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
    const CLASS: Class = Class::Ld;

    /// A double word has no width to select and no extension.
    const LEGAL: &'static [u64] = &[0];

    /// The bus address, and the value read: the cell itself.
    type Output = (u64, u64);

    fn eval(&self) -> (u64, u64) {
        (WordAccess::word_address(self.v1, self.imm), self.cell)
    }

    fn input_words(&self) -> Vec<u64> {
        vec![self.v1, self.imm]
    }

    /// The address alone: the value moved is a column of the table, not a circuit word.
    fn output_words(&(address, _): &(u64, u64)) -> Vec<u64> {
        vec![address]
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
    const CLASS: Class = Class::Sd;

    /// A double word has no width to select.
    const LEGAL: &'static [u64] = &[0];

    /// The bus address, and the cell the store leaves: `v2` itself.
    type Output = (u64, u64);

    fn eval(&self) -> (u64, u64) {
        (WordAccess::word_address(self.v1, self.imm), self.v2)
    }

    fn input_words(&self) -> Vec<u64> {
        vec![self.v1, self.imm]
    }

    /// The address alone: the value moved is a column of the table, not a circuit word.
    fn output_words(&(address, _): &(u64, u64)) -> Vec<u64> {
        vec![address]
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

#[cfg(test)]
mod tests {
    use super::*;
    use crate::rv::semantics::tests::{circuit_matches_reference, edge_word, run};
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
}
