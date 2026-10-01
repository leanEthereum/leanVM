//! Loads and stores: one access to one 64-bit cell.

use super::InstructionClass;
use crate::rv::entry::Class;

/// One load instance: the width and extension in its flags, the address `v1 + imm`, the cell read there.
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

    /// The flag word of a load with function `funct3`.
    ///
    /// - 0 to 2 are `lb`, `lh` and `lw`: signed, of width 2^funct3.
    /// - 3 is `ld`, which has no extension.
    /// - 4 to 6 are `lbu`, `lhu` and `lwu`: unsigned, of width 2^(funct3 - 4).
    ///
    /// Returns `None` for function 7, which is reserved.
    pub const fn flags_of(funct3: u32) -> Option<u64> {
        match funct3 {
            0..=2 => Some(Self::SIGNED | funct3 as u64),
            3 => Some(3),
            4..=6 => Some((funct3 - 4) as u64),
            _ => None,
        }
    }
}

impl InstructionClass for Load {
    const CLASS: Class = Class::Load;

    /// A double word has no extension.
    const LEGAL: &'static [u64] = &[Self::SIGNED, Self::SIGNED | 1, Self::SIGNED | 2, 3, 0, 1, 2];

    /// The bus address, and the value read.
    type Output = (u64, u64);

    fn eval(&self) -> (u64, u64) {
        let address = WordAccess::address(self.v1, self.imm);
        let log_width = self.flags & Self::LOG_WIDTH;
        let bits = 8 << log_width;

        // Bring the addressed byte down to bit 0.
        let x = self.cell >> (8 * (address & 7));

        // Keep the width, extended as the flags say.
        let value = if bits == 64 {
            x
        } else if self.flags & Self::SIGNED != 0 {
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

/// One store instance: the width in its flags, the address `v1 + imm`, the value `v2`, the cell it lands in.
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

    /// Every width.
    const LEGAL: &'static [u64] = &[0, 1, 2, 3];

    /// The bus address, and the cell the store leaves.
    ///
    /// A misaligned store names no cell, so its new cell is never read.
    type Output = (u64, u64);

    fn eval(&self) -> (u64, u64) {
        let address = WordAccess::address(self.v1, self.imm);
        let log_width = self.flags & Self::LOG_WIDTH;
        let bits = 8 << log_width;
        let bus = WordAccess::bus_address(address, log_width);
        if bits == 64 {
            return (bus, self.v2);
        }

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

#[cfg(test)]
mod tests {
    use super::*;
    use crate::rv::semantics::tests::edge_word;
    use proptest::prelude::*;
    use proptest::sample::select;
    use proptest::strategy::BoxedStrategy;

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

    proptest! {
        #[test]
        fn a_load_reads_back_what_a_store_wrote(cell in any::<u64>(), value in edge_word(), offset in 0u64..8, signed in any::<bool>(), log_width in 0u64..4) {
            // Fixture: an aligned access of 2^log_width bytes in one cell.
            let address = 0x4000_0000 + (offset & !((1 << log_width) - 1));
            let bits = 8u32 << log_width;

            // A store, then a load of the same width at the same address.
            let (_, stored) = Store { flags: log_width, v1: address, v2: value, imm: 0, cell }.eval();
            let flags = if signed && log_width < 3 { Load::SIGNED | log_width } else { log_width };
            let (_, got) = Load { flags, v1: address, imm: 0, cell: stored }.eval();

            // The load returns the stored bytes, extended as the flags say.
            let expected = match (bits, signed) {
                (64, _) => value,
                (_, true) => ((value << (64 - bits)) as i64 >> (64 - bits)) as u64,
                (_, false) => value & ((1 << bits) - 1),
            };
            prop_assert_eq!(got, expected);
        }

        #[test]
        fn a_store_keeps_the_bytes_it_does_not_write(cell in any::<u64>(), value in any::<u64>(), offset in 0u64..8, log_width in 0u64..4) {
            // Fixture: an aligned access, and a mask of the bytes it covers.
            let address = offset & !((1 << log_width) - 1);
            let covered = if log_width == 3 { u64::MAX } else { ((1u64 << (8 << log_width)) - 1) << (8 * address) };

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
}
