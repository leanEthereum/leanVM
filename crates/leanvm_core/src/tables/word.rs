//! Circuit port selectors and their values on trace rows.

use super::Clock;
use crate::cpu::{Payload, RowRef};
use crate::rv::{Div, Entry, Ext};

/// A circuit port word represented by a virtual table column or a prover hint.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Word {
    /// Row timestamp, supplied to the clock circuit.
    Clock,
    /// Previous timestamp of an indexed memory access.
    Prev(u8),
    /// XOR mask that advances the clock or records an ordering failure.
    Step,
    /// Decoded instruction selectors.
    Flags,
    /// Decoded sign-extended immediate.
    Imm,
    /// First source register's value.
    V1,
    /// Second source register's value.
    V2,
    /// Result written to the destination register.
    Out,
    /// Whether control flow takes the branch or jump, encoded as zero or one.
    Taken,
    /// Load or store address carried on the memory bus.
    Address,
    /// Indexed cell value before the instruction: the one cell of a load or a store, or one of the hash's block.
    Cell(u8),
    /// Indexed cell value after the instruction.
    CellNew(u8),
    /// Destination register's value, used as an extension-field output pointer.
    Dest,
    /// Bit `k` of the flags, a 0 or 1 field element: what a table with no class circuit selects with.
    FlagBit(u8),
    /// Computed bus address of an extension-field limb beyond its pointer ([`Ext::bus_address`]).
    LimbAddress(u8),
    /// Circuit verdict bound to a public zero in the bytecode lookup.
    Bad,
    /// Prover-supplied quotient magnitude, not a table column.
    HintQ,
    /// Prover-supplied remainder magnitude, not a table column.
    HintR,
}

impl Word {
    /// The value this circuit word takes on an executed or padding row.
    ///
    /// The entry and access slots must belong to the row's instruction class.
    ///
    /// Division hints are computed only when requested.
    ///
    /// # Panics
    ///
    /// Panics if an indexed word is out of range or needs extension-field data absent from the row.
    pub(crate) fn value(self, r: RowRef<'_>, entry: &Entry, slots: &[u32]) -> u64 {
        let row = r.row;
        // The operands of an extension-field row, which only its ports read.
        let ext = || match r.payload {
            Payload::Ext(ext) => &ext.instance,
            _ => panic!("{self:?} reads an extension-field row's limbs"),
        };
        match self {
            Self::Clock => row.ts,
            Self::Prev(i) => r.prev()[i as usize],
            Self::Step => Clock { timestamp: row.ts }.step(&r.prev()[..slots.len()], slots),
            Self::Flags => entry.flags,
            Self::Imm => entry.imm,
            Self::V1 => row.v1,
            Self::V2 => row.v2,
            Self::Out => row.out,
            Self::Taken => row.taken as u64,
            Self::Address => row.ram.address,
            Self::Cell(k) => r.cell(k as usize),
            Self::CellNew(k) => r.cell_new(k as usize),
            Self::Dest => ext().pointers[2],
            Self::FlagBit(k) => entry.flags >> k & 1,
            Self::LimbAddress(k) => {
                // Pointer limbs have register ports; only offset limbs have computed addresses.
                assert!(Ext::OFFSET_LIMBS.contains(&(k as usize)), "a computed limb address");
                let x = ext();
                Ext::bus_address(x.pointers, x.flags, k as usize)
            }
            Self::Bad => 0,
            Self::HintQ | Self::HintR => {
                // Only hint ports compute the magnitudes supplied to the division circuit.
                let (quotient, remainder) = Div {
                    flags: entry.flags,
                    v1: row.v1,
                    v2: row.v2,
                }
                .hints();
                if self == Self::HintQ { quotient } else { remainder }
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::super::Clock;
    use super::*;
    use crate::cpu::execute::{ExtRow, HashRow, Row};
    use crate::rv::{Class, InstructionClass, Region, WordAccess};
    use proptest::prelude::*;

    fn row() -> Row {
        // Distinct values expose a port accidentally reading its neighbor.
        Row {
            index: 0,
            ts: Clock::CLOCK_START,
            v1: 11,
            v2: 12,
            out: 13,
            taken: true,
            vd_old: 14,
            ram: WordAccess {
                address: 16,
                old: 17,
                new: 18,
            },
            prev: [
                Clock::SEED_CLOCK,
                Clock::SEED_CLOCK | 1,
                Clock::SEED_CLOCK | 2,
                Clock::SEED_CLOCK | 3,
            ],
        }
    }

    fn entry() -> Entry {
        // A decoded instruction supplies metadata independently of the row's values.
        Entry::decode(
            Class::Alu.nop().expect("the ALU has a no-op").bits(),
            Region::TEXT.base(),
        )
    }

    proptest! {
        #[test]
        fn word_values_preserve_scalar_ports(values in any::<[u64; 8]>(), taken in any::<bool>()) {
            // Each port must preserve all 64 bits of its source, including arbitrary flag words.
            let mut row = row();
            let mut entry = entry();
            [row.ts, entry.flags, entry.imm, row.v1, row.v2, row.out, row.ram.old, row.ram.new] = values;
            row.taken = taken;
            let ports = [Word::Clock, Word::Flags, Word::Imm, Word::V1, Word::V2, Word::Out, Word::Cell(0), Word::CellNew(0)];
            for (port, expected) in ports.into_iter().zip(values) {
                prop_assert_eq!(port.value(RowRef::plain(&row), &entry, &[]), expected);
            }
            prop_assert_eq!(Word::Taken.value(RowRef::plain(&row), &entry, &[]), u64::from(taken));
            prop_assert_eq!(Word::Address.value(RowRef::plain(&row), &entry, &[]), 16);
            prop_assert_eq!(Word::Bad.value(RowRef::plain(&row), &entry, &[]), 0);
        }

        #[test]
        fn word_division_hints_are_unsigned_magnitudes(
            dividend in any::<u64>(), divisor in any::<u64>()
        ) {
            // Wider signed arithmetic gives an independent reference even for i64::MIN.
            for flags in Div::LEGAL {
                let mut row = row();
                let mut entry = entry();
                row.v1 = dividend;
                row.v2 = divisor;
                entry.flags = *flags;
                let magnitude = |v: u64| -> u128 {
                    match (flags & Div::WORD != 0, flags & Div::SIGNED != 0) {
                        (false, false) => u128::from(v),
                        (false, true) => i128::from(v as i64).unsigned_abs(),
                        (true, false) => u128::from(v as u32),
                        (true, true) => i128::from(v as i32).unsigned_abs(),
                    }
                };
                let (n, d) = (magnitude(dividend), magnitude(divisor));
                let (q, r) = n.checked_div(d).map_or((0, 0), |q| (q, n % d));
                prop_assert_eq!(Word::HintQ.value(RowRef::plain(&row), &entry, &[]), q as u64);
                prop_assert_eq!(Word::HintR.value(RowRef::plain(&row), &entry, &[]), r as u64);
            }
        }
    }

    #[test]
    fn word_division_hints_cover_zero_and_signed_boundaries() {
        // Zero divisors have ignored zero hints; signed overflow still has a representable magnitude.
        for (flags, v1, v2, expected) in [
            (0, u64::MAX, 0, (0, 0)),
            (Div::SIGNED, 1 << 63, u64::MAX, (1 << 63, 0)),
            (Div::SIGNED, (-7i64) as u64, 3, (2, 1)),
            (Div::WORD | Div::SIGNED, 1 << 31, u64::MAX, (1 << 31, 0)),
            (Div::WORD, u64::MAX, 1 << 32, (0, 0)),
        ] {
            let mut row = row();
            let mut entry = entry();
            row.v1 = v1;
            row.v2 = v2;
            entry.flags = flags;
            assert_eq!(
                (
                    Word::HintQ.value(RowRef::plain(&row), &entry, &[]),
                    Word::HintR.value(RowRef::plain(&row), &entry, &[])
                ),
                expected
            );
        }
    }

    #[test]
    fn word_hash_cells_replace_only_the_four_output_words() {
        // The compression writes words 4..8, preserving the chaining input and message.
        let row = row();
        let entry = entry();
        let hash = HashRow {
            block: std::array::from_fn(|i| 100 + i as u64),
            out: [200, 201, 202, 203],
            prev: std::array::from_fn(|i| 300 + i as u64),
        };
        let r = RowRef {
            row: &row,
            payload: Payload::Hash(&hash),
        };
        for k in 0..16 {
            assert_eq!(Word::Cell(k).value(r, &entry, &[]), 100 + u64::from(k));
            let expected = if (4..8).contains(&k) {
                196 + u64::from(k)
            } else {
                100 + u64::from(k)
            };
            assert_eq!(Word::CellNew(k).value(r, &entry, &[]), expected);
        }
        for i in 0..18 {
            assert_eq!(Word::Prev(i).value(r, &entry, &[]), 300 + u64::from(i));
        }
    }

    #[test]
    fn word_extension_ports_bind_pointers_flag_bits_and_limb_addresses() {
        // The clock circuit's words of an extension-field row: the destination pointer, the flags' two bits, and
        // where the limbs that are no pointer sit, b's high limbs at register zero in the base-field form.
        for &flags in Ext::LEGAL {
            for pointers in [[0x4000_0000, 0x4000_0020, 0x4000_0040], [u64::MAX - 7; 3]] {
                let row = row();
                let mut entry = entry();
                entry.flags = flags;
                let instance = Ext {
                    flags,
                    pointers,
                    limbs: [0; 9],
                };
                let ext = ExtRow {
                    c: instance.eval(),
                    instance,
                    prev: std::array::from_fn(|i| 400 + i as u64),
                };
                let r = RowRef {
                    row: &row,
                    payload: Payload::Ext(&ext),
                };
                assert_eq!(Word::Dest.value(r, &entry, &[]), pointers[2]);
                assert_eq!(Word::FlagBit(0).value(r, &entry, &[]), flags & Ext::ACCUMULATE);
                assert_eq!(Word::FlagBit(1).value(r, &entry, &[]), flags >> 1);
                for (k, p, offset) in [
                    (1, pointers[0], 8),
                    (2, pointers[0], 16),
                    (4, pointers[1], 8),
                    (5, pointers[1], 16),
                    (7, pointers[2], 8),
                    (8, pointers[2], 16),
                ] {
                    let expected = if flags & Ext::BASE != 0 && (k == 4 || k == 5) {
                        0
                    } else {
                        p.wrapping_add(offset)
                    };
                    assert_eq!(Word::LimbAddress(k).value(r, &entry, &[]), expected);
                }
                for i in 0..12 {
                    assert_eq!(Word::Prev(i).value(r, &entry, &[]), 400 + u64::from(i));
                }
            }
        }
    }

    #[test]
    fn word_clock_step_uses_only_the_class_accesses() {
        let mut row = row();
        let entry = entry();
        let slots = [0, 1, 3];
        // The unused fourth timestamp must not reject an otherwise ordered row.
        row.prev[3] = u64::MAX;
        // Cycle 1 -> 2 flips both low cycle bits, so the XOR step is 3 * 32.
        assert_eq!(Word::Step.value(RowRef::plain(&row), &entry, &slots), 3 * Clock::CYCLE);
        for i in 0..3 {
            assert_eq!(
                Word::Prev(i).value(RowRef::plain(&row), &entry, &slots),
                row.prev[i as usize]
            );
        }
        // Reading one's own push is unordered, even when its value could balance the bus.
        row.prev[1] = row.ts ^ 1;
        assert_eq!(
            Word::Step.value(RowRef::plain(&row), &entry, &slots),
            (3 * Clock::CYCLE) | (1 << Clock::FAIL_BIT)
        );
        // Padding accesses cancel themselves without advancing the clock.
        row.ts = 0;
        row.prev[..3].copy_from_slice(&[0, 1, 3]);
        assert_eq!(Word::Step.value(RowRef::plain(&row), &entry, &slots), 0);
        // A padding row cannot pull a seeded, live tuple.
        row.prev[0] = Clock::SEED_CLOCK;
        assert_eq!(
            Word::Step.value(RowRef::plain(&row), &entry, &slots),
            1 << Clock::FAIL_BIT
        );
    }

    #[test]
    #[should_panic(expected = "Dest reads an extension-field row's limbs")]
    fn word_extension_destination_requires_extension_data() {
        // A class-specific port cannot be supplied by an ordinary row.
        Word::Dest.value(RowRef::plain(&row()), &entry(), &[]);
    }

    #[test]
    #[should_panic(expected = "a computed limb address")]
    fn word_limb_address_rejects_a_pointer_limb() {
        // Limb zero uses the pointer port, not an address computed by the circuit.
        let row = row();
        let instance = Ext {
            flags: 0,
            pointers: [0; 3],
            limbs: [0; 9],
        };
        let ext = ExtRow {
            instance,
            c: instance.eval(),
            prev: [0; 12],
        };
        let r = RowRef {
            row: &row,
            payload: Payload::Ext(&ext),
        };
        Word::LimbAddress(0).value(r, &entry(), &[]);
    }

    #[test]
    #[should_panic]
    fn word_previous_timestamp_rejects_an_out_of_range_index() {
        // Ordinary rows store four previous timestamps at most.
        Word::Prev(4).value(RowRef::plain(&row()), &entry(), &[]);
    }
}
