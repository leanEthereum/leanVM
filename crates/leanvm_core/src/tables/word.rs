//! Circuit port selectors and their values on trace rows.

use super::Clock;
use crate::cpu::RowRef;
use crate::rv::{Alu, Div, Fetched};

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
    /// A compression's fourth register's value: its counter, or a node's bit.
    V3,
    /// Result written to the destination register.
    Out,
    /// Decoded jump offset: the fixed target XOR `pc + 4`, zero for an entry with none.
    Dt,
    /// Decoded fall-through address, `pc + 4`.
    Pc4,
    /// The jump offset when the jump is taken, zero otherwise: what the successor adds to `pc + 4`.
    Jump,
    /// Load or store address carried on the memory bus.
    Address,
    /// Indexed cell value before the instruction: the one cell of a load or a store, or one of the hash's block.
    Cell(u8),
    /// Indexed cell value after the instruction.
    CellNew(u8),
    /// Circuit verdict bound to a public zero in the bytecode lookup.
    Bad,
    /// Prover-supplied quotient magnitude, not a table column.
    HintQ,
    /// Prover-supplied remainder magnitude, not a table column.
    HintR,
}

impl Word {
    /// The value this circuit word takes on an executed or padding row of the entry `at`.
    ///
    /// The entry and access slots must belong to the row's instruction class.
    ///
    /// Division hints are computed only when requested.
    ///
    /// # Panics
    ///
    /// Panics if an indexed word is out of range.
    pub(crate) fn value(self, r: RowRef<'_>, at: Fetched<'_>, slots: &[u32]) -> u64 {
        let (row, entry) = (r.row, at.entry);
        match self {
            Self::Clock => row.ts,
            Self::Prev(i) => r.prev()[i as usize],
            Self::Step => Clock { timestamp: row.ts }.step(&r.prev()[..slots.len()], slots),
            Self::Flags => entry.flags,
            Self::Imm => entry.imm,
            Self::V1 => row.v1,
            Self::V2 => row.v2,
            Self::V3 => r.third(),
            Self::Out => row.out,
            Self::Dt => at.dt,
            Self::Pc4 => at.pc4,
            Self::Jump => Alu {
                flags: entry.flags,
                v1: row.v1,
                v2: row.v2,
                imm: entry.imm,
                dt: at.dt,
                pc4: at.pc4,
            }
            .jump(row.taken),
            Self::Address => row.ram.address,
            Self::Cell(k) => r.cell(k as usize),
            Self::CellNew(k) => r.cell_new(k as usize),
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
    use crate::cpu::execute::{HashRow, Payload, Row};
    use crate::rv::{BlockAccess, Hash};
    use crate::rv::{Class, Entry, InstructionClass, Region, WordAccess};
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
        Entry::new(Class::Alu.nop().expect("the ALU has a no-op"), Region::TEXT.base())
    }

    fn at(entry: &Entry, dt: u64) -> Fetched<'_> {
        Fetched {
            entry,
            pc4: Region::TEXT.base() + 4,
            dt,
        }
    }

    proptest! {
        #[test]
        fn word_values_preserve_scalar_ports(values in any::<[u64; 8]>(), taken in any::<bool>(), dt in any::<u64>()) {
            // Each port must preserve all 64 bits of its source, including arbitrary flag words.
            let mut row = row();
            let mut entry = entry();
            [row.ts, entry.flags, entry.imm, row.v1, row.v2, row.out, row.ram.old, row.ram.new] = values;
            row.taken = taken;
            let ports = [Word::Clock, Word::Flags, Word::Imm, Word::V1, Word::V2, Word::Out, Word::Cell(0), Word::CellNew(0)];
            for (port, expected) in ports.into_iter().zip(values) {
                prop_assert_eq!(port.value(RowRef::plain(&row), at(&entry, dt), &[]), expected);
            }
            // The offset and the link are the bytecode's, and a fixed jump adds that offset only when the row takes it.
            entry.flags = Alu::ALWAYS;
            prop_assert_eq!(Word::Dt.value(RowRef::plain(&row), at(&entry, dt), &[]), dt);
            prop_assert_eq!(Word::Pc4.value(RowRef::plain(&row), at(&entry, dt), &[]), Region::TEXT.base() + 4);
            prop_assert_eq!(Word::Jump.value(RowRef::plain(&row), at(&entry, dt), &[]), if taken { dt } else { 0 });
            prop_assert_eq!(Word::Address.value(RowRef::plain(&row), at(&entry, 0), &[]), 16);
            prop_assert_eq!(Word::Bad.value(RowRef::plain(&row), at(&entry, 0), &[]), 0);
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
                prop_assert_eq!(Word::HintQ.value(RowRef::plain(&row), at(&entry, 0), &[]), q as u64);
                prop_assert_eq!(Word::HintR.value(RowRef::plain(&row), at(&entry, 0), &[]), r as u64);
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
                    Word::HintQ.value(RowRef::plain(&row), at(&entry, 0), &[]),
                    Word::HintR.value(RowRef::plain(&row), at(&entry, 0), &[])
                ),
                expected
            );
        }
    }

    #[test]
    fn word_hash_cells_are_the_words_read_then_the_result() {
        // The compression's words: the chaining value's four, the message's eight, and the result's four.
        let row = row();
        let entry = entry();
        let hash = HashRow {
            access: BlockAccess {
                hash: Hash {
                    flags: 0,
                    x: 77,
                    h: std::array::from_fn(|i| 100 + i as u64),
                    m: std::array::from_fn(|i| 104 + i as u64),
                },
                to: 0,
                old: [0; 4],
                out: [200, 201, 202, 203],
            },
            prev: std::array::from_fn(|i| 300 + i as u64),
        };
        let r = RowRef {
            row: &row,
            payload: Payload::Hash(&hash),
        };
        assert_eq!(Word::V3.value(r, at(&entry, 0), &[]), 77);
        for k in 0..12 {
            assert_eq!(Word::Cell(k).value(r, at(&entry, 0), &[]), 100 + u64::from(k));
        }
        for k in 0..4 {
            assert_eq!(Word::CellNew(k).value(r, at(&entry, 0), &[]), 200 + u64::from(k));
        }
        for i in 0..20 {
            assert_eq!(Word::Prev(i).value(r, at(&entry, 0), &[]), 300 + u64::from(i));
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
        assert_eq!(
            Word::Step.value(RowRef::plain(&row), at(&entry, 0), &slots),
            3 * Clock::CYCLE
        );
        for i in 0..3 {
            assert_eq!(
                Word::Prev(i).value(RowRef::plain(&row), at(&entry, 0), &slots),
                row.prev[i as usize]
            );
        }
        // Reading one's own push is unordered, even when its value could balance the bus.
        row.prev[1] = row.ts ^ 1;
        assert_eq!(
            Word::Step.value(RowRef::plain(&row), at(&entry, 0), &slots),
            (3 * Clock::CYCLE) | (1 << Clock::FAIL_BIT)
        );
        // Padding accesses cancel themselves without advancing the clock.
        row.ts = 0;
        row.prev[..3].copy_from_slice(&[0, 1, 3]);
        assert_eq!(Word::Step.value(RowRef::plain(&row), at(&entry, 0), &slots), 0);
        // A padding row cannot pull a seeded, live tuple.
        row.prev[0] = Clock::SEED_CLOCK;
        assert_eq!(
            Word::Step.value(RowRef::plain(&row), at(&entry, 0), &slots),
            1 << Clock::FAIL_BIT
        );
    }

    #[test]
    #[should_panic]
    fn word_previous_timestamp_rejects_an_out_of_range_index() {
        // Ordinary rows store four previous timestamps at most.
        Word::Prev(4).value(RowRef::plain(&row()), at(&entry(), 0), &[]);
    }
}
