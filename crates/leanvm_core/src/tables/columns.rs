//! Local column allocation and the aliases used by memory moves.

use super::{ClassSpec, Control, Ram, Word};
use crate::leaf::Coord::{self, Col};
use crate::rv::{Ext, Hash};

/// The `rs2` read's columns: the register's number and what it held.
#[derive(Clone, Copy)]
pub(super) struct SourceColumns {
    /// Second source register number.
    pub(super) a2: usize,

    /// Second source register value.
    pub(super) v2: usize,
}

/// The destination read's columns: the register's number and the address it holds.
#[derive(Clone, Copy)]
pub(super) struct PointerColumns {
    /// Destination register number.
    pub(super) ad: usize,

    /// Address held in the destination register.
    pub(super) vd: usize,
}

/// Columns binding a destination register write.
#[derive(Clone, Copy)]
pub(super) struct DestinationColumns {
    /// Destination register number.
    pub(super) ad: usize,

    /// Destination value before the write.
    pub(super) vd_old: usize,

    /// Result value, or a shared memory-cell column.
    pub(super) out: usize,
}

/// Columns of a class with branches or jumps, a jump's exit included.
#[derive(Clone, Copy)]
pub(super) struct ControlColumns {
    /// Decoded jump offset, a circuit input.
    pub(super) dt: usize,

    /// The offset when the jump is taken, zero otherwise: a circuit output.
    pub(super) jump: usize,

    /// Selector for the exit instruction: a jump's column, a branch's constant zero.
    pub(super) exit: Option<usize>,
}

impl ControlColumns {
    /// The successor, `pc + 4` plus the jump: the fall-through or the target.
    pub(super) fn next_pc(self, pc4: usize) -> Coord {
        Coord::Sum(vec![Col(pc4), Col(self.jump)])
    }
}

/// Columns binding a load or store to one memory cell.
#[derive(Clone, Copy)]
pub(super) struct MemoryColumns {
    /// Effective bus address.
    pub(super) address: usize,

    /// Memory value before the access.
    pub(super) cell: usize,

    /// First replacement value column.
    pub(super) new: usize,
}

/// Columns for a hash block and its four output words.
#[derive(Clone, Copy)]
pub(super) struct BlockColumns {
    /// First hash block word column.
    pub(super) words: usize,

    /// Result value, or a shared memory-cell column.
    pub(super) out: usize,
}

impl BlockColumns {
    /// What the row leaves in word `k` of its block.
    pub(super) const fn left(&self, k: usize) -> usize {
        match k.wrapping_sub(Hash::OUT as usize / 8) {
            j if j < 4 => self.out + j,
            _ => self.words + k,
        }
    }
}

/// Columns for extension-field operands, output, and computed limb locations.
///
/// The limbs and `c`'s new limbs are committed columns, which the table's identities relate; the addresses are the
/// clock circuit's words.
#[derive(Clone, Copy)]
pub(super) struct LimbColumns {
    /// First operand limb column.
    pub(super) limbs: usize,

    /// First replacement value column.
    pub(super) new: usize,

    /// First computed limb address column.
    pub(super) addresses: usize,
}

impl LimbColumns {
    /// The column of limb `k`'s computed bus address: every limb but an operand's first.
    pub(super) fn computed(&self, k: usize) -> Option<usize> {
        let i = Ext::OFFSET_LIMBS.iter().position(|&j| j == k)?;
        Some(self.addresses + i)
    }

    /// The bus address of limb `k`: the operand's pointer for its first limb, else what the clock circuit computes.
    pub(super) fn address(&self, k: usize, pointers: [usize; 3]) -> usize {
        self.computed(k).unwrap_or(pointers[k / 3])
    }

    /// What the row leaves in limb `k`: `c`'s are rewritten.
    pub(super) const fn left(&self, k: usize) -> usize {
        if k >= 6 { self.new + k - 6 } else { self.limbs + k }
    }
}

/// Local column layout, including shared columns for unchanged doubleword moves.
///
/// Allocation order is protocol data mirrored by the Python verifier.
#[derive(Clone, Copy)]
pub(super) struct Columns {
    /// Current instruction address.
    pub(super) pc: usize,

    /// Current row timestamp.
    pub(super) ts: usize,

    /// First source register number.
    pub(super) a1: usize,

    /// Fall-through instruction address, `pc + 4`.
    pub(super) pc4: usize,

    /// First source register value.
    pub(super) v1: usize,

    /// Optional decoded selector word.
    pub(super) flags: Option<usize>,

    /// Optional second source register read.
    pub(super) rs2: Option<SourceColumns>,

    /// Optional destination register write.
    pub(super) rd: Option<DestinationColumns>,

    /// Optional destination register used as an address.
    pub(super) pointer: Option<PointerColumns>,

    /// Optional control-flow columns.
    pub(super) control: Option<ControlColumns>,

    /// Optional decoded immediate.
    pub(super) imm: Option<usize>,

    /// Optional single-cell memory access.
    pub(super) ram: Option<MemoryColumns>,

    /// Optional hash block access.
    pub(super) block: Option<BlockColumns>,

    /// Optional extension-field memory accesses.
    pub(super) limbs: Option<LimbColumns>,

    /// The flags' bits, one column each, for a table with no class circuit.
    pub(super) flag_bits: Option<usize>,

    /// Circuit verdict bound to public zero.
    pub(super) bad: Option<usize>,

    /// The first access's previous timestamp, the others following it.
    pub(super) prev: usize,

    /// XOR mask advancing the row timestamp.
    pub(super) step: usize,
}

impl Columns {
    /// Allocate the fixed layout in protocol order, retaining aliases for doubleword moves.
    pub(super) fn new(spec: &ClassSpec) -> Self {
        let mut allocator = ColumnAllocator::default();
        let (pc, ts, a1, pc4, v1) = (
            allocator.allocate(1),
            allocator.allocate(1),
            allocator.allocate(1),
            allocator.allocate(1),
            allocator.allocate(1),
        );
        let flags = spec.words().any(|w| w == Word::Flags).then(|| allocator.allocate(1));
        let rs2 = spec.reads_rs2.then(|| SourceColumns {
            a2: allocator.allocate(1),
            v2: allocator.allocate(1),
        });
        // A doubleword load's `rd` receives its cell, which is a column further on, and a jump's its link, `pc + 4`.
        let rd = spec.writes_rd.then(|| {
            (
                allocator.allocate(1),
                allocator.allocate(1),
                (!spec.copies && spec.control != Control::Jump).then(|| allocator.allocate(1)),
            )
        });
        let pointer = spec.reads_rd.then(|| PointerColumns {
            ad: allocator.allocate(1),
            vd: allocator.allocate(1),
        });
        let control = (spec.control != Control::None).then(|| ControlColumns {
            dt: allocator.allocate(1),
            jump: allocator.allocate(1),
            exit: (spec.control == Control::Jump).then(|| allocator.allocate(1)),
        });
        let imm = spec.words().any(|w| w == Word::Imm).then(|| allocator.allocate(1));
        let (ram, block) = match spec.ram {
            Ram::None | Ram::Limbs => (None, None),
            Ram::Read | Ram::Write => {
                let (address, cell) = (allocator.allocate(1), allocator.allocate(1));
                let new = match (spec.ram, rs2) {
                    (Ram::Read, _) => cell,
                    (Ram::Write, Some(rs2)) if spec.copies => rs2.v2,
                    _ => allocator.allocate(1),
                };
                (Some(MemoryColumns { address, cell, new }), None)
            }
            Ram::Block => {
                let words = allocator.allocate(Hash::WORDS);
                (
                    None,
                    Some(BlockColumns {
                        words,
                        out: allocator.allocate(4),
                    }),
                )
            }
        };
        let rd = rd.map(|(ad, vd_old, out)| DestinationColumns {
            ad,
            vd_old,
            out: out.unwrap_or_else(|| ram.map_or(pc4, |ram| ram.cell)),
        });
        let limbs = (spec.ram == Ram::Limbs).then(|| LimbColumns {
            limbs: allocator.allocate(Ext::LIMBS),
            new: allocator.allocate(3),
            addresses: allocator.allocate(Ext::OFFSET_LIMBS.len()),
        });
        let n_flag_bits = spec.words().filter(|w| matches!(w, Word::FlagBit(_))).count();
        let flag_bits = (n_flag_bits > 0).then(|| allocator.allocate(n_flag_bits));
        let bad = spec.words().any(|w| w == Word::Bad).then(|| allocator.allocate(1));
        let (prev, step) = (allocator.allocate(spec.n_accesses()), allocator.allocate(1));
        Self {
            pc,
            ts,
            a1,
            pc4,
            v1,
            flags,
            rs2,
            rd,
            pointer,
            control,
            imm,
            ram,
            block,
            limbs,
            flag_bits,
            bad,
            prev,
            step,
        }
    }

    /// Number of local columns, including aliases to circuit words.
    pub(super) const fn len(&self) -> usize {
        self.step + 1
    }

    /// The word's column, if it has one: a hint has none.
    pub(super) fn column(&self, word: Word) -> Option<usize> {
        let missing = || -> usize { panic!("the class has no {word:?} word") };
        Some(match word {
            Word::Clock => self.ts,
            Word::Prev(i) => self.prev + i as usize,
            Word::Step => self.step,
            Word::Flags => self.flags.unwrap_or_else(missing),
            Word::Imm => self.imm.unwrap_or_else(missing),
            Word::V1 => self.v1,
            Word::Pc4 => self.pc4,
            Word::V2 => self.rs2.map_or_else(missing, |r| r.v2),
            Word::Out => self.rd.map_or_else(missing, |rd| rd.out),
            Word::Dt => self.control.map_or_else(missing, |c| c.dt),
            Word::Jump => self.control.map_or_else(missing, |c| c.jump),
            Word::Address => self.ram.map_or_else(missing, |r| r.address),
            Word::Cell(k) => match (self.ram, self.block) {
                (Some(ram), _) => ram.cell,
                (_, Some(block)) => block.words + k as usize,
                _ => missing(),
            },
            Word::CellNew(k) => match (self.ram, self.block) {
                (Some(ram), _) => ram.new,
                (_, Some(block)) => block.left(k as usize),
                _ => missing(),
            },
            Word::Dest => self.pointer.map_or_else(missing, |p| p.vd),
            Word::FlagBit(k) => self.flag_bits.map_or_else(missing, |b| b + k as usize),
            Word::LimbAddress(k) => self.limbs.and_then(|l| l.computed(k as usize)).unwrap_or_else(missing),
            Word::Bad => self.bad.unwrap_or_else(missing),
            Word::HintQ | Word::HintR => return None,
        })
    }
}

/// Assign contiguous local columns in protocol order.
#[derive(Default)]
struct ColumnAllocator {
    /// First local column index not yet assigned.
    next: usize,
}

impl ColumnAllocator {
    /// Reserve consecutive columns, returning their first index.
    const fn allocate(&mut self, count: usize) -> usize {
        let start = self.next;
        self.next += count;
        start
    }
}

#[cfg(test)]
mod tests {
    use super::super::ClassSpec;
    use super::*;

    #[test]
    fn doubleword_moves_share_the_value_column_on_both_bus_sides() {
        // A load's register write and a store's cell write must bind the value read, without a new output port.
        let load = Columns::new(&ClassSpec::LD);
        let store = Columns::new(&ClassSpec::SD);
        assert_eq!(
            load.rd.expect("a load writes rd").out,
            load.ram.expect("a load reads RAM").cell
        );
        assert_eq!(
            store.rs2.expect("a store reads rs2").v2,
            store.ram.expect("a store writes RAM").new
        );
        assert!(load.flags.is_none() && store.flags.is_none());
    }
}
