//! Local column views and the shared value aliases supplied by the Clean table source.

use super::Word;
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

/// Columns of a class with branches and jumps, the exit included.
#[derive(Clone, Copy)]
pub(super) struct ControlColumns {
    /// Decoded jump offset, a circuit input.
    pub(super) dt: usize,

    /// The offset when the jump is taken, zero otherwise: a circuit output.
    pub(super) jump: usize,

    /// Selector for the exit instruction.
    pub(super) exit: usize,
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
}

/// Local column layout, including shared columns for unchanged doubleword moves.
///
/// Allocation order is protocol data.
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
