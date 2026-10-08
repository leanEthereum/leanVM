//! Local column allocation and the aliases used by memory moves.

use super::{ClassSpec, Ram, Word};
use crate::leaf::Coord::{self, Col};

/// The `rs2` read's columns: the register's number and what it held.
#[derive(Clone, Copy)]
pub(super) struct SourceColumns {
    /// Second source register number.
    pub(super) a2: usize,

    /// Second source register value.
    pub(super) v2: usize,
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

/// Columns of a compression: its two more registers, its twelve words read, and its result.
#[derive(Clone, Copy)]
pub(super) struct BlockColumns {
    /// The fourth register's number, the entry's immediate.
    pub(super) a3: usize,

    /// The fourth register's value: the counter, or a node's bit.
    pub(super) v3: usize,

    /// The destination register's number: it is read, as the result's pointer.
    pub(super) ad: usize,

    /// The result's pointer.
    pub(super) vd: usize,

    /// The chaining value's four words, then the message's eight.
    pub(super) words: usize,

    /// The result's four words as found.
    pub(super) old: usize,

    /// The result's four words.
    pub(super) out: usize,
}

/// Columns of a move of one element between memory and an extension register.
///
/// The limbs moved are one set of columns on both tuples: what the load's register receives is what its words hold,
/// and what the store's words receive is what its register holds.
#[derive(Clone, Copy)]
pub(super) struct ElementColumns {
    /// The address of the first limb, the circuit's word.
    pub(super) address: usize,

    /// The three limbs moved.
    pub(super) limbs: usize,

    /// What the destination held, three limbs: the register for a load, the words for a store.
    pub(super) old: usize,
}

/// Columns of an extension-field product: its operands' limbs, the result's, and its selectors.
///
/// All are committed columns, which the table's identities relate.
#[derive(Clone, Copy)]
pub(super) struct ExtColumns {
    /// The nine limbs as found, `a`'s, `b`'s, then `c`'s: `a`'s first is the first source's value column.
    pub(super) limbs: usize,

    /// `c`'s three limbs after the row.
    pub(super) new: usize,

    /// The three selectors, each 0 or 1: accumulate, base-field operand, zero result.
    pub(super) flags: usize,
}

impl ExtColumns {
    /// The limbs of operand `i` as found: `a`, `b`, then `c`.
    pub(super) fn operand(&self, i: usize) -> [Coord; 3] {
        std::array::from_fn(|k| Col(self.limbs + 3 * i + k))
    }

    /// `c`'s limbs after the row.
    pub(super) fn result(&self) -> [Coord; 3] {
        std::array::from_fn(|k| Col(self.new + k))
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

    /// Optional control-flow columns.
    pub(super) control: Option<ControlColumns>,

    /// Optional decoded immediate.
    pub(super) imm: Option<usize>,

    /// Optional single-cell memory access.
    pub(super) ram: Option<MemoryColumns>,

    /// Optional hash block access.
    pub(super) block: Option<BlockColumns>,

    /// Optional move of an element.
    pub(super) element: Option<ElementColumns>,

    /// Optional extension-field product.
    pub(super) ext: Option<ExtColumns>,

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
        // An extension-field product's nine limbs start at its first source's value, `b`'s and `c`'s after `a`'s.
        let limbs = spec.wide.then(|| allocator.allocate(8) - 1);
        // An element's move: the address, the limbs moved, then what the destination held.
        let element = (spec.ram == Ram::Element).then(|| ElementColumns {
            address: allocator.allocate(1),
            limbs: allocator.allocate(3),
            old: allocator.allocate(3),
        });
        let flags = spec.words().any(|w| w == Word::Flags).then(|| allocator.allocate(1));
        let rs2 = spec.reads_rs2.then(|| SourceColumns {
            a2: allocator.allocate(1),
            v2: match (limbs, element) {
                (Some(l), _) => l + 3,
                (_, Some(e)) => e.limbs,
                _ => allocator.allocate(1),
            },
        });
        // A doubleword load's `rd` receives its cell, which is a column further on.
        let rd = spec.writes_rd.then(|| {
            (
                allocator.allocate(1),
                match (limbs, element) {
                    (Some(l), _) => l + 6,
                    (_, Some(e)) => e.old,
                    _ => allocator.allocate(1),
                },
                (!spec.copies).then(|| allocator.allocate(if spec.wide { 3 } else { 1 })),
            )
        });
        let control = spec.control.then(|| ControlColumns {
            dt: allocator.allocate(1),
            jump: allocator.allocate(1),
            exit: allocator.allocate(1),
        });
        let imm = spec.words().any(|w| w == Word::Imm).then(|| allocator.allocate(1));
        let (ram, block) = match spec.ram {
            Ram::None | Ram::Element => (None, None),
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
                let (a3, v3, ad, vd) = (
                    allocator.allocate(1),
                    allocator.allocate(1),
                    allocator.allocate(1),
                    allocator.allocate(1),
                );
                let words = allocator.allocate(12);
                (
                    None,
                    Some(BlockColumns {
                        a3,
                        v3,
                        ad,
                        vd,
                        words,
                        old: allocator.allocate(4),
                        out: allocator.allocate(4),
                    }),
                )
            }
        };
        let rd = rd.map(|(ad, vd_old, out)| DestinationColumns {
            ad,
            vd_old,
            out: out.unwrap_or_else(|| {
                element.map_or_else(|| ram.expect("a doubleword load reads a cell").cell, |e| e.limbs)
            }),
        });
        let ext = limbs.map(|limbs| ExtColumns {
            limbs,
            new: rd.expect("a product writes its destination").out,
            flags: allocator.allocate(3),
        });
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
            control,
            imm,
            ram,
            block,
            element,
            ext,
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
            Word::V3 => self.block.map_or_else(missing, |b| b.v3),
            Word::Out => self.rd.map_or_else(missing, |rd| rd.out),
            Word::Dt => self.control.map_or_else(missing, |c| c.dt),
            Word::Jump => self.control.map_or_else(missing, |c| c.jump),
            Word::Address => match (self.ram, self.element) {
                (Some(ram), _) => ram.address,
                (_, Some(element)) => element.address,
                _ => missing(),
            },
            Word::Cell(k) => match (self.ram, self.block) {
                (Some(ram), _) => ram.cell,
                (_, Some(block)) => block.words + k as usize,
                _ => missing(),
            },
            Word::CellNew(k) => match (self.ram, self.block) {
                (Some(ram), _) => ram.new,
                (_, Some(block)) => block.out + k as usize,
                _ => missing(),
            },
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
