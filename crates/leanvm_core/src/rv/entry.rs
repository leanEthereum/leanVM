//! Decoded instructions: the classes, and the entries the bytecode table holds.
//!
//! A class is one table and, but for the extension-field product, one circuit.
//!
//! Its instructions differ only by a flag word, which selects what the class's one function does.
//!
//! The program is public, so each instruction word is decoded into an entry once, before any run.

use super::circuits::ClassCircuit;
use super::instruction::{ExtOp, ImmOp, Instruction, LoadOp, Op, RegOp, ShiftOp, StoreOp};
use super::register::{ExtReg, Reg, RegisterFile};
use super::semantics::{
    Alu, Div, Ext, Hash, InstructionClass, Ld, Load, Mul, Mulh, Outcome, Sd, Shift, Store, WordAccess,
};
use flock::circuit::Circuit;

/// An instruction class: one table, and one circuit unless its table proves it by identities.
///
/// The classes with a table come in table order.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum Class {
    /// Add, subtract, compare, bitwise logic, branches and jumps.
    Alu,
    /// A byte, half word or word read from memory.
    Load,
    /// A byte, half word or word written to memory.
    Store,
    /// `ld`: a double word moved from its cell to a register, with no byte to select.
    Ld,
    /// `sd`: a double word moved from a register to its cell, with no byte to select.
    Sd,
    /// Logical and arithmetic shifts.
    Shift,
    /// The low word of a product.
    Mul,
    /// The high word of a product.
    Mulh,
    /// Quotients and remainders.
    Div,
    /// The BLAKE2s compression, a custom instruction.
    Hash,
    /// The multiplication in the extension field, by an element of it or of the base field: a custom instruction.
    Ext,
    /// No table runs it, so reaching one is a trap.
    Illegal,
}

impl Class {
    /// The flag words this class defines.
    ///
    /// An entry may carry no other.
    ///
    /// An illegal entry carries none at all.
    pub const fn legal_flags(self) -> &'static [u64] {
        match self {
            Self::Alu => Alu::LEGAL,
            Self::Shift => Shift::LEGAL,
            Self::Load => Load::LEGAL,
            Self::Store => Store::LEGAL,
            Self::Ld => Ld::LEGAL,
            Self::Sd => Sd::LEGAL,
            Self::Mul => Mul::LEGAL,
            Self::Mulh => Mulh::LEGAL,
            Self::Div => Div::LEGAL,
            Self::Hash => Hash::LEGAL,
            Self::Ext => Ext::LEGAL,
            Self::Illegal => &[],
        }
    }

    /// An instruction of the class that names no register but `x0`, or `ra` where `x0` is undefined.
    ///
    /// A load, a store, a hash and an extension-field product touch the memory at address zero.
    ///
    /// The extension-field product reads `c`'s address from `ra`, as an address in `x0` is undefined.
    ///
    /// Returns `None` for the illegal class, which has no instruction.
    pub const fn nop(self) -> Option<Op> {
        let (rd, rs1, rs2) = (Reg::ZERO, Reg::ZERO, Reg::ZERO);
        Some(match self {
            Self::Alu => Op::Imm {
                op: ImmOp::Addi,
                rd,
                rs1,
                imm: 0,
            },
            Self::Shift => Op::Shift {
                op: ShiftOp::Slli,
                rd,
                rs1,
                amount: 0,
            },
            Self::Load => Op::Load {
                op: LoadOp::Lb,
                rd,
                rs1,
                offset: 0,
            },
            Self::Store => Op::Store {
                op: StoreOp::Sb,
                rs1,
                rs2,
                offset: 0,
            },
            Self::Ld => Op::Load {
                op: LoadOp::Ld,
                rd,
                rs1,
                offset: 0,
            },
            Self::Sd => Op::Store {
                op: StoreOp::Sd,
                rs1,
                rs2,
                offset: 0,
            },
            Self::Mul => Op::Reg {
                op: RegOp::Mul,
                rd,
                rs1,
                rs2,
            },
            Self::Mulh => Op::Reg {
                op: RegOp::Mulhu,
                rd,
                rs1,
                rs2,
            },
            Self::Div => Op::Reg {
                op: RegOp::Divu,
                rd,
                rs1,
                rs2,
            },
            Self::Hash => Op::Blake2s { rs1, rs2, last: false },
            Self::Ext => Op::Ext {
                op: ExtOp::Extmul,
                rd: ExtReg::F3,
                rs1: ExtReg::ONE,
                rs2: ExtReg::ONE,
            },
            Self::Illegal => return None,
        })
    }

    /// The class's circuit: its function as a gate list over the words its table puts on the bus.
    ///
    /// # Panics
    ///
    /// Panics for the illegal class, which no table runs, and for the extension-field product, which its table
    /// proves by identities over `K` instead (`tables::ClassTable::identities`).
    pub fn circuit(self) -> Circuit {
        match self {
            Self::Alu => Alu::circuit(),
            Self::Shift => Shift::circuit(),
            Self::Load => Load::circuit(),
            Self::Store => Store::circuit(),
            Self::Ld => Ld::circuit(),
            Self::Sd => Sd::circuit(),
            Self::Mul => Mul::circuit(),
            Self::Mulh => Mulh::circuit(),
            Self::Div => Div::circuit(),
            Self::Hash => Hash::circuit(),
            Self::Ext => panic!("the extension-field product has no circuit"),
            Self::Illegal => panic!("the illegal class has no circuit"),
        }
    }
}

/// Where control goes after an instruction.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Target {
    /// The next instruction, or the address an indirect jump computes.
    Next,
    /// A fixed address, taken when the class says so: a branch or a `jal`.
    Abs(u64),
    /// The halt slot, the last of the text: where `ECALL` jumps.
    Halt,
}

/// One decoded instruction.
///
/// Every entry reads two registers and writes one cell.
///
/// An instruction with fewer reads `x0`.
///
/// One with no destination, or with `rd = x0`, writes the sink.
///
/// The fields are plain data, since a table may hold any entry.
///
/// What makes an entry RISC-V is checked separately, by the well-formedness rules.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Entry {
    /// The table that runs the instruction.
    pub class: Class,
    /// What the class's function computes: one of the class's legal words.
    pub flags: u64,
    /// The first register read, below 32.
    pub a1: u8,
    /// The second register read, below 32.
    pub a2: u8,
    /// The cell written, in `1..=32`.
    pub ad: u8,
    /// The immediate, sign-extended, or a constant folded at decoding.
    pub imm: u64,
    /// Where control goes.
    pub target: Target,
}

impl Entry {
    /// An instruction no table runs.
    ///
    /// Every encoding rv64im does not define decodes to this one entry.
    pub const ILLEGAL: Self = Self {
        class: Class::Illegal,
        flags: 0,
        a1: 0,
        a2: 0,
        ad: RegisterFile::SINK,
        imm: 0,
        target: Target::Next,
    };

    /// `ECALL`: an unconditional jump to the halt slot.
    pub const EXIT: Self = Self {
        class: Class::Alu,
        flags: Alu::ALWAYS,
        a1: 0,
        a2: 0,
        ad: RegisterFile::SINK,
        imm: 0,
        target: Target::Halt,
    };

    /// What this entry, at `pc`, computes from its registers and, for a load or a store, the cell it names.
    ///
    /// The result holds whether or not a run could make the access.
    ///
    /// A hash or an extension-field product computes nothing here: its operands are the machine's to read.
    pub fn evaluate(&self, pc: u64, v1: u64, v2: u64, cell: u64) -> Outcome {
        let (flags, imm) = (self.flags, self.imm);
        let (out, taken, access) = match self.class {
            // The decision reads no jump offset.
            Class::Alu => {
                let (out, taken) = Alu {
                    flags,
                    v1,
                    v2,
                    imm,
                    dt: 0,
                    pc4: pc.wrapping_add(4),
                }
                .eval();
                (out, taken, None)
            }
            Class::Shift => (Shift { flags, v1, v2, imm }.eval(), false, None),
            Class::Mul => (Mul { flags, v1, v2 }.eval(), false, None),
            Class::Mulh => (Mulh { flags, v1, v2 }.eval(), false, None),
            Class::Div => (Div { flags, v1, v2 }.eval(), false, None),
            // A load leaves its cell as it was.
            Class::Load => {
                let (address, value) = Load { flags, v1, imm, cell }.eval();
                let access = WordAccess {
                    address,
                    old: cell,
                    new: cell,
                };
                (value, false, Some(access))
            }
            // A store's result is the cell it leaves.
            Class::Store => {
                let (address, new) = Store {
                    flags,
                    v1,
                    v2,
                    imm,
                    cell,
                }
                .eval();
                let access = WordAccess {
                    address,
                    old: cell,
                    new,
                };
                (0, false, Some(access))
            }
            // A double word's value is its cell, unchanged.
            Class::Ld => {
                let (address, value) = Ld { v1, imm, cell }.eval();
                let access = WordAccess {
                    address,
                    old: cell,
                    new: cell,
                };
                (value, false, Some(access))
            }
            // A double word's store leaves `v2` itself in its cell.
            Class::Sd => {
                let (address, new) = Sd { v1, v2, imm }.eval();
                let access = WordAccess {
                    address,
                    old: cell,
                    new,
                };
                (0, false, Some(access))
            }
            Class::Hash | Class::Ext | Class::Illegal => (0, false, None),
        };
        Outcome { out, taken, access }
    }

    /// The entry of the instruction `word` at address `pc`.
    ///
    /// Every encoding the machine does not define is the illegal entry.
    pub fn decode(word: u32, pc: u64) -> Self {
        Instruction::from_bits(word)
            .decode()
            .map_or(Self::ILLEGAL, |op| Self::new(op, pc))
    }

    /// The entry of the operation `op` at address `pc`.
    ///
    /// The address is known, so `AUIPC`, `JAL`'s link and the jump targets fold to constants.
    ///
    /// A register-register and a register-immediate operation share one shape:
    ///
    /// - a register-register one reads `rs1` and `rs2`, and has no immediate;
    /// - a register-immediate one reads `rs1` and `x0`, and has the immediate.
    pub fn new(op: Op, pc: u64) -> Self {
        let (class, flags) = op.function();
        let entry = |rs1: Reg, rs2: Reg, rd: Reg, imm: u64| Self::sequential(class, flags, rs1, rs2, rd, imm);
        let zero = Reg::ZERO;
        match op {
            Op::Reg { rd, rs1, rs2, .. } => entry(rs1, rs2, rd, 0),
            // The three numbers are extension registers', but a base-field form's second, an integer register's.
            Op::Ext { rd, rs1, rs2, .. } => Self {
                class,
                flags,
                a1: rs1.index() as u8,
                a2: rs2.index() as u8,
                ad: rd.index() as u8,
                imm: 0,
                target: Target::Next,
            },
            Op::Imm { rd, rs1, imm, .. } => entry(rs1, zero, rd, imm as i64 as u64),
            Op::Shift { rd, rs1, amount, .. } => entry(rs1, zero, rd, amount as u64),
            Op::Load { rd, rs1, offset, .. } => entry(rs1, zero, rd, offset as i64 as u64),
            Op::Store { rs1, rs2, offset, .. } => entry(rs1, rs2, zero, offset as i64 as u64),
            Op::Blake2s { rs1, rs2, .. } => entry(rs1, rs2, zero, 0),
            Op::Fence => entry(zero, zero, zero, 0),
            Op::Ecall => Self::EXIT,

            // LUI and AUIPC: a constant added to x0.
            Op::Lui { rd, imm20 } => entry(zero, zero, rd, (imm20 << 12) as i32 as i64 as u64),
            Op::Auipc { rd, imm20 } => entry(zero, zero, rd, pc.wrapping_add((imm20 << 12) as i32 as i64 as u64)),

            // A branch compares by subtraction, and jumps to a fixed target.
            Op::Branch { rs1, rs2, offset, .. } => Self {
                target: Target::Abs(pc.wrapping_add(offset as i64 as u64)),
                ..entry(rs1, rs2, zero, 0)
            },

            // JAL: an unconditional jump to a fixed target, linking pc + 4 as a constant added to x0.
            Op::Jal { rd, offset } => Self {
                target: Target::Abs(pc.wrapping_add(offset as i64 as u64)),
                ..entry(zero, zero, rd, pc.wrapping_add(4))
            },

            // JALR: a jump to rs1 + offset with bit 0 cleared, linking pc + 4.
            Op::Jalr { rd, rs1, offset } => entry(rs1, zero, rd, offset as i64 as u64),
        }
    }

    /// Whether this entry jumps to the halt slot.
    pub fn is_exit(&self) -> bool {
        self.target == Target::Halt
    }

    /// Whether the entry at `pc` obeys the rules that make the bytecode table RISC-V.
    ///
    /// Both verifiers check these rules on every entry.
    ///
    /// The proof system itself is sound for any table, a malformed one included.
    ///
    /// The rules:
    ///
    /// - an illegal entry and an exit each have exactly one form;
    /// - the registers read are below 32, and the cell written is in `1..=32`;
    /// - the flags are legal for the class;
    /// - the target matches what the flags select, and a `jal` links `pc + 4`;
    /// - a field the class's table holds at a constant has that constant.
    pub fn is_well_formed(&self, pc: u64) -> bool {
        // An illegal entry has one inert form.
        if self.class == Class::Illegal {
            return *self == Self::ILLEGAL;
        }

        // Only the canonical exit may jump to the halt slot.
        if self.is_exit() {
            return *self == Self::EXIT;
        }

        // Register numbers, and flags the class's circuit is written for.
        let operands = match self.class {
            // Extension registers: the constants are never written, and a base-field operand is an integer register.
            Class::Ext => {
                let second = if self.flags & Ext::BASE != 0 {
                    Reg::COUNT
                } else {
                    ExtReg::COUNT
                };
                let written = ExtReg::FIRST_WRITABLE..ExtReg::COUNT as u8;
                (self.a1 as usize) < ExtReg::COUNT && (self.a2 as usize) < second && written.contains(&self.ad)
            }
            _ => self.a1 < 32 && self.a2 < 32 && (1..=RegisterFile::SINK).contains(&self.ad),
        };
        let flags = self.class.legal_flags().contains(&self.flags);
        operands && flags && self.has_consistent_control(pc) && self.has_table_constants()
    }

    /// An entry with no control flow.
    ///
    /// A destination of `x0` becomes the sink, which nothing reads.
    const fn sequential(class: Class, flags: u64, rs1: Reg, rs2: Reg, rd: Reg, imm: u64) -> Self {
        Self {
            class,
            flags,
            a1: rs1.index() as u8,
            a2: rs2.index() as u8,
            ad: if rd.index() == 0 {
                RegisterFile::SINK
            } else {
                rd.index() as u8
            },
            imm,
            target: Target::Next,
        }
    }

    /// Whether the target matches the flags of the entry at `pc`.
    ///
    /// - A `jal` jumps to a fixed target, and its sum `x0 + x0 + imm` is the link `pc + 4`.
    /// - A branch jumps to a fixed target.
    /// - Anything else has none: it falls through, or jumps to the address it computes.
    fn has_consistent_control(&self, pc: u64) -> bool {
        let fixed = matches!(self.target, Target::Abs(_));
        let next = self.target == Target::Next;
        if self.class != Class::Alu {
            return next;
        }

        // The flags say which control shape the entry must have.
        match self.flags {
            Alu::ALWAYS => fixed && self.a1 == 0 && self.a2 == 0 && self.imm == pc.wrapping_add(4),
            flags if flags & Alu::BRANCHES != 0 => fixed,
            _ => next,
        }
    }

    /// Whether the fields a class's table fixes hold their constants.
    ///
    /// - A load reads no `rs2`, so its second register is `x0`.
    /// - A store writes no `rd`, so its destination is the sink.
    /// - A hash writes no `rd` and has no immediate.
    /// - An extension-field product reads `rd` as an address, so it names a register, and has no immediate.
    ///
    /// That a doubleword load or store has no flags is its legal flag word, zero.
    const fn has_table_constants(&self) -> bool {
        match self.class {
            Class::Load | Class::Ld => self.a2 == 0,
            Class::Store | Class::Sd => self.ad == RegisterFile::SINK,
            Class::Hash => self.ad == RegisterFile::SINK && self.imm == 0,
            Class::Ext => self.imm == 0,
            _ => true,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::rv::Region;
    use crate::rv::instruction::BranchOp;
    use crate::rv::register::Reg;
    use proptest::prelude::*;
    use std::collections::HashSet;

    #[test]
    fn only_the_canonical_exit_jumps_to_the_halt_slot() {
        // Fixture: the decoded ecall.
        let exit = Entry::decode(0x73, 0);
        assert_eq!(exit, Entry::EXIT);
        assert!(exit.is_well_formed(0));

        // Mutation: change any one field, the halt target kept.
        for malformed in [
            Entry {
                class: Class::Load,
                ..exit
            },
            Entry { flags: 0, ..exit },
            Entry { a1: 1, ..exit },
            Entry { a2: 1, ..exit },
            Entry { ad: 1, ..exit },
            Entry { imm: 1, ..exit },
        ] {
            assert!(!malformed.is_well_formed(0), "{malformed:?}");
        }
    }

    #[test]
    fn a_skipped_register_access_names_its_constant() {
        // Invariant: a load's rs2 is x0, a store's rd is the sink, and a double word's flags are zero.
        //
        // Fixture: `ld`, `sd`, `lw` and `sw` of `a0` at `0(a1)`.
        for (load, store, classes) in [
            (0x0005_b503, 0x00a5_b023, (Class::Ld, Class::Sd)),
            (0x0005_a503, 0x00a5_a023, (Class::Load, Class::Store)),
        ] {
            let (load, store) = (Entry::decode(load, 0), Entry::decode(store, 0));
            assert_eq!((load.class, store.class), classes);
            assert!(load.is_well_formed(0) && store.is_well_formed(0));

            // Mutation: the load reads x1 as rs2, the store writes x1, the double words carry a width.
            assert!(!Entry { a2: 1, ..load }.is_well_formed(0));
            assert!(!Entry { ad: 1, ..store }.is_well_formed(0));
            if classes.0 == Class::Ld {
                assert!(!Entry { flags: 3, ..load }.is_well_formed(0));
                assert!(!Entry { flags: 3, ..store }.is_well_formed(0));
            }
        }
    }

    #[test]
    fn alu_control_shapes_match_their_flags() {
        // Fixture: one instruction per legal ALU word, in the order of the legal list.
        //
        //     addi, sub, addiw, subw, slt, sltu, and, or, xor,
        //     jalr, beq, bne, blt, bge, bltu, bgeu, jal
        let witnesses = [
            0x0000_0013,
            0x4000_0033,
            0x0000_001b,
            0x4000_003b,
            0x0000_2033,
            0x0000_3033,
            0x0000_7033,
            0x0000_6033,
            0x0000_4033,
            0x0000_0067,
            0x0000_0063,
            0x0000_1063,
            0x0000_4063,
            0x0000_5063,
            0x0000_6063,
            0x0000_7063,
            0x0000_006f,
        ];
        assert_eq!(Alu::LEGAL.len(), witnesses.len());

        let pc = Region::TEXT.base();
        for (&flags, word) in Alu::LEGAL.iter().zip(witnesses) {
            let decoded = Entry::decode(word, pc);
            assert_eq!((decoded.class, decoded.flags), (Class::Alu, flags));

            // Mutation: every target kind.
            //
            // Only the decoded shape is well formed, whatever the fixed address.
            for target in [Target::Next, Target::Abs(pc), Target::Abs(pc + 4)] {
                let candidate = Entry { target, ..decoded };
                let same_kind = matches!(
                    (target, decoded.target),
                    (Target::Next, Target::Next) | (Target::Abs(_), Target::Abs(_))
                );
                assert_eq!(candidate.is_well_formed(pc), same_kind, "{candidate:?}");
            }
        }

        // A jal links pc + 4, a constant added to x0: at another address, or read off a register, it is not a jal.
        let jal = Entry::decode(0x0000_00ef, pc);
        assert_eq!((jal.flags, jal.imm), (Alu::ALWAYS, pc + 4));
        assert!(jal.is_well_formed(pc));
        assert!(!jal.is_well_formed(pc + 4));
        assert!(!Entry { a1: 1, ..jal }.is_well_formed(pc));
        assert!(!Entry { a2: 1, ..jal }.is_well_formed(pc));
    }

    #[test]
    fn each_class_defines_exactly_the_flag_words_its_operations_use() {
        // Fixture: every operation once, with registers that make every one well formed.
        //
        let (rd, rs1, rs2) = (Reg::RA, Reg::RA, Reg::RA);
        let ops: Vec<Op> = RegOp::ALL
            .map(|op| Op::Reg { op, rd, rs1, rs2 })
            .into_iter()
            .chain(ImmOp::ALL.map(|op| Op::Imm { op, rd, rs1, imm: 0 }))
            .chain(ShiftOp::ALL.map(|op| Op::Shift { op, rd, rs1, amount: 0 }))
            .chain(LoadOp::ALL.map(|op| Op::Load { op, rd, rs1, offset: 0 }))
            .chain(StoreOp::ALL.map(|op| Op::Store {
                op,
                rs1,
                rs2,
                offset: 0,
            }))
            .chain(BranchOp::ALL.map(|op| Op::Branch {
                op,
                rs1,
                rs2,
                offset: 0,
            }))
            .chain(ExtOp::ALL.map(|op| Op::Ext {
                op,
                rd: ExtReg::F3,
                rs1: ExtReg::ONE,
                rs2: ExtReg::ONE,
            }))
            .chain([
                Op::Lui { rd, imm20: 0 },
                Op::Auipc { rd, imm20: 0 },
                Op::Jal { rd, offset: 0 },
                Op::Jalr { rd, rs1, offset: 0 },
                Op::Fence,
                Op::Ecall,
                Op::Blake2s { rs1, rs2, last: false },
                Op::Blake2s { rs1, rs2, last: true },
            ])
            .collect();

        // Every operation's entry obeys the bytecode table's rules.
        for &op in &ops {
            assert!(
                Entry::new(op, Region::TEXT.base()).is_well_formed(Region::TEXT.base()),
                "{op:?}"
            );
        }

        // Invariant: a class's legal words are the words its operations use, no more and no fewer.
        //
        //     an unused legal word would be a function no program reaches
        //     a used word outside the list would be refused by the verifiers
        for class in [
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
        ] {
            let used: HashSet<u64> = ops
                .iter()
                .map(|op| op.function())
                .filter(|&(c, _)| c == class)
                .map(|(_, flags)| flags)
                .collect();
            let legal: HashSet<u64> = class.legal_flags().iter().copied().collect();
            assert_eq!(used, legal, "{class:?}");
        }
    }

    #[test]
    fn decoded_entries_are_well_formed() {
        // The forms the sweep below misses: they need rd = x0.
        //
        //     ecall, blake2s, blake2s on the final block
        for word in [0x73, 0x0000_000b, 0x0000_100b] {
            assert!(Entry::decode(word, Region::TEXT.base()).is_well_formed(Region::TEXT.base()));
        }

        // Every opcode and function, every 12-bit top, with fixed registers.
        //
        // Fixture: rd = x21 and rs1 = x10, so every register field is nonzero.
        for opcode in 0..128u32 {
            for f3 in 0..8u32 {
                for top in 0..(1u32 << 12) {
                    let word = opcode | (f3 << 12) | (top << 20) | (0x15 << 7) | (0x0a << 15);
                    let e = Entry::decode(word, Region::TEXT.base());
                    assert!(e.is_well_formed(Region::TEXT.base()), "{word:#010x} decodes to {e:?}");
                }
            }
        }
    }

    #[test]
    fn each_class_nop_is_of_its_class_and_names_only_x0() {
        // Fixture: every class but the illegal one, which has no instruction.
        let classes = [
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
        assert_eq!(Class::Illegal.nop(), None);

        // Each no-op decodes to its class, reads x0 twice, writes the sink, and has no immediate.
        for class in classes {
            let e = Entry::new(class.nop().expect("a legal class"), Region::TEXT.base());
            assert_eq!(
                (e.class, e.a1, e.a2, e.ad, e.imm),
                (class, 0, 0, RegisterFile::SINK, 0),
                "{class:?}"
            );
            assert!(e.is_well_formed(Region::TEXT.base()));
        }
    }

    #[test]
    fn reserved_encodings_are_illegal() {
        // Shift encodings RV64 reserves, and what rv64im does not define.
        let illegal = [
            0x0400_1013u32, // SLLI with a function bit set
            0x0200_101b,    // SLLIW with bit 5 of the amount
            0x0200_501b,    // SRLIW with bit 5 of the amount
            0x4200_501b,    // SRAIW with bit 5 of the amount
            0x0010_0073,    // EBREAK
            0x3000_2073,    // CSRRS mstatus
            0x0000_100f,    // FENCE.I
            0x0000_0000,
            0xffff_ffff,
            0x0000_7003,          // a load of width 7
            0x0000_4023,          // a store of width 4
            0x0000_2063,          // a branch with function 2
            0x0000_1067,          // JALR with a nonzero function
            0x0000_208b,          // BLAKE2S with function 2
            0x0000_008b | 5 << 7, // BLAKE2S with a destination
            0x0200_000b,          // BLAKE2S with a function-7 bit set
            0x8000_002b | 5 << 7, // an extension-field product with the top function-7 bit set
            0x0000_002b | 2 << 7, // an extension-field product into a constant
            0x2000_202b | 5 << 7, // a base-field operand past the integer registers
        ];
        for word in illegal {
            assert_eq!(Entry::decode(word, 0), Entry::ILLEGAL, "{word:#010x}");
        }

        // SRAI by 63 uses bit 25 as an amount bit, which RV64 allows.
        assert_eq!(Entry::decode(0x43f5_5513, 0).class, Class::Shift);
    }

    proptest! {
        #[test]
        fn register_operations_decode_to_their_operands(op in proptest::sample::select(&RegOp::ALL[..]), rd in any::<Reg>(), rs1 in any::<Reg>(), rs2 in any::<Reg>()) {
            // Invariant: the assembler and the decoder agree on every register field.
            let e = Entry::decode(op.encode(rd, rs1, rs2).bits(), Region::TEXT.base());
            let ad = if rd.index() == 0 { RegisterFile::SINK } else { rd.index() as u8 };
            prop_assert_eq!((e.a1, e.a2, e.ad, e.imm), (rs1.index() as u8, rs2.index() as u8, ad, 0));
            prop_assert!(e.is_well_formed(Region::TEXT.base()));
        }

        #[test]
        fn extension_field_operations_decode_to_their_flags(op in proptest::sample::select(&ExtOp::ALL[..]), rd in any::<ExtReg>(), rs1 in any::<ExtReg>(), rs2 in any::<ExtReg>()) {
            // Invariant: the flags are the function's bits, and every register is read as itself.
            //
            //     bit 0 accumulates, bit 1 takes a base-field operand, bit 2 requires a zero result
            let e = Entry::decode(op.encode(rd, rs1, rs2).bits(), Region::TEXT.base());
            let flags = ExtOp::ALL.iter().position(|&o| o == op).unwrap() as u64;
            if rd.index() < 3 || flags & Ext::BASE != 0 && rs2.index() >= 32 {
                // A constant is never written, and a base-field operand is an integer register.
                prop_assert_eq!(e, Entry::ILLEGAL);
            } else {
                prop_assert_eq!((e.class, e.flags), (Class::Ext, flags));
                prop_assert_eq!((e.a1, e.a2, e.ad), (rs1.index() as u8, rs2.index() as u8, rd.index() as u8));
                prop_assert!(e.is_well_formed(Region::TEXT.base()));
                prop_assert!(!Entry { ad: 2, ..e }.is_well_formed(Region::TEXT.base()), "a constant written");
                prop_assert!(!Entry { a1: 128, ..e }.is_well_formed(Region::TEXT.base()), "no such register");
            }
        }

        #[test]
        fn immediate_operations_decode_to_their_immediate(op in proptest::sample::select(&ImmOp::ALL[..]), imm in -2048i32..2048, rd in any::<Reg>(), rs1 in any::<Reg>()) {
            // The 12-bit immediate is sign-extended, and the second read is x0.
            let e = Entry::decode(op.encode(rd, rs1, imm).bits(), Region::TEXT.base());
            prop_assert_eq!((e.a1, e.a2, e.imm), (rs1.index() as u8, 0, imm as i64 as u64));
        }

        #[test]
        fn shifts_decode_to_their_amount(op in proptest::sample::select(&ShiftOp::ALL[..]), raw in any::<u32>(), rd in any::<Reg>(), rs1 in any::<Reg>()) {
            // Any amount the format holds is the entry's immediate.
            let amount = raw % (1 << op.amount_bits());
            let e = Entry::decode(op.encode(rd, rs1, amount).bits(), Region::TEXT.base());
            prop_assert_eq!((e.class, e.imm), (Class::Shift, amount as u64));
        }

        #[test]
        fn memory_operations_decode_to_their_width(load in proptest::sample::select(&LoadOp::ALL[..]), store in proptest::sample::select(&StoreOp::ALL[..]), offset in -2048i32..2048, rs1 in any::<Reg>(), rs2 in any::<Reg>()) {
            // The width in the flags is the operation's, and the offset is the immediate.
            //
            // A double word is LD's or SD's, which have no flags.
            let (l, s) = (Entry::decode(load.encode(rs2, rs1, offset).bits(), 0), Entry::decode(store.encode(rs2, rs1, offset).bits(), 0));
            let load_shape = if load.log_width() == 3 { (Class::Ld, 0) } else { (Class::Load, load.log_width() as u64) };
            let store_shape = if store.log_width() == 3 { (Class::Sd, 0) } else { (Class::Store, store.log_width() as u64) };
            prop_assert_eq!((l.class, l.flags & Load::LOG_WIDTH, l.imm), (load_shape.0, load_shape.1, offset as i64 as u64));
            prop_assert_eq!((s.class, s.flags, s.imm), (store_shape.0, store_shape.1, offset as i64 as u64));
        }

        #[test]
        fn branches_fold_their_target(op in proptest::sample::select(&BranchOp::ALL[..]), half in -2048i32..2048, rs1 in any::<Reg>(), rs2 in any::<Reg>()) {
            // The target is pc plus the offset, folded at decoding.
            let offset = 2 * half;
            let e = Entry::decode(op.encode(rs1, rs2, offset).bits(), Region::TEXT.base());
            prop_assert_eq!(e.target, Target::Abs(Region::TEXT.base().wrapping_add(offset as i64 as u64)));
        }
    }
}
