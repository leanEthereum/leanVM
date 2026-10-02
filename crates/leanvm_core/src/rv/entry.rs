//! Decoded instructions: the classes, and the entries the bytecode table holds.
//!
//! A class is one table and, but for the extension-field product, one circuit.
//!
//! Its instructions differ only by a flag word, which selects what the class's one function does.
//!
//! The program is public, so each instruction word is decoded into an entry once, before any run.

use super::circuits::ClassCircuit;
use super::instruction::{ExtOp, ImmOp, Instruction, LoadOp, Opcode, RegOp, ShiftOp, StoreOp};
use super::register::{Reg, RegisterFile};
use super::semantics::{Alu, Div, Ext, Hash, InstructionClass, Load, Mul, Mulh, Outcome, Shift, Store, WordAccess};
use flock::circuit::Circuit;

/// An instruction class: one table, and one circuit unless its table proves it by identities.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum Class {
    /// Add, subtract, compare, bitwise logic, branches and jumps.
    Alu,
    /// Logical and arithmetic shifts.
    Shift,
    /// A byte, half word, word or double word read from memory.
    Load,
    /// A byte, half word, word or double word written to memory.
    Store,
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
    pub const fn nop(self) -> Option<Instruction> {
        let zero = Reg::ZERO;
        Some(match self {
            Self::Alu => ImmOp::Addi.encode(zero, zero, 0),
            Self::Shift => ShiftOp::Slli.encode(zero, zero, 0),
            Self::Load => LoadOp::Lb.encode(zero, zero, 0),
            Self::Store => StoreOp::Sb.encode(zero, zero, 0),
            Self::Mul => RegOp::Mul.encode(zero, zero, zero),
            Self::Mulh => RegOp::Mulhu.encode(zero, zero, zero),
            Self::Div => RegOp::Divu.encode(zero, zero, zero),
            Self::Hash => Instruction::r(Opcode::Custom0, 0, 0, zero, zero, zero),
            Self::Ext => ExtOp::Extmul.encode(Reg::RA, zero, zero),
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
    /// The next instruction, or the address the row computes for a `JALR`.
    Next,
    /// A fixed address, taken when the class says so: a branch or a `JAL`.
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
    /// The destination receives `pc + 4` instead of the class's result.
    pub link: bool,
    /// The next `pc` is the class's result.
    pub jalr: bool,
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
        link: false,
        jalr: false,
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
        link: false,
        jalr: false,
    };

    /// What this entry computes from its registers and, for a load or a store, the cell it names.
    ///
    /// The result holds whether or not a run could make the access.
    ///
    /// A hash or an extension-field product computes nothing here: its operands are the machine's to read.
    pub fn evaluate(&self, v1: u64, v2: u64, cell: u64) -> Outcome {
        let (flags, imm) = (self.flags, self.imm);
        let (out, taken, access) = match self.class {
            Class::Alu => {
                let (out, taken) = Alu { flags, v1, v2, imm }.eval();
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
            Class::Hash | Class::Ext | Class::Illegal => (0, false, None),
        };
        Outcome { out, taken, access }
    }

    /// The entry of the instruction `word` at address `pc`.
    ///
    /// The address is known, so `AUIPC` and the jump targets fold to constants.
    ///
    /// Every encoding rv64im does not define is the illegal entry, a reserved one included.
    pub fn decode(word: u32, pc: u64) -> Self {
        let ins = Instruction::from_bits(word);
        let (rd, f3, rs1, rs2, f7) = (ins.rd(), ins.funct3(), ins.rs1(), ins.rs2(), ins.funct7());

        // A register-register and a register-immediate instruction share one entry shape.
        //
        // - A register-register one reads rs1 and rs2, and has no immediate.
        // - A register-immediate one reads rs1 and x0, and has the immediate.
        let reg = |class, flags| Self::sequential(class, flags, rs1, rs2, rd, 0);
        let imm = |class, flags, imm| Self::sequential(class, flags, rs1, 0, rd, imm);

        let Some(opcode) = ins.opcode() else {
            return Self::ILLEGAL;
        };
        match opcode {
            // LUI and AUIPC: a constant added to x0.
            Opcode::Lui => Self::sequential(Class::Alu, 0, 0, 0, rd, ins.imm_u()),
            Opcode::Auipc => Self::sequential(Class::Alu, 0, 0, 0, rd, pc.wrapping_add(ins.imm_u())),

            // JAL: an unconditional jump to a fixed target, linking pc + 4.
            Opcode::Jal => Self {
                target: Target::Abs(pc.wrapping_add(ins.imm_j())),
                link: true,
                ..Self::sequential(Class::Alu, Alu::ALWAYS, 0, 0, rd, 0)
            },

            // JALR: a jump to rs1 + imm with bit 0 cleared, linking pc + 4.
            Opcode::Jalr if f3 == 0 => Self {
                link: true,
                jalr: true,
                ..imm(Class::Alu, Alu::CLEAR_BIT0, ins.imm_i())
            },

            // Branches: a comparison by subtraction, and a fixed target.
            Opcode::Branch => Alu::branch_flags(f3).map_or(Self::ILLEGAL, |flags| Self {
                target: Target::Abs(pc.wrapping_add(ins.imm_b())),
                ..Self::sequential(Class::Alu, flags, rs1, rs2, 0, 0)
            }),

            // Loads: the width and the extension.
            Opcode::Load => Load::flags_of(f3).map_or(Self::ILLEGAL, |flags| imm(Class::Load, flags, ins.imm_i())),

            // Stores: the width, from 1 to 8 bytes.
            Opcode::Store if f3 <= 3 => Self::sequential(Class::Store, f3 as u64, rs1, rs2, 0, ins.imm_s()),

            // Register-immediate arithmetic.
            Opcode::OpImm => match f3 {
                0 => imm(Class::Alu, 0, ins.imm_i()),
                2 => imm(Class::Alu, Alu::SUB | Alu::SEL_LT, ins.imm_i()),
                3 => imm(Class::Alu, Alu::SUB | Alu::SEL_LTU, ins.imm_i()),
                4 => imm(Class::Alu, Alu::SEL_XOR, ins.imm_i()),
                6 => imm(Class::Alu, Alu::SEL_OR, ins.imm_i()),
                7 => imm(Class::Alu, Alu::SEL_AND, ins.imm_i()),
                // A 64-bit shift amount has six bits, leaving six for the function.
                1 if ins.funct6() == 0 => imm(Class::Shift, 0, ins.shamt() as u64),
                5 if ins.funct6() == 0 => imm(Class::Shift, Shift::RIGHT, ins.shamt() as u64),
                5 if ins.funct6() == 0x10 => imm(Class::Shift, Shift::RIGHT | Shift::ARITH, ins.shamt() as u64),
                _ => Self::ILLEGAL,
            },

            // Register-immediate arithmetic on the low 32 bits: a shift amount has five bits.
            Opcode::OpImm32 => match (f3, f7) {
                (0, _) => imm(Class::Alu, Alu::WORD, ins.imm_i()),
                (1, 0) => imm(Class::Shift, Shift::WORD, rs2 as u64),
                (5, 0) => imm(Class::Shift, Shift::WORD | Shift::RIGHT, rs2 as u64),
                (5, 0x20) => imm(Class::Shift, Shift::WORD | Shift::RIGHT | Shift::ARITH, rs2 as u64),
                _ => Self::ILLEGAL,
            },

            // Register-register arithmetic, multiplication and division.
            Opcode::Op => match (f7, f3) {
                (0, 0) => reg(Class::Alu, 0),
                (0x20, 0) => reg(Class::Alu, Alu::SUB),
                (0, 1) => reg(Class::Shift, 0),
                (0, 2) => reg(Class::Alu, Alu::SUB | Alu::SEL_LT),
                (0, 3) => reg(Class::Alu, Alu::SUB | Alu::SEL_LTU),
                (0, 4) => reg(Class::Alu, Alu::SEL_XOR),
                (0, 5) => reg(Class::Shift, Shift::RIGHT),
                (0x20, 5) => reg(Class::Shift, Shift::RIGHT | Shift::ARITH),
                (0, 6) => reg(Class::Alu, Alu::SEL_OR),
                (0, 7) => reg(Class::Alu, Alu::SEL_AND),
                (1, 0) => reg(Class::Mul, 0),
                (1, 1) => reg(Class::Mulh, Mulh::SIGNED_1 | Mulh::SIGNED_2),
                (1, 2) => reg(Class::Mulh, Mulh::SIGNED_1),
                (1, 3) => reg(Class::Mulh, 0),
                (1, 4) => reg(Class::Div, Div::SIGNED),
                (1, 5) => reg(Class::Div, 0),
                (1, 6) => reg(Class::Div, Div::SIGNED | Div::REM),
                (1, 7) => reg(Class::Div, Div::REM),
                _ => Self::ILLEGAL,
            },

            // Register-register arithmetic on the low 32 bits.
            Opcode::Op32 => match (f7, f3) {
                (0, 0) => reg(Class::Alu, Alu::WORD),
                (0x20, 0) => reg(Class::Alu, Alu::SUB | Alu::WORD),
                (0, 1) => reg(Class::Shift, Shift::WORD),
                (0, 5) => reg(Class::Shift, Shift::WORD | Shift::RIGHT),
                (0x20, 5) => reg(Class::Shift, Shift::WORD | Shift::RIGHT | Shift::ARITH),
                (1, 0) => reg(Class::Mul, Mul::WORD),
                (1, 4) => reg(Class::Div, Div::WORD | Div::SIGNED),
                (1, 5) => reg(Class::Div, Div::WORD),
                (1, 6) => reg(Class::Div, Div::WORD | Div::SIGNED | Div::REM),
                (1, 7) => reg(Class::Div, Div::WORD | Div::REM),
                _ => Self::ILLEGAL,
            },

            // FENCE: a no-op, whatever its other fields hold.
            Opcode::MiscMem if f3 == 0 => Self::sequential(Class::Alu, 0, 0, 0, 0, 0),

            // The BLAKE2s compression: the block at rs1, the counter in rs2, no destination.
            //
            // Function 1 marks the final block.
            Opcode::Custom0 if f7 == 0 && rd == 0 && f3 <= 1 => {
                let flags = if f3 == 1 { Hash::FINAL } else { 0 };
                Self::sequential(Class::Hash, flags, rs1, rs2, 0, 0)
            }

            // The extension-field multiplication: the function's bits accumulate, and make rs2 a base-field element.
            //
            // Every register is an address, and address 0 is unmapped, so rd = x0 is undefined.
            Opcode::Custom1 if f7 == 0 && f3 <= 3 && rd != 0 => {
                Self::sequential(Class::Ext, f3 as u64, rs1, rs2, rd, 0)
            }

            // ECALL is a jump to the halt slot.
            //
            // EBREAK and the CSR instructions share its opcode and stay illegal.
            Opcode::System if ins == Instruction::ECALL => Self::EXIT,

            _ => Self::ILLEGAL,
        }
    }

    /// Whether this entry jumps to the halt slot.
    pub fn is_exit(&self) -> bool {
        self.target == Target::Halt
    }

    /// Whether the entry obeys the rules that make the bytecode table RISC-V.
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
    /// - the control-flow fields match what the flags select;
    /// - a field the class's table holds at a constant has that constant.
    pub fn is_well_formed(&self) -> bool {
        // An illegal entry has one inert form.
        if self.class == Class::Illegal {
            return *self == Self::ILLEGAL;
        }

        // Only the canonical exit may jump to the halt slot.
        if self.is_exit() {
            return *self == Self::EXIT;
        }

        // Register numbers, and flags the class's circuit is written for.
        let operands = self.a1 < 32 && self.a2 < 32 && (1..=RegisterFile::SINK).contains(&self.ad);
        let flags = self.class.legal_flags().contains(&self.flags);
        operands && flags && self.has_consistent_control() && self.has_table_constants()
    }

    /// An entry with no control flow.
    ///
    /// A destination of `x0` becomes the sink, which nothing reads.
    const fn sequential(class: Class, flags: u64, a1: u32, a2: u32, rd: u32, imm: u64) -> Self {
        Self {
            class,
            flags,
            a1: a1 as u8,
            a2: a2 as u8,
            ad: if rd == 0 { RegisterFile::SINK } else { rd as u8 },
            imm,
            target: Target::Next,
            link: false,
            jalr: false,
        }
    }

    /// Whether the target, link and jalr fields match the flags.
    ///
    /// - A `JALR` links, and jumps to the address it computes.
    /// - A `JAL` links, and jumps to a fixed target.
    /// - A branch jumps to a fixed target.
    /// - Anything else does neither, and falls through.
    fn has_consistent_control(&self) -> bool {
        // Only the ALU moves control.
        let fixed = matches!(self.target, Target::Abs(_));
        let next = self.target == Target::Next;
        if self.class != Class::Alu {
            return next && !self.link && !self.jalr;
        }

        // The flags say which control shape the entry must have.
        match self.flags {
            Alu::CLEAR_BIT0 => self.jalr && self.link && next,
            Alu::ALWAYS => !self.jalr && self.link && fixed,
            flags if flags & Alu::BRANCHES != 0 => !self.jalr && !self.link && fixed,
            _ => !self.jalr && !self.link && next,
        }
    }

    /// Whether the fields a class's table fixes hold their constants.
    ///
    /// - A load reads no `rs2`, so its second register is `x0`.
    /// - A store writes no `rd`, so its destination is the sink.
    /// - A hash writes no `rd` and has no immediate.
    /// - An extension-field product reads `rd` as an address, so it names a register, and has no immediate.
    const fn has_table_constants(&self) -> bool {
        match self.class {
            Class::Load => self.a2 == 0,
            Class::Store => self.ad == RegisterFile::SINK,
            Class::Hash => self.ad == RegisterFile::SINK && self.imm == 0,
            Class::Ext => self.ad < RegisterFile::SINK && self.imm == 0,
            _ => true,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::rv::Region;
    use crate::rv::instruction::{BranchOp, ExtOp, ImmOp, LoadOp, RegOp, ShiftOp, StoreOp};
    use crate::rv::register::Reg;
    use proptest::prelude::*;

    #[test]
    fn only_the_canonical_exit_jumps_to_the_halt_slot() {
        // Fixture: the decoded ecall.
        let exit = Entry::decode(0x73, 0);
        assert_eq!(exit, Entry::EXIT);
        assert!(exit.is_well_formed());

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
            Entry { link: true, ..exit },
            Entry { jalr: true, ..exit },
        ] {
            assert!(!malformed.is_well_formed(), "{malformed:?}");
        }
    }

    #[test]
    fn a_skipped_register_access_names_its_constant() {
        // Invariant: a load's rs2 is x0, and a store's rd is the sink.
        //
        // Fixture: `ld a0, 0(a1)` and `sd a0, 0(a1)`.
        let (load, store) = (Entry::decode(0x0005_b503, 0), Entry::decode(0x00a5_b023, 0));
        assert_eq!((load.class, store.class), (Class::Load, Class::Store));
        assert!(load.is_well_formed() && store.is_well_formed());

        // Mutation: the load reads x1 as rs2, the store writes x1.
        assert!(!Entry { a2: 1, ..load }.is_well_formed());
        assert!(!Entry { ad: 1, ..store }.is_well_formed());
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

        for (&flags, word) in Alu::LEGAL.iter().zip(witnesses) {
            let decoded = Entry::decode(word, Region::TEXT.base());
            assert_eq!((decoded.class, decoded.flags), (Class::Alu, flags));

            // Mutation: every target kind, link and jalr.
            //
            // Only the decoded shape is well formed, whatever the fixed address.
            for target in [
                Target::Next,
                Target::Abs(Region::TEXT.base()),
                Target::Abs(Region::TEXT.base() + 4),
            ] {
                for link in [false, true] {
                    for jalr in [false, true] {
                        let candidate = Entry {
                            target,
                            link,
                            jalr,
                            ..decoded
                        };
                        let same_kind = matches!(
                            (target, decoded.target),
                            (Target::Next, Target::Next) | (Target::Abs(_), Target::Abs(_))
                        );
                        let expected = same_kind && link == decoded.link && jalr == decoded.jalr;
                        assert_eq!(candidate.is_well_formed(), expected, "{candidate:?}");
                    }
                }
            }
        }
    }

    #[test]
    fn decoded_entries_are_well_formed() {
        // The forms the sweep below misses: they need rd = x0.
        //
        //     ecall, blake2s, blake2s on the final block
        for word in [0x73, 0x0000_000b, 0x0000_100b] {
            assert!(Entry::decode(word, Region::TEXT.base()).is_well_formed());
        }

        // Every opcode and function, every 12-bit top, with fixed registers.
        //
        // Fixture: rd = x21 and rs1 = x10, so every register field is nonzero.
        for opcode in 0..128u32 {
            for f3 in 0..8u32 {
                for top in 0..(1u32 << 12) {
                    let word = opcode | (f3 << 12) | (top << 20) | (0x15 << 7) | (0x0a << 15);
                    let e = Entry::decode(word, Region::TEXT.base());
                    assert!(e.is_well_formed(), "{word:#010x} decodes to {e:?}");
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
            Class::Mul,
            Class::Mulh,
            Class::Div,
            Class::Hash,
        ];
        assert_eq!(Class::Illegal.nop(), None);

        // Each no-op decodes to its class, reads x0 twice, writes the sink, and has no immediate.
        for class in classes {
            let e = Entry::decode(class.nop().expect("a legal class").bits(), Region::TEXT.base());
            assert_eq!(
                (e.class, e.a1, e.a2, e.ad, e.imm),
                (class, 0, 0, RegisterFile::SINK, 0),
                "{class:?}"
            );
            assert!(e.is_well_formed());
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
            0x0000_402b | 5 << 7, // an extension-field product with function 4
            0x0200_002b | 5 << 7, // an extension-field product with a function-7 bit set
            0x0000_002b,          // an extension-field product into the address in x0
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
            prop_assert!(e.is_well_formed());
        }

        #[test]
        fn extension_field_operations_decode_to_their_flags(op in proptest::sample::select(&ExtOp::ALL[..]), rd in any::<Reg>(), rs1 in any::<Reg>(), rs2 in any::<Reg>()) {
            // Invariant: the flags are the function's bits, and every register is read as itself.
            //
            //     extmul 0, extmac 1 (accumulate), extmulk 2 (base field), extmack 3
            let e = Entry::decode(op.encode(rd, rs1, rs2).bits(), Region::TEXT.base());
            if rd == Reg::ZERO {
                // The address in x0 would be 0, which is unmapped.
                prop_assert_eq!(e, Entry::ILLEGAL);
            } else {
                let flags = ExtOp::ALL.iter().position(|&o| o == op).unwrap() as u64;
                prop_assert_eq!((e.class, e.flags), (Class::Ext, flags));
                prop_assert_eq!((e.a1, e.a2, e.ad), (rs1.index() as u8, rs2.index() as u8, rd.index() as u8));
                prop_assert!(e.is_well_formed());
                prop_assert!(!Entry { ad: RegisterFile::SINK, ..e }.is_well_formed(), "an address in the sink");
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
            let (l, s) = (Entry::decode(load.encode(rs2, rs1, offset).bits(), 0), Entry::decode(store.encode(rs2, rs1, offset).bits(), 0));
            prop_assert_eq!((l.class, l.flags & Load::LOG_WIDTH, l.imm), (Class::Load, load.log_width() as u64, offset as i64 as u64));
            prop_assert_eq!((s.class, s.flags, s.imm), (Class::Store, store.log_width() as u64, offset as i64 as u64));
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
