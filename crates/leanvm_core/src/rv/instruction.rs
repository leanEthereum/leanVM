//! Encoded instructions: the 32-bit formats, and every rv64im operation typed by its format.
//!
//! Every format keeps the opcode in bits 0 to 6.
//!
//! The register fields never move:
//!
//! - `rd` in bits 7 to 11;
//! - `rs1` in bits 15 to 19;
//! - `rs2` in bits 20 to 24.
//!
//! The six formats differ in where the immediate goes:
//!
//! - R has no immediate, and a `funct7` in bits 25 to 31;
//! - I has a 12-bit immediate in bits 20 to 31;
//! - S splits its immediate around `rs2`;
//! - B is S with the bits of an even offset reordered;
//! - U has a 20-bit upper immediate in bits 12 to 31;
//! - J is U with the bits of an even offset reordered.
//!
//! One enum per format means the assembler cannot emit, say, a load with a branch's operands.

use std::ops::Range;

use super::register::Reg;

/// Sign-extend the low bits of a 32-bit value to a 64-bit word.
const fn sign_extend(value: u32, bits: u32) -> u64 {
    // Move the sign bit to bit 63, then shift back arithmetically.
    (((value as u64) << (u64::BITS - bits)) as i64 >> (u64::BITS - bits)) as u64
}

/// A contiguous field in a 32-bit instruction.
#[derive(Clone, Copy)]
struct BitField {
    /// The position of the least significant bit.
    start: u32,
    /// The number of bits in the field.
    width: u32,
}

impl BitField {
    /// A nonempty range of instruction bits, with an exclusive end.
    const fn new(bits: Range<u32>) -> Self {
        // Every field lies wholly inside one instruction.
        assert!(bits.start < bits.end && bits.end <= u32::BITS);
        Self {
            start: bits.start,
            width: bits.end - bits.start,
        }
    }

    /// The mask for a field value before placement.
    const fn mask(self) -> u32 {
        u32::MAX >> (u32::BITS - self.width)
    }

    /// Extract the field as an unsigned value.
    const fn extract(self, instruction: u32) -> u32 {
        (instruction >> self.start) & self.mask()
    }

    /// Place the low field-width bits of a value into the instruction.
    const fn place(self, value: u32) -> u32 {
        self.shift(value & self.mask())
    }

    /// Shift a value to the field's position without masking it.
    const fn shift(self, value: u32) -> u32 {
        value << self.start
    }
}

/// A major opcode: the low seven bits of every instruction, naming its format and family.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
#[repr(u32)]
pub enum Opcode {
    /// Loads.
    Load = 0x03,
    /// The custom-0 space, which holds the BLAKE2s compression.
    Custom0 = 0x0b,
    /// The custom-1 space, which holds the extension-field multiplication.
    Custom1 = 0x2b,
    /// `FENCE`.
    MiscMem = 0x0f,
    /// Register-immediate arithmetic.
    OpImm = 0x13,
    /// `AUIPC`.
    Auipc = 0x17,
    /// Register-immediate arithmetic on the low 32 bits.
    OpImm32 = 0x1b,
    /// Stores.
    Store = 0x23,
    /// Register-register arithmetic, multiplication and division.
    Op = 0x33,
    /// `LUI`.
    Lui = 0x37,
    /// Register-register arithmetic on the low 32 bits.
    Op32 = 0x3b,
    /// Conditional branches.
    Branch = 0x63,
    /// `JALR`.
    Jalr = 0x67,
    /// `JAL`.
    Jal = 0x6f,
    /// `ECALL`, `EBREAK` and the CSR instructions.
    System = 0x73,
}

impl Opcode {
    /// Every opcode the machine uses: rv64im's, and the two custom spaces.
    pub const ALL: [Self; 15] = [
        Self::Load,
        Self::Custom0,
        Self::Custom1,
        Self::MiscMem,
        Self::OpImm,
        Self::Auipc,
        Self::OpImm32,
        Self::Store,
        Self::Op,
        Self::Lui,
        Self::Op32,
        Self::Branch,
        Self::Jalr,
        Self::Jal,
        Self::System,
    ];

    /// The opcode with these seven bits.
    ///
    /// Returns `None` for an opcode the machine does not use.
    pub const fn from_bits(bits: u32) -> Option<Self> {
        Some(match bits {
            0x03 => Self::Load,
            0x0b => Self::Custom0,
            0x2b => Self::Custom1,
            0x0f => Self::MiscMem,
            0x13 => Self::OpImm,
            0x17 => Self::Auipc,
            0x1b => Self::OpImm32,
            0x23 => Self::Store,
            0x33 => Self::Op,
            0x37 => Self::Lui,
            0x3b => Self::Op32,
            0x63 => Self::Branch,
            0x67 => Self::Jalr,
            0x6f => Self::Jal,
            0x73 => Self::System,
            _ => return None,
        })
    }

    /// The opcode's seven bits.
    pub const fn bits(self) -> u32 {
        self as u32
    }
}

/// One encoded instruction.
///
/// The accessors read a field whatever the format.
///
/// The constructors write one format, masking each immediate to its width.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct Instruction(u32);

impl Instruction {
    /// The major opcode.
    const OPCODE: BitField = BitField::new(0..7);
    /// The destination register.
    const RD: BitField = BitField::new(7..12);
    /// The low function selector.
    const FUNCT3: BitField = BitField::new(12..15);
    /// The first source register.
    const RS1: BitField = BitField::new(15..20);
    /// The second source register or a 32-bit shift amount.
    const RS2: BitField = BitField::new(20..25);
    /// A 64-bit shift amount.
    const SHAMT: BitField = BitField::new(20..26);
    /// The function selector above a 64-bit shift amount.
    const FUNCT6: BitField = BitField::new(26..32);
    /// The high function selector or the high seven store-immediate bits.
    const FUNCT7: BitField = BitField::new(25..32);
    /// A contiguous 12-bit immediate.
    const IMM_I: BitField = BitField::new(20..32);
    /// A contiguous 20-bit upper immediate.
    const IMM_U: BitField = BitField::new(12..32);
    /// The sign bit of every immediate format.
    const SIGN: BitField = BitField::new(31..32);
    /// Branch-offset bit 11.
    const B_IMM_11: BitField = BitField::new(7..8);
    /// Branch-offset bits 1 through 4.
    const B_IMM_4_1: BitField = BitField::new(8..12);
    /// Branch-offset bits 5 through 10.
    const B_IMM_10_5: BitField = BitField::new(25..31);
    /// Jump-offset bits 12 through 19.
    const J_IMM_19_12: BitField = BitField::new(12..20);
    /// Jump-offset bit 11.
    const J_IMM_11: BitField = BitField::new(20..21);
    /// Jump-offset bits 1 through 10.
    const J_IMM_10_1: BitField = BitField::new(21..31);

    /// `ecall`, the only system instruction rv64im runs here.
    pub const ECALL: Self = Self(Opcode::System.bits());

    /// The instruction with these bits.
    pub const fn from_bits(bits: u32) -> Self {
        Self(bits)
    }

    /// The instruction's bits.
    pub const fn bits(self) -> u32 {
        self.0
    }

    /// The opcode, bits 0 to 6.
    ///
    /// Returns `None` for an opcode the machine does not use.
    pub const fn opcode(self) -> Option<Opcode> {
        Opcode::from_bits(Self::OPCODE.extract(self.0))
    }

    /// Bits 7 to 11: the destination register.
    pub const fn rd(self) -> u32 {
        Self::RD.extract(self.0)
    }

    /// Bits 12 to 14.
    pub const fn funct3(self) -> u32 {
        Self::FUNCT3.extract(self.0)
    }

    /// Bits 15 to 19: the first source register.
    pub const fn rs1(self) -> u32 {
        Self::RS1.extract(self.0)
    }

    /// Bits 20 to 24: the second source register, or a 32-bit shift's amount.
    pub const fn rs2(self) -> u32 {
        Self::RS2.extract(self.0)
    }

    /// Bits 20 to 25: a 64-bit shift's amount.
    pub const fn shamt(self) -> u32 {
        Self::SHAMT.extract(self.0)
    }

    /// Bits 26 to 31: what a 64-bit shift leaves of its function field.
    pub const fn funct6(self) -> u32 {
        Self::FUNCT6.extract(self.0)
    }

    /// Bits 25 to 31.
    pub const fn funct7(self) -> u32 {
        Self::FUNCT7.extract(self.0)
    }

    /// The I-type immediate, sign-extended.
    pub const fn imm_i(self) -> u64 {
        sign_extend(Self::IMM_I.extract(self.0), Self::IMM_I.width)
    }

    /// The S-type immediate, sign-extended.
    pub const fn imm_s(self) -> u64 {
        // The low five bits occupy the destination field, followed by seven high bits.
        sign_extend((self.funct7() << Self::RD.width) | self.rd(), Self::IMM_I.width)
    }

    /// The B-type offset, sign-extended.
    pub const fn imm_b(self) -> u64 {
        let w = self.0;
        // Bits 12, 11, 10..5 and 4..1, scattered over the word.
        let offset = (Self::SIGN.extract(w) << 12)
            | (Self::B_IMM_11.extract(w) << 11)
            | (Self::B_IMM_10_5.extract(w) << 5)
            | (Self::B_IMM_4_1.extract(w) << 1);
        sign_extend(offset, 13)
    }

    /// The U-type immediate, already shifted into bits 12 to 31, sign-extended.
    pub const fn imm_u(self) -> u64 {
        // Keep the upper immediate in position before extending its sign.
        sign_extend(Self::IMM_U.place(Self::IMM_U.extract(self.0)), u32::BITS)
    }

    /// The J-type offset, sign-extended.
    pub const fn imm_j(self) -> u64 {
        let w = self.0;
        // Bits 20, 19..12, 11 and 10..1, scattered over the word.
        let offset = (Self::SIGN.extract(w) << 20)
            | (Self::J_IMM_19_12.extract(w) << 12)
            | (Self::J_IMM_11.extract(w) << 11)
            | (Self::J_IMM_10_1.extract(w) << 1);
        sign_extend(offset, 21)
    }

    /// An R-type instruction.
    pub const fn r(opcode: Opcode, funct3: u32, funct7: u32, rd: Reg, rs1: Reg, rs2: Reg) -> Self {
        Self(
            opcode.bits()
                | Self::RD.place(rd.index() as u32)
                | Self::FUNCT3.shift(funct3)
                | Self::RS1.place(rs1.index() as u32)
                | Self::RS2.place(rs2.index() as u32)
                | Self::FUNCT7.shift(funct7),
        )
    }

    /// An I-type instruction, the immediate's low 12 bits kept.
    pub const fn i(opcode: Opcode, funct3: u32, rd: Reg, rs1: Reg, imm: i32) -> Self {
        Self(
            opcode.bits()
                | Self::RD.place(rd.index() as u32)
                | Self::FUNCT3.shift(funct3)
                | Self::RS1.place(rs1.index() as u32)
                | Self::IMM_I.place(imm as u32),
        )
    }

    /// A store, the offset's low 12 bits kept.
    pub const fn s(funct3: u32, rs1: Reg, rs2: Reg, offset: i32) -> Self {
        let o = offset as u32;
        Self(
            Opcode::Store.bits()
                | Self::RD.place(o)
                | Self::FUNCT3.shift(funct3)
                | Self::RS1.place(rs1.index() as u32)
                | Self::RS2.place(rs2.index() as u32)
                | Self::FUNCT7.place(o >> Self::RD.width),
        )
    }

    /// A conditional branch, the offset's bits 1 to 12 kept.
    pub const fn b(funct3: u32, rs1: Reg, rs2: Reg, offset: i32) -> Self {
        let o = offset as u32;
        Self(
            Opcode::Branch.bits()
                | Self::B_IMM_11.place(o >> 11)
                | Self::B_IMM_4_1.place(o >> 1)
                | Self::FUNCT3.shift(funct3)
                | Self::RS1.place(rs1.index() as u32)
                | Self::RS2.place(rs2.index() as u32)
                | Self::B_IMM_10_5.place(o >> 5)
                | Self::SIGN.place(o >> 12),
        )
    }

    /// A U-type instruction, `imm20` becoming bits 12 to 31.
    pub const fn u(opcode: Opcode, rd: Reg, imm20: u32) -> Self {
        Self(opcode.bits() | Self::RD.place(rd.index() as u32) | Self::IMM_U.place(imm20))
    }

    /// A `JAL`, the offset's bits 1 to 20 kept.
    pub const fn j(rd: Reg, offset: i32) -> Self {
        let o = offset as u32;
        Self(
            Opcode::Jal.bits()
                | Self::RD.place(rd.index() as u32)
                | Self::J_IMM_19_12.place(o >> 12)
                | Self::J_IMM_11.place(o >> 11)
                | Self::J_IMM_10_1.place(o >> 1)
                | Self::SIGN.place(o >> 20),
        )
    }
}

impl From<Instruction> for u32 {
    fn from(instruction: Instruction) -> Self {
        instruction.bits()
    }
}

/// Declares one format's operations: the enum, its full list, mnemonics, and encoding fields.
macro_rules! operations {
    (
        $(#[$meta:meta])*
        $name:ident: $fields:ty {
            $($(#[$doc:meta])* $variant:ident = $mnemonic:literal => $value:expr,)*
        }
    ) => {
        $(#[$meta])*
        #[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
        pub enum $name {
            $($(#[$doc])* $variant,)*
        }

        impl $name {
            /// Every operation of this format.
            pub const ALL: [Self; [$($mnemonic),*].len()] = [$(Self::$variant),*];

            /// The assembly mnemonic.
            pub const fn mnemonic(self) -> &'static str {
                match self {
                    $(Self::$variant => $mnemonic,)*
                }
            }

            /// The encoding fields that tell this operation apart from the others of its format.
            const fn fields(self) -> $fields {
                match self {
                    $(Self::$variant => $value,)*
                }
            }
        }
    };
}

operations! {
    /// A register-register operation: `op rd, rs1, rs2`, as `(opcode, funct3, funct7)`.
    RegOp: (Opcode, u32, u32) {
        /// `rd = rs1 + rs2`.
        Add = "add" => (Opcode::Op, 0, 0),
        /// `rd = rs1 - rs2`.
        Sub = "sub" => (Opcode::Op, 0, 0x20),
        /// `rd = rs1 << rs2`.
        Sll = "sll" => (Opcode::Op, 1, 0),
        /// `rd = rs1 < rs2`, signed.
        Slt = "slt" => (Opcode::Op, 2, 0),
        /// `rd = rs1 < rs2`, unsigned.
        Sltu = "sltu" => (Opcode::Op, 3, 0),
        /// `rd = rs1 ^ rs2`.
        Xor = "xor" => (Opcode::Op, 4, 0),
        /// `rd = rs1 >> rs2`, logical.
        Srl = "srl" => (Opcode::Op, 5, 0),
        /// `rd = rs1 >> rs2`, arithmetic.
        Sra = "sra" => (Opcode::Op, 5, 0x20),
        /// `rd = rs1 | rs2`.
        Or = "or" => (Opcode::Op, 6, 0),
        /// `rd = rs1 & rs2`.
        And = "and" => (Opcode::Op, 7, 0),
        /// The low word of `rs1 * rs2`.
        Mul = "mul" => (Opcode::Op, 0, 1),
        /// The high word of `rs1 * rs2`, both signed.
        Mulh = "mulh" => (Opcode::Op, 1, 1),
        /// The high word of `rs1 * rs2`, `rs1` signed.
        Mulhsu = "mulhsu" => (Opcode::Op, 2, 1),
        /// The high word of `rs1 * rs2`, both unsigned.
        Mulhu = "mulhu" => (Opcode::Op, 3, 1),
        /// `rd = rs1 / rs2`, signed.
        Div = "div" => (Opcode::Op, 4, 1),
        /// `rd = rs1 / rs2`, unsigned.
        Divu = "divu" => (Opcode::Op, 5, 1),
        /// `rd = rs1 % rs2`, signed.
        Rem = "rem" => (Opcode::Op, 6, 1),
        /// `rd = rs1 % rs2`, unsigned.
        Remu = "remu" => (Opcode::Op, 7, 1),
        /// `add` on the low 32 bits, sign-extended.
        Addw = "addw" => (Opcode::Op32, 0, 0),
        /// `sub` on the low 32 bits, sign-extended.
        Subw = "subw" => (Opcode::Op32, 0, 0x20),
        /// `sll` on the low 32 bits, sign-extended.
        Sllw = "sllw" => (Opcode::Op32, 1, 0),
        /// `srl` on the low 32 bits, sign-extended.
        Srlw = "srlw" => (Opcode::Op32, 5, 0),
        /// `sra` on the low 32 bits, sign-extended.
        Sraw = "sraw" => (Opcode::Op32, 5, 0x20),
        /// `mul` on the low 32 bits, sign-extended.
        Mulw = "mulw" => (Opcode::Op32, 0, 1),
        /// `div` on the low 32 bits, sign-extended.
        Divw = "divw" => (Opcode::Op32, 4, 1),
        /// `divu` on the low 32 bits, sign-extended.
        Divuw = "divuw" => (Opcode::Op32, 5, 1),
        /// `rem` on the low 32 bits, sign-extended.
        Remw = "remw" => (Opcode::Op32, 6, 1),
        /// `remu` on the low 32 bits, sign-extended.
        Remuw = "remuw" => (Opcode::Op32, 7, 1),
    }
}

operations! {
    /// A register-immediate operation: `op rd, rs1, imm`, as `(opcode, funct3)`.
    ImmOp: (Opcode, u32) {
        /// `rd = rs1 + imm`.
        Addi = "addi" => (Opcode::OpImm, 0),
        /// `rd = rs1 < imm`, signed.
        Slti = "slti" => (Opcode::OpImm, 2),
        /// `rd = rs1 < imm`, unsigned.
        Sltiu = "sltiu" => (Opcode::OpImm, 3),
        /// `rd = rs1 ^ imm`.
        Xori = "xori" => (Opcode::OpImm, 4),
        /// `rd = rs1 | imm`.
        Ori = "ori" => (Opcode::OpImm, 6),
        /// `rd = rs1 & imm`.
        Andi = "andi" => (Opcode::OpImm, 7),
        /// `addi` on the low 32 bits, sign-extended.
        Addiw = "addiw" => (Opcode::OpImm32, 0),
    }
}

operations! {
    /// A shift by an immediate: `op rd, rs1, amount`, as `(opcode, funct3, high bits, amount bits)`.
    ShiftOp: (Opcode, u32, u32, u32) {
        /// `rd = rs1 << amount`.
        Slli = "slli" => (Opcode::OpImm, 1, 0, 6),
        /// `rd = rs1 >> amount`, logical.
        Srli = "srli" => (Opcode::OpImm, 5, 0, 6),
        /// `rd = rs1 >> amount`, arithmetic.
        Srai = "srai" => (Opcode::OpImm, 5, 0x400, 6),
        /// `slli` on the low 32 bits, sign-extended.
        Slliw = "slliw" => (Opcode::OpImm32, 1, 0, 5),
        /// `srli` on the low 32 bits, sign-extended.
        Srliw = "srliw" => (Opcode::OpImm32, 5, 0, 5),
        /// `srai` on the low 32 bits, sign-extended.
        Sraiw = "sraiw" => (Opcode::OpImm32, 5, 0x400, 5),
    }
}

operations! {
    /// A load: `op rd, offset(rs1)`, as its `funct3`.
    LoadOp: u32 {
        /// A byte, sign-extended.
        Lb = "lb" => 0,
        /// A half word, sign-extended.
        Lh = "lh" => 1,
        /// A word, sign-extended.
        Lw = "lw" => 2,
        /// A double word.
        Ld = "ld" => 3,
        /// A byte, zero-extended.
        Lbu = "lbu" => 4,
        /// A half word, zero-extended.
        Lhu = "lhu" => 5,
        /// A word, zero-extended.
        Lwu = "lwu" => 6,
    }
}

operations! {
    /// A store: `op rs2, offset(rs1)`, as its `funct3`.
    StoreOp: u32 {
        /// The low byte.
        Sb = "sb" => 0,
        /// The low half word.
        Sh = "sh" => 1,
        /// The low word.
        Sw = "sw" => 2,
        /// The double word.
        Sd = "sd" => 3,
    }
}

operations! {
    /// A conditional branch: `op rs1, rs2, offset`, as its `funct3`.
    BranchOp: u32 {
        /// Taken when `rs1 == rs2`.
        Beq = "beq" => 0,
        /// Taken when `rs1 != rs2`.
        Bne = "bne" => 1,
        /// Taken when `rs1 < rs2`, signed.
        Blt = "blt" => 4,
        /// Taken when `rs1 >= rs2`, signed.
        Bge = "bge" => 5,
        /// Taken when `rs1 < rs2`, unsigned.
        Bltu = "bltu" => 6,
        /// Taken when `rs1 >= rs2`, unsigned.
        Bgeu = "bgeu" => 7,
    }
}

operations! {
    /// An extension-field multiplication: `op rd, rs1, rs2`, every register an address, as its `funct3`.
    ///
    /// Bit 0 of the function accumulates into `rd`, and bit 1 makes `rs2` a base-field element.
    ExtOp: u32 {
        /// `E[rd] = E[rs1] * E[rs2]`.
        Extmul = "extmul" => 0,
        /// `E[rd] = E[rd] + E[rs1] * E[rs2]`.
        Extmac = "extmac" => 1,
        /// `E[rd] = E[rs1] * K[rs2]`.
        Extmulk = "extmulk" => 2,
        /// `E[rd] = E[rd] + E[rs1] * K[rs2]`.
        Extmack = "extmack" => 3,
    }
}

impl RegOp {
    /// The instruction `op rd, rs1, rs2`.
    pub const fn encode(self, rd: Reg, rs1: Reg, rs2: Reg) -> Instruction {
        let (opcode, funct3, funct7) = self.fields();
        Instruction::r(opcode, funct3, funct7, rd, rs1, rs2)
    }
}

impl ImmOp {
    /// The instruction `op rd, rs1, imm`, the immediate's low 12 bits kept.
    pub const fn encode(self, rd: Reg, rs1: Reg, imm: i32) -> Instruction {
        let (opcode, funct3) = self.fields();
        Instruction::i(opcode, funct3, rd, rs1, imm)
    }
}

impl ShiftOp {
    /// How many bits the amount has: 6, or 5 on the low 32 bits.
    pub const fn amount_bits(self) -> u32 {
        self.fields().3
    }

    /// The instruction `op rd, rs1, amount`, the amount's low bits kept.
    pub const fn encode(self, rd: Reg, rs1: Reg, amount: u32) -> Instruction {
        let (opcode, funct3, high, bits) = self.fields();
        // The amount shares the immediate with the function's high bits.
        let amount = amount & ((1 << bits) - 1);
        Instruction::i(opcode, funct3, rd, rs1, (high | amount) as i32)
    }
}

impl LoadOp {
    /// The base-two logarithm of the width in bytes.
    pub const fn log_width(self) -> u32 {
        self.fields() & 3
    }

    /// The instruction `op rd, offset(rs1)`, the offset's low 12 bits kept.
    pub const fn encode(self, rd: Reg, rs1: Reg, offset: i32) -> Instruction {
        Instruction::i(Opcode::Load, self.fields(), rd, rs1, offset)
    }
}

impl StoreOp {
    /// The base-two logarithm of the width in bytes.
    pub const fn log_width(self) -> u32 {
        self.fields()
    }

    /// The instruction `op rs2, offset(rs1)`, the offset's low 12 bits kept.
    pub const fn encode(self, rs2: Reg, rs1: Reg, offset: i32) -> Instruction {
        Instruction::s(self.fields(), rs1, rs2, offset)
    }
}

impl ExtOp {
    /// The instruction `op rd, rs1, rs2`.
    pub const fn encode(self, rd: Reg, rs1: Reg, rs2: Reg) -> Instruction {
        Instruction::r(Opcode::Custom1, self.fields(), 0, rd, rs1, rs2)
    }
}

impl BranchOp {
    /// The instruction `op rs1, rs2, offset`, the offset's bits 1 to 12 kept.
    pub const fn encode(self, rs1: Reg, rs2: Reg, offset: i32) -> Instruction {
        Instruction::b(self.fields(), rs1, rs2, offset)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::rv::register::Reg;
    use proptest::prelude::*;
    use std::collections::HashSet;

    proptest! {
        #[test]
        fn encoded_formats_match_bit_layout(
            opcode in proptest::sample::select(&Opcode::ALL[..]),
            funct3 in any::<u32>(), funct7 in any::<u32>(), value in any::<u32>(),
            rd in any::<Reg>(), rs1 in any::<Reg>(), rs2 in any::<Reg>(),
        ) {
            // Independent ISA formulas cover all immediate bits, including truncation and odd offsets.
            let d = (rd.index() as u32) << 7;
            let a = (rs1.index() as u32) << 15;
            let b = (rs2.index() as u32) << 20;
            let f = funct3 << 12;
            let expected = [
                opcode.bits() | d | f | a | b | (funct7 << 25),
                opcode.bits() | d | f | a | ((value & 0xfff) << 20),
                0x23 | ((value & 31) << 7) | f | a | b | (((value >> 5) & 0x7f) << 25),
                0x63 | (((value >> 11) & 1) << 7) | (((value >> 1) & 0xf) << 8)
                    | f | a | b | (((value >> 5) & 0x3f) << 25) | (((value >> 12) & 1) << 31),
                opcode.bits() | d | ((value & 0xf_ffff) << 12),
                0x6f | d | (((value >> 12) & 0xff) << 12) | (((value >> 11) & 1) << 20)
                    | (((value >> 1) & 0x3ff) << 21) | (((value >> 20) & 1) << 31),
            ];

            // Function fields retain their full shifted values, even outside the legal encodings.
            let actual = [
                Instruction::r(opcode, funct3, funct7, rd, rs1, rs2).bits(),
                Instruction::i(opcode, funct3, rd, rs1, value as i32).bits(),
                Instruction::s(funct3, rs1, rs2, value as i32).bits(),
                Instruction::b(funct3, rs1, rs2, value as i32).bits(),
                Instruction::u(opcode, rd, value).bits(),
                Instruction::j(rd, value as i32).bits(),
            ];
            prop_assert_eq!(actual, expected);
        }

        #[test]
        fn accessors_match_bit_layout(word in any::<u32>()) {
            // Decode arbitrary words, including reserved instructions, using independent bit slices.
            let instruction = Instruction::from_bits(word);
            let opcode = Opcode::ALL.into_iter().find(|op| op.bits() == word & 0x7f);
            prop_assert_eq!(instruction.opcode(), opcode);
            prop_assert_eq!(
                [instruction.rd(), instruction.funct3(), instruction.rs1(), instruction.rs2(),
                    instruction.shamt(), instruction.funct6(), instruction.funct7()],
                [(word >> 7) & 31, (word >> 12) & 7, (word >> 15) & 31, (word >> 20) & 31,
                    (word >> 20) & 63, word >> 26, word >> 25],
            );

            // Assemble each immediate before extending its sign with native 32-bit arithmetic.
            let s = ((word >> 25) << 5) | ((word >> 7) & 31);
            let b = ((word >> 31) << 12) | (((word >> 7) & 1) << 11)
                | (((word >> 25) & 0x3f) << 5) | (((word >> 8) & 0xf) << 1);
            let j = ((word >> 31) << 20) | (((word >> 12) & 0xff) << 12)
                | (((word >> 20) & 1) << 11) | (((word >> 21) & 0x3ff) << 1);
            prop_assert_eq!(
                [instruction.imm_i(), instruction.imm_s(), instruction.imm_b(), instruction.imm_u(), instruction.imm_j()],
                [((word as i32) >> 20) as i64 as u64,
                    (((s as i32) << 20) >> 20) as i64 as u64,
                    (((b as i32) << 19) >> 19) as i64 as u64,
                    (word & 0xffff_f000) as i32 as i64 as u64,
                    (((j as i32) << 11) >> 11) as i64 as u64],
            );
        }

        #[test]
        fn r_type_fields_round_trip(funct3 in 0u32..8, funct7 in 0u32..128, rd in any::<Reg>(), rs1 in any::<Reg>(), rs2 in any::<Reg>()) {
            // Every field written comes back from its accessor.
            let ins = Instruction::r(Opcode::Op, funct3, funct7, rd, rs1, rs2);
            prop_assert_eq!(
                (ins.opcode(), ins.funct3(), ins.funct7(), ins.rd(), ins.rs1(), ins.rs2()),
                (Some(Opcode::Op), funct3, funct7, rd.index() as u32, rs1.index() as u32, rs2.index() as u32)
            );
        }

        #[test]
        fn i_and_s_immediates_round_trip(imm in -2048i32..2048, rd in any::<Reg>(), rs1 in any::<Reg>(), rs2 in any::<Reg>()) {
            // A 12-bit immediate comes back sign-extended to 64 bits.
            let expected = imm as i64 as u64;
            prop_assert_eq!(Instruction::i(Opcode::OpImm, 0, rd, rs1, imm).imm_i(), expected);
            prop_assert_eq!(Instruction::s(3, rs1, rs2, imm).imm_s(), expected);
        }

        #[test]
        fn b_and_j_offsets_round_trip(half_b in -2048i32..2048, half_j in -(1i32 << 19)..(1 << 19), rs1 in any::<Reg>(), rs2 in any::<Reg>()) {
            // Offsets are even, so the encodings drop bit 0.
            let (b, j) = (2 * half_b, 2 * half_j);
            prop_assert_eq!(Instruction::b(0, rs1, rs2, b).imm_b(), b as i64 as u64);
            prop_assert_eq!(Instruction::j(rs1, j).imm_j(), j as i64 as u64);
        }

        #[test]
        fn u_immediate_round_trips(imm20 in 0u32..1 << 20, rd in any::<Reg>()) {
            // The 20 bits land in bits 12..32, then sign-extend from bit 31.
            let expected = (imm20 << 12) as i32 as i64 as u64;
            prop_assert_eq!(Instruction::u(Opcode::Lui, rd, imm20).imm_u(), expected);
        }
    }

    #[test]
    fn opcodes_round_trip_and_nothing_else_is_one() {
        // Each opcode's bits name it back.
        for op in Opcode::ALL {
            assert_eq!(Opcode::from_bits(op.bits()), Some(op));
        }

        // The other 114 seven-bit values name no opcode.
        let unused = (0..128).filter(|&bits| Opcode::from_bits(bits).is_none()).count();
        assert_eq!(unused, 128 - Opcode::ALL.len());
    }

    #[test]
    fn shift_fields_split_the_immediate() {
        // `srai a0, a1, 63`: function 0x10 above a six-bit amount.
        let srai = Instruction::from_bits(0x43f5_d513);
        assert_eq!((srai.funct6(), srai.shamt()), (0x10, 63));
    }

    #[test]
    fn every_operation_has_its_own_mnemonic_and_encoding() {
        // Fixture: every operation of every format, as (mnemonic, bits with zero operands).
        let zero = Reg::ZERO;
        let all: Vec<(&str, u32)> = RegOp::ALL
            .iter()
            .map(|op| (op.mnemonic(), op.encode(zero, zero, zero).bits()))
            .chain(
                ImmOp::ALL
                    .iter()
                    .map(|op| (op.mnemonic(), op.encode(zero, zero, 0).bits())),
            )
            .chain(
                ShiftOp::ALL
                    .iter()
                    .map(|op| (op.mnemonic(), op.encode(zero, zero, 0).bits())),
            )
            .chain(
                LoadOp::ALL
                    .iter()
                    .map(|op| (op.mnemonic(), op.encode(zero, zero, 0).bits())),
            )
            .chain(
                StoreOp::ALL
                    .iter()
                    .map(|op| (op.mnemonic(), op.encode(zero, zero, 0).bits())),
            )
            .chain(
                BranchOp::ALL
                    .iter()
                    .map(|op| (op.mnemonic(), op.encode(zero, zero, 0).bits())),
            )
            .chain(
                ExtOp::ALL
                    .iter()
                    .map(|op| (op.mnemonic(), op.encode(zero, zero, zero).bits())),
            )
            .collect();

        // rv64im has 58 such operations, 28 + 7 + 6 + 7 + 4 + 6, and the extension field adds 4.
        assert_eq!(all.len(), 62);

        // A duplicate would make two names emit, or decode to, the same instruction.
        let mnemonics: HashSet<_> = all.iter().map(|&(name, _)| name).collect();
        let encodings: HashSet<_> = all.iter().map(|&(_, bits)| bits).collect();
        assert_eq!((mnemonics.len(), encodings.len()), (62, 62));
    }
}
