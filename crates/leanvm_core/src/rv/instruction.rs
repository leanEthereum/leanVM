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

use super::register::Reg;

/// A major opcode: the low seven bits of every instruction, naming its format and family.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
#[repr(u32)]
pub enum Opcode {
    /// Loads.
    Load = 0x03,
    /// The custom-0 space, which holds the BLAKE2s compression.
    Custom0 = 0x0b,
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
    /// Every opcode rv64im uses.
    pub const ALL: [Self; 14] = [
        Self::Load,
        Self::Custom0,
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
    /// Returns `None` for an opcode rv64im does not use.
    pub fn from_bits(bits: u32) -> Option<Self> {
        Self::ALL.into_iter().find(|op| op.bits() == bits)
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
    /// Returns `None` for an opcode rv64im does not use.
    pub fn opcode(self) -> Option<Opcode> {
        Opcode::from_bits(self.0 & 0x7f)
    }

    /// Bits 7 to 11: the destination register.
    pub const fn rd(self) -> u32 {
        (self.0 >> 7) & 31
    }

    /// Bits 12 to 14.
    pub const fn funct3(self) -> u32 {
        (self.0 >> 12) & 7
    }

    /// Bits 15 to 19: the first source register.
    pub const fn rs1(self) -> u32 {
        (self.0 >> 15) & 31
    }

    /// Bits 20 to 24: the second source register, or a 32-bit shift's amount.
    pub const fn rs2(self) -> u32 {
        (self.0 >> 20) & 31
    }

    /// Bits 20 to 25: a 64-bit shift's amount.
    pub const fn shamt(self) -> u32 {
        (self.0 >> 20) & 63
    }

    /// Bits 26 to 31: what a 64-bit shift leaves of its function field.
    pub const fn funct6(self) -> u32 {
        self.0 >> 26
    }

    /// Bits 25 to 31.
    pub const fn funct7(self) -> u32 {
        self.0 >> 25
    }

    /// The I-type immediate, sign-extended.
    pub const fn imm_i(self) -> u64 {
        Self::sign_extend(self.0 >> 20, 12)
    }

    /// The S-type immediate, sign-extended.
    pub const fn imm_s(self) -> u64 {
        Self::sign_extend((self.funct7() << 5) | self.rd(), 12)
    }

    /// The B-type offset, sign-extended.
    pub const fn imm_b(self) -> u64 {
        let w = self.0;
        // Bits 12, 11, 10..5 and 4..1, scattered over the word.
        let offset = ((w >> 31) << 12) | (((w >> 7) & 1) << 11) | (((w >> 25) & 0x3f) << 5) | (((w >> 8) & 0xf) << 1);
        Self::sign_extend(offset, 13)
    }

    /// The U-type immediate, already shifted into bits 12 to 31, sign-extended.
    pub const fn imm_u(self) -> u64 {
        Self::sign_extend(self.0 & 0xffff_f000, 32)
    }

    /// The J-type offset, sign-extended.
    pub const fn imm_j(self) -> u64 {
        let w = self.0;
        // Bits 20, 19..12, 11 and 10..1, scattered over the word.
        let offset =
            ((w >> 31) << 20) | (((w >> 12) & 0xff) << 12) | (((w >> 20) & 1) << 11) | (((w >> 21) & 0x3ff) << 1);
        Self::sign_extend(offset, 21)
    }

    /// An R-type instruction.
    pub const fn r(opcode: Opcode, funct3: u32, funct7: u32, rd: Reg, rs1: Reg, rs2: Reg) -> Self {
        Self(
            opcode.bits()
                | (Self::field(rd) << 7)
                | (funct3 << 12)
                | (Self::field(rs1) << 15)
                | (Self::field(rs2) << 20)
                | (funct7 << 25),
        )
    }

    /// An I-type instruction, the immediate's low 12 bits kept.
    pub const fn i(opcode: Opcode, funct3: u32, rd: Reg, rs1: Reg, imm: i32) -> Self {
        Self(
            opcode.bits()
                | (Self::field(rd) << 7)
                | (funct3 << 12)
                | (Self::field(rs1) << 15)
                | ((imm as u32 & 0xfff) << 20),
        )
    }

    /// A store, the offset's low 12 bits kept.
    pub const fn s(funct3: u32, rs1: Reg, rs2: Reg, offset: i32) -> Self {
        let o = offset as u32;
        Self(
            Opcode::Store.bits()
                | ((o & 31) << 7)
                | (funct3 << 12)
                | (Self::field(rs1) << 15)
                | (Self::field(rs2) << 20)
                | (((o >> 5) & 0x7f) << 25),
        )
    }

    /// A conditional branch, the offset's bits 1 to 12 kept.
    pub const fn b(funct3: u32, rs1: Reg, rs2: Reg, offset: i32) -> Self {
        let o = offset as u32;
        Self(
            Opcode::Branch.bits()
                | (((o >> 11) & 1) << 7)
                | (((o >> 1) & 0xf) << 8)
                | (funct3 << 12)
                | (Self::field(rs1) << 15)
                | (Self::field(rs2) << 20)
                | (((o >> 5) & 0x3f) << 25)
                | (((o >> 12) & 1) << 31),
        )
    }

    /// A U-type instruction, `imm20` becoming bits 12 to 31.
    pub const fn u(opcode: Opcode, rd: Reg, imm20: u32) -> Self {
        Self(opcode.bits() | (Self::field(rd) << 7) | ((imm20 & 0xf_ffff) << 12))
    }

    /// A `JAL`, the offset's bits 1 to 20 kept.
    pub const fn j(rd: Reg, offset: i32) -> Self {
        let o = offset as u32;
        Self(
            Opcode::Jal.bits()
                | (Self::field(rd) << 7)
                | (((o >> 12) & 0xff) << 12)
                | (((o >> 11) & 1) << 20)
                | (((o >> 1) & 0x3ff) << 21)
                | (((o >> 20) & 1) << 31),
        )
    }

    /// Sign-extend the low `bits` bits of `x`.
    const fn sign_extend(x: u32, bits: u32) -> u64 {
        // Move the sign bit to bit 63, then shift back arithmetically.
        (((x as u64) << (64 - bits)) as i64 >> (64 - bits)) as u64
    }

    /// A register's number as an encoding field.
    const fn field(r: Reg) -> u32 {
        r.index() as u32
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
        fn r_type_fields_round_trip(funct3 in 0u32..8, funct7 in 0u32..128, rd in any::<Reg>(), rs1 in any::<Reg>(), rs2 in any::<Reg>()) {
            // Every field written comes back from its accessor.
            let ins = Instruction::r(Opcode::Op, funct3, funct7, rd, rs1, rs2);
            prop_assert_eq!(
                (ins.opcode(), ins.funct3(), ins.funct7(), ins.rd(), ins.rs1(), ins.rs2()),
                (Some(Opcode::Op), funct3, funct7, Instruction::field(rd), Instruction::field(rs1), Instruction::field(rs2))
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
            .collect();

        // rv64im has 58 such operations: 28 + 7 + 6 + 7 + 4 + 6.
        assert_eq!(all.len(), 58);

        // A duplicate would make two names emit, or decode to, the same instruction.
        let mnemonics: HashSet<_> = all.iter().map(|&(name, _)| name).collect();
        let encodings: HashSet<_> = all.iter().map(|&(_, bits)| bits).collect();
        assert_eq!((mnemonics.len(), encodings.len()), (58, 58));
    }
}
