//! A small assembler: instruction encoders, labels for branches and jumps, and `li`.
//! For hand-written programs and tests; real guests come from an ELF.

use std::collections::HashMap;

// Registers, by their ABI names.
pub const ZERO: u32 = 0;
pub const RA: u32 = 1;
pub const SP: u32 = 2;
pub const T0: u32 = 5;
pub const T1: u32 = 6;
pub const T2: u32 = 7;
pub const S0: u32 = 8;
pub const S1: u32 = 9;
pub const A0: u32 = 10;
pub const A1: u32 = 11;
pub const A2: u32 = 12;
pub const A3: u32 = 13;
pub const A4: u32 = 14;
pub const A5: u32 = 15;
pub const A6: u32 = 16;
pub const A7: u32 = 17;

pub fn r_type(opcode: u32, f3: u32, f7: u32, rd: u32, rs1: u32, rs2: u32) -> u32 {
    opcode | (rd << 7) | (f3 << 12) | (rs1 << 15) | (rs2 << 20) | (f7 << 25)
}
pub fn i_type(opcode: u32, f3: u32, rd: u32, rs1: u32, imm: i32) -> u32 {
    opcode | (rd << 7) | (f3 << 12) | (rs1 << 15) | ((imm as u32 & 0xfff) << 20)
}
pub fn s_type(opcode: u32, f3: u32, rs1: u32, rs2: u32, imm: i32) -> u32 {
    let imm = imm as u32;
    opcode | ((imm & 31) << 7) | (f3 << 12) | (rs1 << 15) | (rs2 << 20) | ((imm >> 5 & 0x7f) << 25)
}
pub fn b_type(f3: u32, rs1: u32, rs2: u32, offset: i32) -> u32 {
    let o = offset as u32;
    0x63 | ((o >> 11 & 1) << 7)
        | ((o >> 1 & 0xf) << 8)
        | (f3 << 12)
        | (rs1 << 15)
        | (rs2 << 20)
        | ((o >> 5 & 0x3f) << 25)
        | ((o >> 12 & 1) << 31)
}
pub fn u_type(opcode: u32, rd: u32, imm20: u32) -> u32 {
    opcode | (rd << 7) | ((imm20 & 0xf_ffff) << 12)
}
pub fn j_type(rd: u32, offset: i32) -> u32 {
    let o = offset as u32;
    0x6f | (rd << 7)
        | ((o >> 12 & 0xff) << 12)
        | ((o >> 11 & 1) << 20)
        | ((o >> 1 & 0x3ff) << 21)
        | ((o >> 20 & 1) << 31)
}

/// `(mnemonic, opcode, f3, f7)` of every register-register instruction.
pub const R_OPS: [(&str, u32, u32, u32); 28] = [
    ("add", 0x33, 0, 0),
    ("sub", 0x33, 0, 0x20),
    ("sll", 0x33, 1, 0),
    ("slt", 0x33, 2, 0),
    ("sltu", 0x33, 3, 0),
    ("xor", 0x33, 4, 0),
    ("srl", 0x33, 5, 0),
    ("sra", 0x33, 5, 0x20),
    ("or", 0x33, 6, 0),
    ("and", 0x33, 7, 0),
    ("mul", 0x33, 0, 1),
    ("mulh", 0x33, 1, 1),
    ("mulhsu", 0x33, 2, 1),
    ("mulhu", 0x33, 3, 1),
    ("div", 0x33, 4, 1),
    ("divu", 0x33, 5, 1),
    ("rem", 0x33, 6, 1),
    ("remu", 0x33, 7, 1),
    ("addw", 0x3b, 0, 0),
    ("subw", 0x3b, 0, 0x20),
    ("sllw", 0x3b, 1, 0),
    ("srlw", 0x3b, 5, 0),
    ("sraw", 0x3b, 5, 0x20),
    ("mulw", 0x3b, 0, 1),
    ("divw", 0x3b, 4, 1),
    ("divuw", 0x3b, 5, 1),
    ("remw", 0x3b, 6, 1),
    ("remuw", 0x3b, 7, 1),
];
/// `(mnemonic, opcode, f3)` of the register-immediate instructions with a 12-bit immediate.
pub const I_OPS: [(&str, u32, u32); 7] = [
    ("addi", 0x13, 0),
    ("slti", 0x13, 2),
    ("sltiu", 0x13, 3),
    ("xori", 0x13, 4),
    ("ori", 0x13, 6),
    ("andi", 0x13, 7),
    ("addiw", 0x1b, 0),
];
/// `(mnemonic, opcode, f3, top bits, amount bits)` of the shifts by an immediate.
pub const SHIFT_OPS: [(&str, u32, u32, u32, u32); 6] = [
    ("slli", 0x13, 1, 0, 6),
    ("srli", 0x13, 5, 0, 6),
    ("srai", 0x13, 5, 0x400, 6),
    ("slliw", 0x1b, 1, 0, 5),
    ("srliw", 0x1b, 5, 0, 5),
    ("sraiw", 0x1b, 5, 0x400, 5),
];
/// `(mnemonic, f3)`.
pub const LOAD_OPS: [(&str, u32); 7] = [
    ("lb", 0),
    ("lh", 1),
    ("lw", 2),
    ("ld", 3),
    ("lbu", 4),
    ("lhu", 5),
    ("lwu", 6),
];
pub const STORE_OPS: [(&str, u32); 4] = [("sb", 0), ("sh", 1), ("sw", 2), ("sd", 3)];
pub const BRANCH_OPS: [(&str, u32); 6] = [("beq", 0), ("bne", 1), ("blt", 4), ("bge", 5), ("bltu", 6), ("bgeu", 7)];

pub const ECALL: u32 = 0x73;

fn lookup<T: Copy>(table: &[T], name: impl Fn(&T) -> &str, mnemonic: &str) -> T {
    *table
        .iter()
        .find(|t| name(t) == mnemonic)
        .unwrap_or_else(|| panic!("no instruction {mnemonic}"))
}

enum Fixup {
    Branch(u32, u32, u32),
    Jal(u32),
}

/// A program under assembly.
#[derive(Default)]
pub struct Asm {
    words: Vec<u32>,
    labels: HashMap<&'static str, usize>,
    fixups: Vec<(usize, &'static str, Fixup)>,
}

impl Asm {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn word(&mut self, word: u32) -> &mut Self {
        self.words.push(word);
        self
    }

    pub fn label(&mut self, name: &'static str) -> &mut Self {
        assert!(
            self.labels.insert(name, self.words.len()).is_none(),
            "label {name} defined twice"
        );
        self
    }

    /// A register-register instruction of [`R_OPS`].
    pub fn r(&mut self, mnemonic: &str, rd: u32, rs1: u32, rs2: u32) -> &mut Self {
        let (_, opcode, f3, f7) = lookup(&R_OPS, |t| t.0, mnemonic);
        self.word(r_type(opcode, f3, f7, rd, rs1, rs2))
    }

    /// A register-immediate instruction of [`I_OPS`] or [`SHIFT_OPS`].
    pub fn i(&mut self, mnemonic: &str, rd: u32, rs1: u32, imm: i32) -> &mut Self {
        if let Some(&(_, opcode, f3, top, bits)) = SHIFT_OPS.iter().find(|t| t.0 == mnemonic) {
            assert!((0..1 << bits).contains(&imm), "{mnemonic} by {imm}");
            return self.word(i_type(opcode, f3, rd, rs1, top as i32 | imm));
        }
        let (_, opcode, f3) = lookup(&I_OPS, |t| t.0, mnemonic);
        assert!((-2048..2048).contains(&imm), "{mnemonic} immediate {imm}");
        self.word(i_type(opcode, f3, rd, rs1, imm))
    }

    /// `rd <- mem[rs1 + offset]`, an instruction of [`LOAD_OPS`].
    pub fn load(&mut self, mnemonic: &str, rd: u32, offset: i32, rs1: u32) -> &mut Self {
        self.word(i_type(0x03, lookup(&LOAD_OPS, |t| t.0, mnemonic).1, rd, rs1, offset))
    }

    /// `mem[rs1 + offset] <- rs2`, an instruction of [`STORE_OPS`].
    pub fn store(&mut self, mnemonic: &str, rs2: u32, offset: i32, rs1: u32) -> &mut Self {
        self.word(s_type(0x23, lookup(&STORE_OPS, |t| t.0, mnemonic).1, rs1, rs2, offset))
    }

    /// A branch of [`BRANCH_OPS`] to `label`.
    pub fn branch(&mut self, mnemonic: &str, rs1: u32, rs2: u32, label: &'static str) -> &mut Self {
        let f3 = lookup(&BRANCH_OPS, |t| t.0, mnemonic).1;
        self.fixups.push((self.words.len(), label, Fixup::Branch(f3, rs1, rs2)));
        self.word(0)
    }

    pub fn jal(&mut self, rd: u32, label: &'static str) -> &mut Self {
        self.fixups.push((self.words.len(), label, Fixup::Jal(rd)));
        self.word(0)
    }

    pub fn jalr(&mut self, rd: u32, rs1: u32, offset: i32) -> &mut Self {
        self.word(i_type(0x67, 0, rd, rs1, offset))
    }

    pub fn lui(&mut self, rd: u32, imm20: u32) -> &mut Self {
        self.word(u_type(0x37, rd, imm20))
    }

    pub fn auipc(&mut self, rd: u32, imm20: u32) -> &mut Self {
        self.word(u_type(0x17, rd, imm20))
    }

    /// `rd <- value`, any 64-bit constant.
    pub fn li(&mut self, rd: u32, value: u64) -> &mut Self {
        let v = value as i64;
        let lo = (v << 52) >> 52;
        if v == v as i32 as i64 {
            let hi = ((v.wrapping_sub(lo)) >> 12) as u32 & 0xf_ffff;
            if hi == 0 {
                return self.i("addi", rd, ZERO, lo as i32);
            }
            self.lui(rd, hi);
            return if lo == 0 {
                self
            } else {
                self.i("addiw", rd, rd, lo as i32)
            };
        }
        let hi = v.wrapping_sub(lo) >> 12;
        let zeros = hi.trailing_zeros();
        self.li(rd, (hi >> zeros) as u64).i("slli", rd, rd, (12 + zeros) as i32);
        if lo == 0 {
            self
        } else {
            self.i("addi", rd, rd, lo as i32)
        }
    }

    /// `blake2s rs1, rs2` ([`super::hash`]): compress the block at `rs1` with the
    /// counter `rs2`, `last` marking the final block.
    pub fn blake2s(&mut self, rs1: u32, rs2: u32, last: bool) -> &mut Self {
        self.word(r_type(super::hash::OPCODE, last as u32, 0, 0, rs1, rs2))
    }

    /// `exit(a0)`.
    pub fn exit(&mut self) -> &mut Self {
        self.i("addi", A7, ZERO, super::SYS_EXIT as i32).word(ECALL)
    }

    /// The words, every label resolved.
    pub fn finish(&mut self) -> Vec<u32> {
        for (at, label, fixup) in self.fixups.drain(..) {
            let to = *self
                .labels
                .get(label)
                .unwrap_or_else(|| panic!("undefined label {label}"));
            let offset = (to as i32 - at as i32) * 4;
            self.words[at] = match fixup {
                Fixup::Branch(f3, rs1, rs2) => {
                    assert!((-4096..4096).contains(&offset), "branch to {label} out of range");
                    b_type(f3, rs1, rs2, offset)
                }
                Fixup::Jal(rd) => j_type(rd, offset),
            };
        }
        std::mem::take(&mut self.words)
    }
}
