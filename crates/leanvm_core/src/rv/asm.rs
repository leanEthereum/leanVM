//! A small assembler for hand-written programs and tests.
//!
//! Real guests come from an ELF file.

use std::collections::HashMap;

pub use super::instruction::BranchOp::{self, *};
pub use super::instruction::ExtOp::{self, *};
pub use super::instruction::ImmOp::{self, *};
pub use super::instruction::LoadOp::{self, *};
pub use super::instruction::RegOp::{self, *};
pub use super::instruction::ShiftOp::{self, *};
pub use super::instruction::StoreOp::{self, *};
pub use super::instruction::{Instruction, Op, Opcode};
pub use super::register::Reg;

use super::register::{ExtReg, Syscall};

/// An instruction whose offset waits for its label.
#[derive(Clone, Copy, Debug)]
enum Fixup {
    /// A conditional branch.
    Branch(BranchOp, Reg, Reg),
    /// A `JAL`.
    Jal(Reg),
}

/// A program under assembly.
///
/// Each method appends one instruction, or a few for `li` and `exit`.
///
/// Branches and jumps name labels, resolved when the program is finished.
#[derive(Debug, Default)]
pub struct Asm {
    /// The instructions so far, branch and jump words zero until resolved.
    words: Vec<u32>,
    /// Each label's instruction index.
    labels: HashMap<&'static str, usize>,
    /// Each unresolved instruction's index, label and shape.
    fixups: Vec<(usize, &'static str, Fixup)>,
}

impl Asm {
    /// An empty program.
    pub fn new() -> Self {
        Self::default()
    }

    /// Append a raw word, which need not be a legal instruction.
    pub fn word(&mut self, word: u32) -> &mut Self {
        self.words.push(word);
        self
    }

    /// Name the next instruction's address.
    ///
    /// # Panics
    ///
    /// Panics if the label is already defined.
    pub fn label(&mut self, name: &'static str) -> &mut Self {
        let fresh = self.labels.insert(name, self.words.len()).is_none();
        assert!(fresh, "label {name} defined twice");
        self
    }

    /// `op rd, rs1, rs2`.
    pub fn r(&mut self, op: RegOp, rd: Reg, rs1: Reg, rs2: Reg) -> &mut Self {
        self.emit(Op::Reg { op, rd, rs1, rs2 })
    }

    /// `op rd, rs1, imm`.
    ///
    /// # Panics
    ///
    /// Panics if the immediate does not fit 12 signed bits.
    pub fn i(&mut self, op: ImmOp, rd: Reg, rs1: Reg, imm: i32) -> &mut Self {
        assert!((-2048..2048).contains(&imm), "{} immediate {imm}", op.mnemonic());
        self.emit(Op::Imm { op, rd, rs1, imm })
    }

    /// `op rd, rs1, amount`.
    ///
    /// # Panics
    ///
    /// Panics if the amount does not fit the operation: 6 bits, or 5 on the low 32 bits.
    pub fn shift(&mut self, op: ShiftOp, rd: Reg, rs1: Reg, amount: u32) -> &mut Self {
        assert!(amount < 1 << op.amount_bits(), "{} by {amount}", op.mnemonic());
        self.emit(Op::Shift { op, rd, rs1, amount })
    }

    /// `op rd, offset(rs1)`: `rd = mem[rs1 + offset]`.
    ///
    /// # Panics
    ///
    /// Panics if the offset does not fit 12 signed bits.
    pub fn load(&mut self, op: LoadOp, rd: Reg, offset: i32, rs1: Reg) -> &mut Self {
        assert!((-2048..2048).contains(&offset), "{} offset {offset}", op.mnemonic());
        self.emit(Op::Load { op, rd, rs1, offset })
    }

    /// `op rs2, offset(rs1)`: `mem[rs1 + offset] = rs2`.
    ///
    /// # Panics
    ///
    /// Panics if the offset does not fit 12 signed bits.
    pub fn store(&mut self, op: StoreOp, rs2: Reg, offset: i32, rs1: Reg) -> &mut Self {
        assert!((-2048..2048).contains(&offset), "{} offset {offset}", op.mnemonic());
        self.emit(Op::Store { op, rs1, rs2, offset })
    }

    /// `op rs1, rs2, label`.
    pub fn branch(&mut self, op: BranchOp, rs1: Reg, rs2: Reg, label: &'static str) -> &mut Self {
        self.fixups.push((self.words.len(), label, Fixup::Branch(op, rs1, rs2)));
        self.word(0)
    }

    /// `jal rd, label`: jump, writing the return address to `rd`.
    pub fn jal(&mut self, rd: Reg, label: &'static str) -> &mut Self {
        self.fixups.push((self.words.len(), label, Fixup::Jal(rd)));
        self.word(0)
    }

    /// `jalr rd, offset(rs1)`: jump to `rs1 + offset`, writing the return address to `rd`.
    pub fn jalr(&mut self, rd: Reg, rs1: Reg, offset: i32) -> &mut Self {
        self.emit(Op::Jalr { rd, rs1, offset })
    }

    /// `lui rd, imm20`: `rd = imm20 << 12`, sign-extended.
    pub fn lui(&mut self, rd: Reg, imm20: u32) -> &mut Self {
        self.emit(Op::Lui { rd, imm20 })
    }

    /// `auipc rd, imm20`: `rd = pc + (imm20 << 12)`, sign-extended.
    pub fn auipc(&mut self, rd: Reg, imm20: u32) -> &mut Self {
        self.emit(Op::Auipc { rd, imm20 })
    }

    /// `rd = value`, any 64-bit constant.
    ///
    /// The sequence is the shortest of three:
    ///
    /// - a 12-bit value is one `addi`;
    /// - a 32-bit value is a `lui`, then an `addiw` if its low 12 bits are not zero;
    /// - a wider value loads its high part, shifts it up, then adds its low 12 bits if not zero.
    pub fn li(&mut self, rd: Reg, value: u64) -> &mut Self {
        // Split off the low 12 bits, sign-extended, so the high part absorbs their sign.
        let v = value as i64;
        let lo = (v << 52) >> 52;

        // A value that fits 32 signed bits: lui and addiw, or a lone addi.
        if v == v as i32 as i64 {
            let hi = (v.wrapping_sub(lo) >> 12) as u32 & 0xf_ffff;
            if hi == 0 {
                return self.i(Addi, rd, Reg::ZERO, lo as i32);
            }
            self.lui(rd, hi);
            return if lo == 0 {
                self
            } else {
                self.i(Addiw, rd, rd, lo as i32)
            };
        }

        // A wider value: the high part with its trailing zeros dropped, shifted back up.
        let hi = v.wrapping_sub(lo) >> 12;
        let zeros = hi.trailing_zeros();
        self.li(rd, (hi >> zeros) as u64).shift(Slli, rd, rd, 12 + zeros);
        if lo == 0 { self } else { self.i(Addi, rd, rd, lo as i32) }
    }

    /// `blake2s rs1, rs2`: compress the block at `rs1` with the counter `rs2`.
    ///
    /// `last` marks the final block.
    pub fn blake2s(&mut self, rs1: Reg, rs2: Reg, last: bool) -> &mut Self {
        self.emit(Op::Blake2s { rs1, rs2, last })
    }

    /// `op fd, fs1, fs2`: an extension-field multiplication on extension registers, by number.
    ///
    /// A base-field form's `fs2` is an integer register's number.
    ///
    /// # Panics
    ///
    /// Panics if a number names no extension register.
    pub fn ext(&mut self, op: ExtOp, rd: u8, rs1: u8, rs2: u8) -> &mut Self {
        let reg = |i| ExtReg::new(i).expect("an extension register");
        let (rd, rs1, rs2) = (reg(rd), reg(rs1), reg(rs2));
        self.emit(Op::Ext { op, rd, rs1, rs2 })
    }

    /// `ecall`.
    pub fn ecall(&mut self) -> &mut Self {
        self.emit(Op::Ecall)
    }

    /// `exit(a0, a1, a2, a3)`: the system call number in `a7`, then `ecall`.
    pub fn exit(&mut self) -> &mut Self {
        self.i(Addi, Reg::A7, Reg::ZERO, Syscall::Exit.number() as i32).ecall()
    }

    /// The program's words, every label resolved.
    ///
    /// # Panics
    ///
    /// Panics if a label is undefined, or a branch's label out of its reach.
    pub fn finish(&mut self) -> Vec<u32> {
        for (at, label, fixup) in self.fixups.drain(..) {
            // The byte offset from the instruction to its label.
            let to = *self
                .labels
                .get(label)
                .unwrap_or_else(|| panic!("undefined label {label}"));
            let offset = (to as i32 - at as i32) * 4;
            let op = match fixup {
                Fixup::Branch(op, rs1, rs2) => {
                    assert!((-4096..4096).contains(&offset), "branch to {label} out of range");
                    Op::Branch { op, rs1, rs2, offset }
                }
                Fixup::Jal(rd) => Op::Jal { rd, offset },
            };
            self.words[at] = op.encode().bits();
        }
        std::mem::take(&mut self.words)
    }

    /// Append one instruction.
    fn emit(&mut self, op: Op) -> &mut Self {
        self.word(op.encode().bits())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::rv::Region;
    use crate::rv::entry::{Class, Entry, Target};

    #[test]
    fn labels_resolve_backward_and_forward() {
        // Fixture: a branch back to the top, and a jump forward to the end.
        //
        //     0  top:  bne a0, zero, top     offset  0
        //     1        jal ra, end           offset +8
        //     2        addi a0, a0, 1
        //     3  end:
        let text = Asm::new()
            .label("top")
            .branch(Bne, Reg::A0, Reg::ZERO, "top")
            .jal(Reg::RA, "end")
            .i(Addi, Reg::A0, Reg::A0, 1)
            .label("end")
            .finish();

        // The decoder folds each offset into its absolute target.
        let entry = |i: usize| Entry::decode(text[i], Region::TEXT.base() + 4 * i as u64);
        assert_eq!(entry(0).target, Target::Abs(Region::TEXT.base()));
        assert_eq!(entry(1).target, Target::Abs(Region::TEXT.base() + 12));
        assert_eq!(entry(2).class, Class::Alu);
    }

    #[test]
    #[should_panic(expected = "undefined label nowhere")]
    fn an_undefined_label_panics() {
        Asm::new().jal(Reg::ZERO, "nowhere").finish();
    }

    #[test]
    #[should_panic(expected = "label twice defined twice")]
    fn a_label_defined_twice_panics() {
        Asm::new().label("twice").label("twice");
    }

    #[test]
    #[should_panic(expected = "slliw by 32")]
    fn a_word_shift_by_32_panics() {
        Asm::new().shift(Slliw, Reg::A0, Reg::A0, 32);
    }

    #[test]
    fn li_uses_the_shortest_sequence() {
        // Fixture: a 12-bit, a 32-bit and a 64-bit constant.
        //
        //     -5               addi
        //     0x1234_5000      lui
        //     0x1234_5678      lui, addiw
        //     1 << 40          addi, slli
        for (value, len) in [(-5i64 as u64, 1), (0x1234_5000, 1), (0x1234_5678, 2), (1 << 40, 2)] {
            assert_eq!(Asm::new().li(Reg::A0, value).finish().len(), len, "{value:#x}");
        }
    }
}
