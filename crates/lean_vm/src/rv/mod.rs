//! RISC-V (rv64im) as the VM sees it: a public program of DECODED entries.
//!
//! The program is public, so nothing is decoded in a table: [`decode()`] turns each
//! 32-bit word into an [`Entry`] once, and a row's bytecode read returns the entry's
//! fields. An entry names an instruction [`Class`], whose one function
//! ([`semantics`]) a `flags` word specializes, the three register cells the row
//! touches, and the immediate already sign-extended. `LUI`, `AUIPC` and `JAL` are
//! folded to constants here, `pc` being known.
//!
//! Every row reads two registers and writes one. An instruction with fewer reads
//! `x0`, and one with no destination, or with `rd = x0`, writes [`SINK`], a cell
//! nothing reads: that is what hardwires `x0` to zero. The one exception is the
//! BLAKE2s precompile ([`hash`]), whose row writes RAM instead of a register.
//!
//! A trap is the absence of a run: [`machine::Trap`].

pub mod asm;
pub mod circuits;
pub mod decode;
pub mod elf;
pub mod machine;
pub mod semantics;

pub use decode::decode;
pub use elf::{ElfError, Guest};
pub use machine::{Machine, Program, Trap};

/// Where the text sits. Nonzero (a function at 0 would be Rust's null), and a
/// multiple of the largest text, so that instruction `i` is at `TEXT_BASE ^ (i << 2)`.
pub const TEXT_BASE: u64 = 0x1000_0000;
/// `log2` of the most instructions a program holds.
pub const MAX_LOG_TEXT: usize = 26;
/// Where RAM sits: a multiple of the largest RAM, in the text's 2 GiB window (the
/// medany code model). A maximal RAM ends at `0x8000_0000`, and its last 2 KiB are past
/// what `LUI` can form, since `LUI` sign-extends bit 31 on RV64; medlow code stops short
/// of them.
pub const RAM_BASE: u64 = 0x4000_0000;
/// `log2` of the most 64-bit words RAM holds.
pub const MAX_LOG_RAM: usize = 27;
/// Where the advice sits: a second region of memory, read and written like RAM, whose
/// contents before the run are the prover's rather than the statement's. What a
/// guest reads from it, it has to check.
pub const ADVICE_BASE: u64 = 0x2000_0000;
pub const MAX_LOG_ADVICE: usize = 26;

/// RAM's first words are the run's public input, and the program's image follows.
pub const INPUT_WORDS: usize = 4;

/// The register array holds `2^LOG_REGS` cells: `x0..x31`, then [`SINK`].
pub const LOG_REGS: usize = 6;
/// The cell written by an instruction with no destination.
pub const SINK: u8 = 32;

/// The exit system call's number, which `a7` must hold when the run halts.
pub const SYS_EXIT: u64 = 93;
/// `a0..a3`, whose final values are the run's public output.
pub const OUTPUT_REGS: [u8; 4] = [10, 11, 12, 13];
/// `a7`.
pub const SYSCALL_REG: u8 = 17;

/// An instruction class: one table, one circuit.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum Class {
    /// Add, subtract, compare, bitwise logic, branches and jumps.
    Alu,
    Shift,
    Load,
    Store,
    /// The low word of a product.
    Mul,
    /// The high word of a product.
    Mulh,
    Div,
    /// The BLAKE2s compression, a custom instruction ([`hash`]).
    Hash,
    /// No table runs it: reaching one is a trap.
    Illegal,
}

/// Where control goes after an instruction.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Target {
    /// Fall through, or wherever the row computes (`JALR`).
    Next,
    /// A branch or `JAL` target, taken when the class says so.
    Abs(u64),
    /// The halt slot, whose address the program fixes: what `ECALL` jumps to.
    Halt,
}

/// One decoded instruction.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Entry {
    pub class: Class,
    /// Selector bits for the class's function, one of its `LEGAL` words.
    pub flags: u64,
    /// The two cells read, below 32, and the cell written, in `1..=32`.
    pub a1: u8,
    pub a2: u8,
    pub ad: u8,
    pub imm: u64,
    pub target: Target,
    /// `rd` receives `pc + 4` instead of the class's result.
    pub link: bool,
    /// The next `pc` is the class's result.
    pub jalr: bool,
}

impl Entry {
    pub const ILLEGAL: Self = Self {
        class: Class::Illegal,
        flags: 0,
        a1: 0,
        a2: 0,
        ad: SINK,
        imm: 0,
        target: Target::Next,
        link: false,
        jalr: false,
    };

    /// What both verifiers check of every entry: the `x0` and [`SINK`] rules are
    /// semantics, and the proof system is sound for any table, a malformed one included.
    pub fn is_well_formed(&self) -> bool {
        if self.class == Class::Illegal {
            return *self == Self::ILLEGAL;
        }
        let legal = legal_flags(self.class);
        let control = self.class == Class::Alu;
        // A hash row writes no register and reads no immediate: its table holds both at
        // their constants.
        let hash = self.class == Class::Hash;
        self.a1 < 32
            && self.a2 < 32
            && (1..=SINK).contains(&self.ad)
            && legal.contains(&self.flags)
            && (control || (self.target == Target::Next && !self.link && !self.jalr))
            && (!hash || (self.ad == SINK && self.imm == 0))
    }
}

/// The flag words a class defines, which are the only ones its circuit is written for
/// and the only ones an entry may carry ([`Entry::is_well_formed`]). Empty for
/// [`Class::Illegal`], which carries no flags at all.
pub fn legal_flags(class: Class) -> &'static [u64] {
    match class {
        Class::Alu => &alu::LEGAL,
        Class::Shift => &shift::LEGAL,
        Class::Load => &load::LEGAL,
        Class::Store => &store::LEGAL,
        Class::Mul => &mul::LEGAL,
        Class::Mulh => &mulh::LEGAL,
        Class::Div => &div::LEGAL,
        Class::Hash => &hash::LEGAL,
        Class::Illegal => &[],
    }
}

/// [`Class::Alu`]'s flags. `b` is `v2 ^ imm`, one of the two being zero.
pub mod alu {
    /// `v1 - b`, which the comparisons and the branches need, instead of `v1 + b`.
    pub const SUB: u64 = 1 << 0;
    /// Sign-extend the low 32 bits of the sum.
    pub const WORD: u64 = 1 << 1;
    // What `out` is, the sum when none is set.
    pub const SEL_LT: u64 = 1 << 2;
    pub const SEL_LTU: u64 = 1 << 3;
    pub const SEL_AND: u64 = 1 << 4;
    pub const SEL_OR: u64 = 1 << 5;
    pub const SEL_XOR: u64 = 1 << 6;
    /// Clear bit 0 of `out` (`JALR`).
    pub const CLEAR_BIT0: u64 = 1 << 7;
    // When the branch is taken.
    pub const BR_EQ: u64 = 1 << 8;
    pub const BR_NE: u64 = 1 << 9;
    pub const BR_LT: u64 = 1 << 10;
    pub const BR_GE: u64 = 1 << 11;
    pub const BR_LTU: u64 = 1 << 12;
    pub const BR_GEU: u64 = 1 << 13;
    pub const ALWAYS: u64 = 1 << 14;

    pub const LEGAL: [u64; 17] = [
        0,
        SUB,
        WORD,
        SUB | WORD,
        SUB | SEL_LT,
        SUB | SEL_LTU,
        SEL_AND,
        SEL_OR,
        SEL_XOR,
        CLEAR_BIT0,
        SUB | BR_EQ,
        SUB | BR_NE,
        SUB | BR_LT,
        SUB | BR_GE,
        SUB | BR_LTU,
        SUB | BR_GEU,
        ALWAYS,
    ];
}

/// [`Class::Shift`]'s flags. The amount is the low 6 bits of `v2 ^ imm`, 5 for a word shift.
pub mod shift {
    pub const RIGHT: u64 = 1 << 0;
    /// An arithmetic right shift.
    pub const ARITH: u64 = 1 << 1;
    /// Shift the low 32 bits, and sign-extend the low 32 bits of the result.
    pub const WORD: u64 = 1 << 2;

    pub const LEGAL: [u64; 6] = [0, RIGHT, RIGHT | ARITH, WORD, WORD | RIGHT, WORD | RIGHT | ARITH];
}

/// [`Class::Load`]'s flags: `log2` of the width in bytes, then the extension.
pub mod load {
    pub const LOG_WIDTH: u64 = 0b11;
    pub const SIGNED: u64 = 1 << 2;

    pub const LEGAL: [u64; 7] = [SIGNED, SIGNED | 1, SIGNED | 2, 3, 0, 1, 2];
}

/// [`Class::Store`]'s flags: `log2` of the width in bytes.
pub mod store {
    pub const LOG_WIDTH: u64 = 0b11;

    pub const LEGAL: [u64; 4] = [0, 1, 2, 3];
}

/// [`Class::Mul`]'s flags.
pub mod mul {
    /// Sign-extend the low 32 bits of the product.
    pub const WORD: u64 = 1 << 0;

    pub const LEGAL: [u64; 2] = [0, WORD];
}

/// [`Class::Mulh`]'s flags: which operands are signed.
pub mod mulh {
    pub const SIGNED_1: u64 = 1 << 0;
    pub const SIGNED_2: u64 = 1 << 1;

    pub const LEGAL: [u64; 3] = [SIGNED_1 | SIGNED_2, SIGNED_1, 0];
}

/// [`Class::Hash`]: `blake2s rs1, rs2`, the BLAKE2s compression of the 128-byte block
/// at `rs1`, with `rs2` the byte counter. The block is the chaining value (32 bytes),
/// where the result goes (32 bytes), then the message (64 bytes). Word `k` of the
/// block is the cell at `rs1 ^ 8k`, which is `rs1 + 8k` when `rs1` is aligned to the
/// block, as the guest library makes sure; an unaligned `rs1` permutes the words,
/// which is deterministic and provable, and a guest bug. The flags are the
/// finalization word `f0`: all ones on the last block.
pub mod hash {
    /// The custom-0 opcode, R-type: `funct3` is 1 for the final block, `funct7` and `rd` are zero.
    pub const OPCODE: u32 = 0x0b;
    /// Byte offsets in the block.
    pub const H: u64 = 0;
    pub const OUT: u64 = 32;
    pub const M: u64 = 64;
    /// The block's words, and how many the row rewrites.
    pub const WORDS: usize = 16;
    pub const BLOCK_BYTES: u64 = 8 * WORDS as u64;

    pub const FINAL: u64 = u32::MAX as u64;
    pub const LEGAL: [u64; 2] = [0, FINAL];
}

/// [`Class::Div`]'s flags.
pub mod div {
    pub const SIGNED: u64 = 1 << 0;
    /// The remainder instead of the quotient.
    pub const REM: u64 = 1 << 1;
    /// Operate on the low 32 bits, extended as `SIGNED` says, and sign-extend the
    /// low 32 bits of the result.
    pub const WORD: u64 = 1 << 2;

    pub const LEGAL: [u64; 8] = [0, 1, 2, 3, 4, 5, 6, 7];
}
