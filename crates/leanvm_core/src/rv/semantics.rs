//! What each instruction class computes.
//!
//! A class is a type whose value is one instance: the flag word and the operands the class reads.
//!
//! The flag word stays a `u64`.
//!
//! It is the bytecode word the proof commits, and its bits are the circuit's selectors.
//!
//! Every class implements one trait, so code over all classes is written once.
//!
//! These functions are the reference.
//!
//! The interpreter runs them, and each class's circuit is tested against them.
//!
//! Each one is defined on its class's legal flag words only.

use super::circuits::ClassCircuit;
use super::entry::{Class, Entry};

/// An instruction class: its flag words, its function, and the circuit that proves it.
///
/// The circuit's ports are the instance's input words, then the result's output words.
///
/// The reference function and the circuit agree on every instance with a legal flag word.
pub trait InstructionClass: ClassCircuit {
    /// The class an entry of this kind names.
    const CLASS: Class;

    /// The flag words the class defines.
    const LEGAL: &'static [u64];

    /// What the class computes.
    type Output;

    /// What the class computes on this instance.
    fn eval(&self) -> Self::Output;

    /// The circuit's input words for this instance, in port order.
    fn input_words(&self) -> Vec<u64>;

    /// The circuit's output words for a result, in port order.
    fn output_words(output: &Self::Output) -> Vec<u64>;
}

/// One ALU instance: add, subtract, compare, bitwise logic, branches and jumps.
///
/// The second operand `b` is `v2 ^ imm`.
///
/// One of the two is always zero.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Alu {
    /// What the ALU computes: one of its legal words.
    pub flags: u64,
    /// The first register's value.
    pub v1: u64,
    /// The second register's value.
    pub v2: u64,
    /// The immediate.
    pub imm: u64,
}

impl Alu {
    /// Compute `v1 - b` instead of `v1 + b`.
    ///
    /// The comparisons and the branches need the difference.
    pub const SUB: u64 = 1 << 0;
    /// Sign-extend the low 32 bits of the sum.
    pub const WORD: u64 = 1 << 1;
    /// Output `v1 < b`, signed.
    pub const SEL_LT: u64 = 1 << 2;
    /// Output `v1 < b`, unsigned.
    pub const SEL_LTU: u64 = 1 << 3;
    /// Output `v1 & b`.
    pub const SEL_AND: u64 = 1 << 4;
    /// Output `v1 | b`.
    pub const SEL_OR: u64 = 1 << 5;
    /// Output `v1 ^ b`.
    pub const SEL_XOR: u64 = 1 << 6;
    /// Clear bit 0 of the output, as `JALR` does to its target.
    pub const CLEAR_BIT0: u64 = 1 << 7;
    /// Branch when `v1 == b`.
    pub const BR_EQ: u64 = 1 << 8;
    /// Branch when `v1 != b`.
    pub const BR_NE: u64 = 1 << 9;
    /// Branch when `v1 < b`, signed.
    pub const BR_LT: u64 = 1 << 10;
    /// Branch when `v1 >= b`, signed.
    pub const BR_GE: u64 = 1 << 11;
    /// Branch when `v1 < b`, unsigned.
    pub const BR_LTU: u64 = 1 << 12;
    /// Branch when `v1 >= b`, unsigned.
    pub const BR_GEU: u64 = 1 << 13;
    /// Always take the jump.
    pub const ALWAYS: u64 = 1 << 14;

    /// Every branch condition.
    pub const BRANCHES: u64 = Self::BR_EQ | Self::BR_NE | Self::BR_LT | Self::BR_GE | Self::BR_LTU | Self::BR_GEU;

    /// The flag word of a branch with function `funct3`.
    ///
    /// Returns `None` for functions 2 and 3, which are reserved.
    pub fn branch_flags(funct3: u32) -> Option<u64> {
        let condition = match funct3 {
            0 => Self::BR_EQ,
            1 => Self::BR_NE,
            4 => Self::BR_LT,
            5 => Self::BR_GE,
            6 => Self::BR_LTU,
            7 => Self::BR_GEU,
            _ => return None,
        };
        Some(Self::SUB | condition)
    }
}

impl InstructionClass for Alu {
    const CLASS: Class = Class::Alu;

    /// At most one output selector and at most one branch condition is set.
    const LEGAL: &'static [u64] = &[
        0,
        Self::SUB,
        Self::WORD,
        Self::SUB | Self::WORD,
        Self::SUB | Self::SEL_LT,
        Self::SUB | Self::SEL_LTU,
        Self::SEL_AND,
        Self::SEL_OR,
        Self::SEL_XOR,
        Self::CLEAR_BIT0,
        Self::SUB | Self::BR_EQ,
        Self::SUB | Self::BR_NE,
        Self::SUB | Self::BR_LT,
        Self::SUB | Self::BR_GE,
        Self::SUB | Self::BR_LTU,
        Self::SUB | Self::BR_GEU,
        Self::ALWAYS,
    ];

    /// The output, and whether the jump is taken.
    type Output = (u64, bool);

    fn eval(&self) -> (u64, bool) {
        let on = |flag: u64| self.flags & flag != 0;
        let (v1, b) = (self.v1, self.v2 ^ self.imm);

        // One adder serves the sum and the difference.
        let sum = if on(Self::SUB) {
            v1.wrapping_sub(b)
        } else {
            v1.wrapping_add(b)
        };

        // The comparisons every selector and branch picks from.
        let (lt, ltu, eq) = ((v1 as i64) < (b as i64), v1 < b, v1 == b);

        // The output: one selector, or the sum when none is set.
        let mut out = if on(Self::SEL_LT) {
            lt as u64
        } else if on(Self::SEL_LTU) {
            ltu as u64
        } else if on(Self::SEL_AND) {
            v1 & b
        } else if on(Self::SEL_OR) {
            v1 | b
        } else if on(Self::SEL_XOR) {
            v1 ^ b
        } else if on(Self::WORD) {
            sext32(sum)
        } else {
            sum
        };

        // A JALR target drops its low bit.
        if on(Self::CLEAR_BIT0) {
            out &= !1;
        }

        // The jump: unconditional, or the one branch condition set.
        let taken = on(Self::ALWAYS)
            || (on(Self::BR_EQ) && eq)
            || (on(Self::BR_NE) && !eq)
            || (on(Self::BR_LT) && lt)
            || (on(Self::BR_GE) && !lt)
            || (on(Self::BR_LTU) && ltu)
            || (on(Self::BR_GEU) && !ltu);
        (out, taken)
    }

    fn input_words(&self) -> Vec<u64> {
        vec![self.v1, self.v2, self.imm, self.flags]
    }

    fn output_words(&(out, taken): &(u64, bool)) -> Vec<u64> {
        vec![out, taken as u64]
    }
}

/// One shifter instance.
///
/// The amount is the low 6 bits of `v2 ^ imm`, or 5 bits for a word shift.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Shift {
    /// What the shifter computes: one of its legal words.
    pub flags: u64,
    /// The value to shift.
    pub v1: u64,
    /// The second register's value.
    pub v2: u64,
    /// The immediate.
    pub imm: u64,
}

impl Shift {
    /// Shift right instead of left.
    pub const RIGHT: u64 = 1 << 0;
    /// Fill a right shift with the sign bit.
    pub const ARITH: u64 = 1 << 1;
    /// Shift the low 32 bits, then sign-extend the low 32 bits of the result.
    pub const WORD: u64 = 1 << 2;
}

impl InstructionClass for Shift {
    const CLASS: Class = Class::Shift;

    /// An arithmetic shift is always a right shift.
    const LEGAL: &'static [u64] = &[
        0,
        Self::RIGHT,
        Self::RIGHT | Self::ARITH,
        Self::WORD,
        Self::WORD | Self::RIGHT,
        Self::WORD | Self::RIGHT | Self::ARITH,
    ];

    /// The shifted value.
    type Output = u64;

    fn eval(&self) -> u64 {
        let on = |flag: u64| self.flags & flag != 0;
        let (right, arith, word) = (on(Self::RIGHT), on(Self::ARITH), on(Self::WORD));
        let amount = (self.v2 ^ self.imm) & if word { 31 } else { 63 };

        // A word shift starts from the low 32 bits, extended as the shift fills.
        let x = match (word, arith) {
            (false, _) => self.v1,
            (true, true) => sext32(self.v1),
            (true, false) => self.v1 as u32 as u64,
        };

        // Shift, then sign-extend a word result.
        let out = match (right, arith) {
            (false, _) => x << amount,
            (true, false) => x >> amount,
            (true, true) => ((x as i64) >> amount) as u64,
        };
        if word { sext32(out) } else { out }
    }

    fn input_words(&self) -> Vec<u64> {
        vec![self.v1, self.v2, self.imm, self.flags]
    }

    fn output_words(&out: &u64) -> Vec<u64> {
        vec![out]
    }
}

/// One load instance: the width and extension in its flags, the address `v1 + imm`, the cell read there.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Load {
    /// The width, then the extension: one of the legal words.
    pub flags: u64,
    /// The base register's value.
    pub v1: u64,
    /// The offset.
    pub imm: u64,
    /// The 64-bit cell holding the address.
    pub cell: u64,
}

impl Load {
    /// The bits holding the base-two logarithm of the width in bytes.
    pub const LOG_WIDTH: u64 = 0b11;
    /// Sign-extend the value instead of zero-extending it.
    pub const SIGNED: u64 = 1 << 2;

    /// The flag word of a load with function `funct3`.
    ///
    /// - 0 to 2 are `lb`, `lh` and `lw`: signed, of width 2^funct3.
    /// - 3 is `ld`, which has no extension.
    /// - 4 to 6 are `lbu`, `lhu` and `lwu`: unsigned, of width 2^(funct3 - 4).
    ///
    /// Returns `None` for function 7, which is reserved.
    pub fn flags_of(funct3: u32) -> Option<u64> {
        match funct3 {
            0..=2 => Some(Self::SIGNED | funct3 as u64),
            3 => Some(3),
            4..=6 => Some((funct3 - 4) as u64),
            _ => None,
        }
    }
}

impl InstructionClass for Load {
    const CLASS: Class = Class::Load;

    /// A double word has no extension.
    const LEGAL: &'static [u64] = &[Self::SIGNED, Self::SIGNED | 1, Self::SIGNED | 2, 3, 0, 1, 2];

    /// The bus address, and the value read.
    type Output = (u64, u64);

    fn eval(&self) -> (u64, u64) {
        let address = WordAccess::address(self.v1, self.imm);
        let log_width = self.flags & Self::LOG_WIDTH;
        let bits = 8 << log_width;

        // Bring the addressed byte down to bit 0.
        let x = self.cell >> (8 * (address & 7));

        // Keep the width, extended as the flags say.
        let value = if bits == 64 {
            x
        } else if self.flags & Self::SIGNED != 0 {
            (((x << (64 - bits)) as i64) >> (64 - bits)) as u64
        } else {
            x & ((1 << bits) - 1)
        };
        (WordAccess::bus_address(address, log_width), value)
    }

    fn input_words(&self) -> Vec<u64> {
        vec![self.v1, self.imm, self.flags, self.cell]
    }

    fn output_words(&(address, value): &(u64, u64)) -> Vec<u64> {
        vec![address, value]
    }
}

/// One store instance: the width in its flags, the address `v1 + imm`, the value `v2`, the cell it lands in.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Store {
    /// The width: one of the legal words.
    pub flags: u64,
    /// The base register's value.
    pub v1: u64,
    /// The value to store.
    pub v2: u64,
    /// The offset.
    pub imm: u64,
    /// The 64-bit cell holding the address.
    pub cell: u64,
}

impl Store {
    /// The bits holding the base-two logarithm of the width in bytes.
    pub const LOG_WIDTH: u64 = 0b11;
}

impl InstructionClass for Store {
    const CLASS: Class = Class::Store;

    /// Every width.
    const LEGAL: &'static [u64] = &[0, 1, 2, 3];

    /// The bus address, and the cell the store leaves.
    ///
    /// A misaligned store names no cell, so its new cell is never read.
    type Output = (u64, u64);

    fn eval(&self) -> (u64, u64) {
        let address = WordAccess::address(self.v1, self.imm);
        let log_width = self.flags & Self::LOG_WIDTH;
        let bits = 8 << log_width;
        let bus = WordAccess::bus_address(address, log_width);
        if bits == 64 {
            return (bus, self.v2);
        }

        // Replace the addressed bytes, keep the others.
        let mask = ((1u64 << bits) - 1) << (8 * (address & 7));
        (bus, (self.cell & !mask) | ((self.v2 << (8 * (address & 7))) & mask))
    }

    fn input_words(&self) -> Vec<u64> {
        vec![self.v1, self.v2, self.imm, self.flags, self.cell]
    }

    fn output_words(&(address, cell): &(u64, u64)) -> Vec<u64> {
        vec![address, cell]
    }
}

/// One low multiplication instance.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Mul {
    /// Whether to sign-extend a word product: one of the legal words.
    pub flags: u64,
    /// The first factor.
    pub v1: u64,
    /// The second factor.
    pub v2: u64,
}

impl Mul {
    /// Sign-extend the low 32 bits of the product.
    pub const WORD: u64 = 1 << 0;
}

impl InstructionClass for Mul {
    const CLASS: Class = Class::Mul;

    /// With or without the word form.
    const LEGAL: &'static [u64] = &[0, Self::WORD];

    /// The low word of the product.
    type Output = u64;

    fn eval(&self) -> u64 {
        let product = self.v1.wrapping_mul(self.v2);
        if self.flags & Self::WORD != 0 {
            sext32(product)
        } else {
            product
        }
    }

    fn input_words(&self) -> Vec<u64> {
        vec![self.v1, self.v2, self.flags]
    }

    fn output_words(&out: &u64) -> Vec<u64> {
        vec![out]
    }
}

/// One high multiplication instance.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Mulh {
    /// Which operands are signed: one of the legal words.
    pub flags: u64,
    /// The first factor.
    pub v1: u64,
    /// The second factor.
    pub v2: u64,
}

impl Mulh {
    /// The first operand is signed.
    pub const SIGNED_1: u64 = 1 << 0;
    /// The second operand is signed.
    pub const SIGNED_2: u64 = 1 << 1;
}

impl InstructionClass for Mulh {
    const CLASS: Class = Class::Mulh;

    /// `mulh`, `mulhsu`, `mulhu`.
    const LEGAL: &'static [u64] = &[Self::SIGNED_1 | Self::SIGNED_2, Self::SIGNED_1, 0];

    /// The high word of the 128-bit product.
    type Output = u64;

    fn eval(&self) -> u64 {
        let widen = |v: u64, signed: bool| if signed { v as i64 as i128 } else { v as i128 };
        let (s1, s2) = (self.flags & Self::SIGNED_1 != 0, self.flags & Self::SIGNED_2 != 0);
        (widen(self.v1, s1).wrapping_mul(widen(self.v2, s2)) >> 64) as u64
    }

    fn input_words(&self) -> Vec<u64> {
        vec![self.v1, self.v2, self.flags]
    }

    fn output_words(&out: &u64) -> Vec<u64> {
        vec![out]
    }
}

/// One division instance.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Div {
    /// Signed or not, quotient or remainder, word or not: one of the legal words.
    pub flags: u64,
    /// The dividend.
    pub v1: u64,
    /// The divisor.
    pub v2: u64,
}

impl Div {
    /// Divide signed operands.
    pub const SIGNED: u64 = 1 << 0;
    /// Output the remainder instead of the quotient.
    pub const REM: u64 = 1 << 1;
    /// Divide the low 32 bits, then sign-extend the low 32 bits of the result.
    pub const WORD: u64 = 1 << 2;

    /// The magnitudes of the quotient and the remainder.
    ///
    /// The prover supplies them to the division circuit, which checks them rather than computes them.
    ///
    /// Both are zero for a zero divisor, which the circuit ignores.
    pub fn hints(&self) -> (u64, u64) {
        let (signed, word) = (self.flags & Self::SIGNED != 0, self.flags & Self::WORD != 0);

        // The operands' magnitudes, on 32 bits for a word division.
        let magnitude = |v: u64| match (word, signed) {
            (false, false) => v,
            (false, true) => (v as i64).unsigned_abs(),
            (true, false) => v as u32 as u64,
            (true, true) => (v as i32 as i64).unsigned_abs(),
        };
        let (n, d) = (magnitude(self.v1), magnitude(self.v2));
        n.checked_div(d).map_or((0, 0), |q| (q, n % d))
    }
}

impl InstructionClass for Div {
    const CLASS: Class = Class::Div;

    /// Every combination.
    const LEGAL: &'static [u64] = &[0, 1, 2, 3, 4, 5, 6, 7];

    /// The quotient or the remainder.
    type Output = u64;

    /// The quotient or the remainder, as RISC-V defines them.
    ///
    /// - Dividing by zero gives all ones, and its remainder is the dividend.
    /// - The one signed overflow, `-2^63 / -1`, wraps to `-2^63` with remainder zero.
    /// - A word division extends the low 32 bits of both operands, divides, and sign-extends the result.
    fn eval(&self) -> u64 {
        let on = |flag: u64| self.flags & flag != 0;
        let (signed, rem, word) = (on(Self::SIGNED), on(Self::REM), on(Self::WORD));

        // A word division's operands, extended to 64 bits.
        let extend = |v: u64| match (word, signed) {
            (false, _) => v,
            (true, true) => sext32(v),
            (true, false) => v as u32 as u64,
        };
        let (n, d) = (extend(self.v1), extend(self.v2));

        // The quotient and the remainder, the zero divisor and the overflow included.
        let (q, r) = if d == 0 {
            (u64::MAX, n)
        } else if signed {
            let (n, d) = (n as i64, d as i64);
            (n.wrapping_div(d) as u64, n.wrapping_rem(d) as u64)
        } else {
            (n / d, n % d)
        };
        let out = if rem { r } else { q };
        if word { sext32(out) } else { out }
    }

    /// The operands, the flags, then the honest hints.
    fn input_words(&self) -> Vec<u64> {
        let (q, r) = self.hints();
        vec![self.v1, self.v2, self.flags, q, r]
    }

    /// The result, then the circuit's verdict on the hints, which honest hints keep at zero.
    fn output_words(&out: &u64) -> Vec<u64> {
        vec![out, 0]
    }
}

/// One BLAKE2s compression instance, `blake2s rs1, rs2`: the finalization word, the counter, the block.
///
/// It compresses the 128-byte block at `rs1`, with the byte counter in `rs2`.
///
/// The block holds three parts:
///
/// - bytes 0 to 31: the chaining value;
/// - bytes 32 to 63: where the new chaining value goes;
/// - bytes 64 to 127: the message.
///
/// Word `k` of the block is the cell at `rs1 ^ 8k`.
///
/// That is `rs1 + 8k` when `rs1` is aligned to the block, as the guest library ensures.
///
/// An unaligned `rs1` permutes the words.
///
/// That is a guest bug, but a deterministic and provable one.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Hash {
    /// The finalization word: one of the legal words.
    pub flags: u64,
    /// The byte counter.
    pub t: u64,
    /// The block's words as found.
    pub block: [u64; Hash::WORDS],
}

impl Hash {
    /// The chaining value's byte offset.
    pub const H: u64 = 0;
    /// The result's byte offset.
    pub const OUT: u64 = 32;
    /// The message's byte offset.
    pub const M: u64 = 64;
    /// The block's words.
    pub const WORDS: usize = 16;
    /// The block's bytes.
    pub const BLOCK_BYTES: u64 = 8 * Self::WORDS as u64;
    /// The finalization word of the last block: all ones.
    pub const FINAL: u64 = u32::MAX as u64;
}

impl InstructionClass for Hash {
    const CLASS: Class = Class::Hash;

    /// Not the last block, or the last.
    const LEGAL: &'static [u64] = &[0, Self::FINAL];

    /// The four words the instruction writes back: the new chaining value.
    type Output = [u64; 4];

    fn eval(&self) -> [u64; 4] {
        debug_assert!(Self::LEGAL.contains(&self.flags));

        // Split each 64-bit word into its two 32-bit halves, low first.
        let block = &self.block;
        let mut h: [u32; 8] = std::array::from_fn(|i| (block[i / 2] >> (32 * (i % 2))) as u32);
        let m: [u32; 16] = std::array::from_fn(|i| (block[8 + i / 2] >> (32 * (i % 2))) as u32);

        // Compress, then pair the halves back into words.
        primitives::hash::compress(&mut h, &m, self.t, self.flags == Self::FINAL);
        std::array::from_fn(|i| h[2 * i] as u64 | (h[2 * i + 1] as u64) << 32)
    }

    /// The counter, the finalization word, the chaining value, then the message.
    fn input_words(&self) -> Vec<u64> {
        [self.t, self.flags]
            .into_iter()
            .chain(self.block[..4].iter().chain(&self.block[8..]).copied())
            .collect()
    }

    fn output_words(out: &[u64; 4]) -> Vec<u64> {
        out.to_vec()
    }
}

/// A load's or a store's access to one memory cell.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct WordAccess {
    /// What goes on the memory bus: the cell's byte address, for an aligned access.
    pub address: u64,
    /// The cell before the access.
    pub old: u64,
    /// The cell after the access: the old value for a load.
    pub new: u64,
}

impl WordAccess {
    /// A load's or a store's byte address: `v1 + imm`.
    pub fn address(v1: u64, imm: u64) -> u64 {
        v1.wrapping_add(imm)
    }

    /// What an access of `2^log_width` bytes at `address` puts on the memory bus.
    ///
    /// That is the byte address of its 64-bit cell, with the bits that misalign the access kept.
    ///
    /// A cell's address is a multiple of 8.
    ///
    /// So a misaligned access names no cell at all, and the bus cannot balance.
    ///
    /// For example, a 4-byte load:
    ///
    /// - at `0x...08` puts `0x...08` on the bus, its cell;
    /// - at `0x...0c` also puts `0x...08` on the bus, the same cell's high half;
    /// - at `0x...0a` puts `0x...0a` on the bus, which is no cell.
    pub fn bus_address(address: u64, log_width: u64) -> u64 {
        (address & !7) | (address & ((1 << log_width) - 1))
    }

    /// Whether an access of `2^log_width` bytes at `address` is naturally aligned.
    pub fn is_aligned(address: u64, log_width: u64) -> bool {
        address & ((1 << log_width) - 1) == 0
    }
}

/// A hash row's access to its block.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct BlockAccess {
    /// The block's words as the row found them.
    pub block: [u64; Hash::WORDS],
    /// The new chaining value, written to the block's result words.
    pub out: [u64; 4],
}

impl From<Hash> for BlockAccess {
    /// The access of a compression: its block, and the result it writes.
    fn from(hash: Hash) -> Self {
        Self {
            block: hash.block,
            out: hash.eval(),
        }
    }
}

/// What an entry computes from the values it reads.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Outcome {
    /// The class's result.
    pub out: u64,
    /// Whether the class takes the jump.
    pub taken: bool,
    /// A load's or a store's cell access.
    pub access: Option<WordAccess>,
}

impl Entry {
    /// What this entry computes from its registers and, for a load or a store, the cell it names.
    ///
    /// The result holds whether or not a run could make the access.
    ///
    /// A hash computes nothing here: its block is the machine's to read.
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
            Class::Hash | Class::Illegal => (0, false, None),
        };
        Outcome { out, taken, access }
    }
}

/// Sign-extend the low 32 bits of `x`.
fn sext32(x: u64) -> u64 {
    x as u32 as i32 as i64 as u64
}

#[cfg(test)]
pub(super) mod tests {
    use super::*;
    use proptest::prelude::*;
    use proptest::sample::select;
    use proptest::strategy::BoxedStrategy;

    /// The words arithmetic most often gets wrong: zero, one, all ones, and the sign bits.
    const EDGES: [u64; 8] = [
        0,
        1,
        u64::MAX,
        1 << 63,
        (1 << 63) - 1,
        1 << 31,
        (1 << 31) - 1,
        0xffff_ffff,
    ];

    /// A 64-bit word biased toward edge values.
    ///
    /// - Edge words reach the carries, signs and overflows.
    /// - Zero- and sign-extended 32-bit values reach the word forms.
    /// - Small values reach the shift amounts and small divisors.
    /// - Any word covers the rest.
    pub(crate) fn edge_word() -> impl Strategy<Value = u64> {
        prop_oneof![
            1 => select(&EDGES[..]),
            1 => any::<u32>().prop_map(u64::from),
            1 => any::<i32>().prop_map(|x| x as i64 as u64),
            1 => 0u64..65,
            4 => any::<u64>(),
        ]
    }

    /// Any ALU instance, as the decoder makes them: one of `v2` and `imm` is zero.
    impl Arbitrary for Alu {
        type Parameters = ();
        type Strategy = BoxedStrategy<Self>;

        fn arbitrary_with((): ()) -> Self::Strategy {
            // Equal operands now and then, which random words never are.
            (
                select(Self::LEGAL),
                edge_word(),
                edge_word(),
                any::<bool>(),
                any::<bool>(),
            )
                .prop_map(|(flags, v1, v2, equal, immediate)| {
                    let v2 = if equal { v1 } else { v2 };
                    let (v2, imm) = if immediate { (0, v2) } else { (v2, 0) };
                    Self { flags, v1, v2, imm }
                })
                .boxed()
        }
    }

    /// Any shifter instance, as the decoder makes them: a register amount or a six-bit immediate.
    impl Arbitrary for Shift {
        type Parameters = ();
        type Strategy = BoxedStrategy<Self>;

        fn arbitrary_with((): ()) -> Self::Strategy {
            // Every amount now and then, which a random word's low bits reach slowly.
            (
                select(Self::LEGAL),
                edge_word(),
                edge_word(),
                0u64..64,
                any::<bool>(),
                any::<bool>(),
            )
                .prop_map(|(flags, v1, v2, amount, small, immediate)| {
                    let v2 = if small { amount } else { v2 };
                    let (v2, imm) = if immediate { (0, v2 & 63) } else { (v2, 0) };
                    Self { flags, v1, v2, imm }
                })
                .boxed()
        }
    }

    /// Any load instance, aligned half the time, which a random address seldom is.
    impl Arbitrary for Load {
        type Parameters = ();
        type Strategy = BoxedStrategy<Self>;

        fn arbitrary_with((): ()) -> Self::Strategy {
            (
                select(Self::LEGAL),
                edge_word(),
                0u64..4096,
                any::<u64>(),
                any::<bool>(),
            )
                .prop_map(|(flags, v1, imm, cell, aligned)| {
                    let mask = (1 << (flags & Self::LOG_WIDTH)) - 1;
                    let (v1, imm) = if aligned { (v1 & !mask, imm & !7) } else { (v1, imm) };
                    Self { flags, v1, imm, cell }
                })
                .boxed()
        }
    }

    /// Any aligned store instance.
    ///
    /// A misaligned store names no cell, so its new cell is never read and need not agree.
    impl Arbitrary for Store {
        type Parameters = ();
        type Strategy = BoxedStrategy<Self>;

        fn arbitrary_with((): ()) -> Self::Strategy {
            (select(Self::LEGAL), edge_word(), edge_word(), 0u64..4096, any::<u64>())
                .prop_map(|(flags, v1, v2, imm, cell)| Self {
                    flags,
                    v1: v1 & !((1 << flags) - 1),
                    v2,
                    imm: imm & !7,
                    cell,
                })
                .boxed()
        }
    }

    /// Any low multiplication instance.
    impl Arbitrary for Mul {
        type Parameters = ();
        type Strategy = BoxedStrategy<Self>;

        fn arbitrary_with((): ()) -> Self::Strategy {
            (select(Self::LEGAL), edge_word(), edge_word())
                .prop_map(|(flags, v1, v2)| Self { flags, v1, v2 })
                .boxed()
        }
    }

    /// Any high multiplication instance.
    impl Arbitrary for Mulh {
        type Parameters = ();
        type Strategy = BoxedStrategy<Self>;

        fn arbitrary_with((): ()) -> Self::Strategy {
            (select(Self::LEGAL), edge_word(), edge_word())
                .prop_map(|(flags, v1, v2)| Self { flags, v1, v2 })
                .boxed()
        }
    }

    /// Any division instance, its divisor biased toward zero and toward small values.
    impl Arbitrary for Div {
        type Parameters = ();
        type Strategy = BoxedStrategy<Self>;

        fn arbitrary_with((): ()) -> Self::Strategy {
            let divisor = prop_oneof![1 => Just(0), 4 => (edge_word(), 0u32..64).prop_map(|(w, s)| w >> s)];
            (select(Self::LEGAL), edge_word(), divisor)
                .prop_map(|(flags, v1, v2)| Self { flags, v1, v2 })
                .boxed()
        }
    }

    /// Any compression instance with a legal finalization word.
    impl Arbitrary for Hash {
        type Parameters = ();
        type Strategy = BoxedStrategy<Self>;

        fn arbitrary_with((): ()) -> Self::Strategy {
            (
                select(Self::LEGAL),
                edge_word(),
                proptest::array::uniform16(edge_word()),
            )
                .prop_map(|(flags, t, block)| Self { flags, t, block })
                .boxed()
        }
    }

    proptest! {
        #[test]
        fn a_load_reads_back_what_a_store_wrote(cell in any::<u64>(), value in edge_word(), offset in 0u64..8, signed in any::<bool>(), log_width in 0u64..4) {
            // Fixture: an aligned access of 2^log_width bytes in one cell.
            let address = 0x4000_0000 + (offset & !((1 << log_width) - 1));
            let bits = 8u32 << log_width;

            // A store, then a load of the same width at the same address.
            let (_, stored) = Store { flags: log_width, v1: address, v2: value, imm: 0, cell }.eval();
            let flags = if signed && log_width < 3 { Load::SIGNED | log_width } else { log_width };
            let (_, got) = Load { flags, v1: address, imm: 0, cell: stored }.eval();

            // The load returns the stored bytes, extended as the flags say.
            let expected = match (bits, signed) {
                (64, _) => value,
                (_, true) => ((value << (64 - bits)) as i64 >> (64 - bits)) as u64,
                (_, false) => value & ((1 << bits) - 1),
            };
            prop_assert_eq!(got, expected);
        }

        #[test]
        fn a_store_keeps_the_bytes_it_does_not_write(cell in any::<u64>(), value in any::<u64>(), offset in 0u64..8, log_width in 0u64..4) {
            // Fixture: an aligned access, and a mask of the bytes it covers.
            let address = offset & !((1 << log_width) - 1);
            let covered = if log_width == 3 { u64::MAX } else { ((1u64 << (8 << log_width)) - 1) << (8 * address) };

            // Outside the access, the cell is unchanged.
            let (_, new) = Store { flags: log_width, v1: address, v2: value, imm: 0, cell }.eval();
            prop_assert_eq!(new & !covered, cell & !covered);
        }

        #[test]
        fn the_bus_address_is_the_cell_exactly_when_aligned(address in any::<u64>(), log_width in 0u64..4) {
            // An aligned access names its cell, a misaligned one names no multiple of 8.
            let bus = WordAccess::bus_address(address, log_width);
            prop_assert_eq!(bus.is_multiple_of(8), WordAccess::is_aligned(address, log_width));
            prop_assert_eq!(bus & !7, address & !7);
        }

        #[test]
        fn div_hints_satisfy_the_division_identity(div in any::<Div>()) {
            // Invariant: |n| = q * |d| + r with r < |d|, over the integers.
            let (q, r) = div.hints();
            let word = div.flags & Div::WORD != 0;
            let signed = div.flags & Div::SIGNED != 0;
            let magnitude = |v: u64| match (word, signed) {
                (false, false) => v as u128,
                (false, true) => (v as i64).unsigned_abs() as u128,
                (true, false) => v as u32 as u128,
                (true, true) => (v as i32 as i64).unsigned_abs() as u128,
            };
            let (n, d) = (magnitude(div.v1), magnitude(div.v2));
            if d == 0 {
                prop_assert_eq!((q, r), (0, 0));
            } else {
                prop_assert_eq!(q as u128 * d + r as u128, n);
                prop_assert!((r as u128) < d);
            }
        }

        #[test]
        fn word_forms_compute_on_32_bits(v1 in edge_word(), v2 in edge_word()) {
            // Each word form is the 32-bit operation, sign-extended.
            let w = |x: u32| x as i32 as i64 as u64;
            let (a, b) = (v1 as u32, v2 as u32);
            let shift = |flags| Shift { flags, v1, v2, imm: 0 }.eval();
            prop_assert_eq!(Alu { flags: Alu::WORD, v1, v2, imm: 0 }.eval().0, w(a.wrapping_add(b)));
            prop_assert_eq!(Mul { flags: Mul::WORD, v1, v2 }.eval(), w(a.wrapping_mul(b)));
            prop_assert_eq!(shift(Shift::WORD), w(a << (b & 31)));
            prop_assert_eq!(shift(Shift::WORD | Shift::RIGHT), w(a >> (b & 31)));
            prop_assert_eq!(shift(Shift::WORD | Shift::RIGHT | Shift::ARITH), w(((a as i32) >> (b & 31)) as u32));
            if let (Some(q), Some(r)) = (a.checked_div(b), a.checked_rem(b)) {
                prop_assert_eq!(Div { flags: Div::WORD, v1, v2 }.eval(), w(q));
                prop_assert_eq!(Div { flags: Div::WORD | Div::REM, v1, v2 }.eval(), w(r));
            }
        }

        #[test]
        fn mulh_is_the_high_half_of_the_wide_product(v1 in edge_word(), v2 in edge_word()) {
            // The unsigned and signed high words, from 128-bit integers.
            prop_assert_eq!(Mulh { flags: 0, v1, v2 }.eval(), ((v1 as u128 * v2 as u128) >> 64) as u64);
            let signed = Mulh { flags: Mulh::SIGNED_1 | Mulh::SIGNED_2, v1, v2 }.eval();
            prop_assert_eq!(signed, ((v1 as i64 as i128 * v2 as i64 as i128) >> 64) as u64);
        }
    }

    #[test]
    fn division_edge_cases_follow_the_specification() {
        let (min, min32) = (i64::MIN as u64, i32::MIN as i64 as u64);
        let div = |flags, v1, v2| Div { flags, v1, v2 }.eval();

        // A zero divisor: all ones, and the remainder is the dividend.
        assert_eq!(div(0, 7, 0), u64::MAX);
        assert_eq!(div(Div::REM, 7, 0), 7);

        // The signed overflow: -2^63 / -1 wraps, remainder zero.
        assert_eq!(div(Div::SIGNED, min, u64::MAX), min);
        assert_eq!(div(Div::SIGNED | Div::REM, min, u64::MAX), 0);

        // The same on 32 bits: -2^31 / -1 wraps to -2^31, sign-extended.
        assert_eq!(div(Div::SIGNED | Div::WORD, min32, u64::MAX), min32);
    }
}
