//! What each instruction class computes.
//!
//! Each class is a type wrapping its flag word.
//!
//! The type names the flags, lists the legal words, and computes the class's function.
//!
//! These functions are the reference.
//!
//! The interpreter runs them, and each class's circuit is tested against them.
//!
//! Each one is defined on its class's legal flag words only.

use super::entry::{Class, Entry};

/// The ALU's function, selected by its flag word: add, subtract, compare, bitwise logic, branches and jumps.
///
/// The second operand `b` is `v2 ^ imm`.
///
/// One of the two is always zero.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Alu(pub u64);

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

    /// The legal words.
    ///
    /// At most one output selector and at most one branch condition is set.
    pub const LEGAL: [u64; 17] = [
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

    /// The comparison of a branch with function `funct3`.
    ///
    /// Returns `None` for functions 2 and 3, which are reserved.
    pub fn branch(funct3: u32) -> Option<Self> {
        let condition = match funct3 {
            0 => Self::BR_EQ,
            1 => Self::BR_NE,
            4 => Self::BR_LT,
            5 => Self::BR_GE,
            6 => Self::BR_LTU,
            7 => Self::BR_GEU,
            _ => return None,
        };
        Some(Self(Self::SUB | condition))
    }

    /// The output, and whether the jump is taken.
    pub fn eval(self, v1: u64, v2: u64, imm: u64) -> (u64, bool) {
        let on = |flag: u64| self.0 & flag != 0;
        let b = v2 ^ imm;

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
}

/// The shifter's function, selected by its flag word.
///
/// The amount is the low 6 bits of `v2 ^ imm`, or 5 bits for a word shift.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Shift(pub u64);

impl Shift {
    /// Shift right instead of left.
    pub const RIGHT: u64 = 1 << 0;
    /// Fill a right shift with the sign bit.
    pub const ARITH: u64 = 1 << 1;
    /// Shift the low 32 bits, then sign-extend the low 32 bits of the result.
    pub const WORD: u64 = 1 << 2;

    /// The legal words: an arithmetic shift is always a right shift.
    pub const LEGAL: [u64; 6] = [
        0,
        Self::RIGHT,
        Self::RIGHT | Self::ARITH,
        Self::WORD,
        Self::WORD | Self::RIGHT,
        Self::WORD | Self::RIGHT | Self::ARITH,
    ];

    /// The shifted value.
    pub fn eval(self, v1: u64, v2: u64, imm: u64) -> u64 {
        let on = |flag: u64| self.0 & flag != 0;
        let (right, arith, word) = (on(Self::RIGHT), on(Self::ARITH), on(Self::WORD));
        let amount = (v2 ^ imm) & if word { 31 } else { 63 };

        // A word shift starts from the low 32 bits, extended as the shift fills.
        let x = match (word, arith) {
            (false, _) => v1,
            (true, true) => sext32(v1),
            (true, false) => v1 as u32 as u64,
        };

        // Shift, then sign-extend a word result.
        let out = match (right, arith) {
            (false, _) => x << amount,
            (true, false) => x >> amount,
            (true, true) => ((x as i64) >> amount) as u64,
        };
        if word { sext32(out) } else { out }
    }
}

/// A load's function, selected by its flag word: the width, then the extension.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Load(pub u64);

impl Load {
    /// The bits holding the base-two logarithm of the width in bytes.
    pub const LOG_WIDTH: u64 = 0b11;
    /// Sign-extend the value instead of zero-extending it.
    pub const SIGNED: u64 = 1 << 2;

    /// The legal words: a double word has no extension.
    pub const LEGAL: [u64; 7] = [Self::SIGNED, Self::SIGNED | 1, Self::SIGNED | 2, 3, 0, 1, 2];

    /// The load with function `funct3`.
    ///
    /// - 0 to 2 are `lb`, `lh` and `lw`: signed, of width 2^funct3.
    /// - 3 is `ld`, which has no extension.
    /// - 4 to 6 are `lbu`, `lhu` and `lwu`: unsigned, of width 2^(funct3 - 4).
    ///
    /// Returns `None` for function 7, which is reserved.
    pub fn from_funct3(funct3: u32) -> Option<Self> {
        match funct3 {
            0..=2 => Some(Self(Self::SIGNED | funct3 as u64)),
            3 => Some(Self(3)),
            4..=6 => Some(Self((funct3 - 4) as u64)),
            _ => None,
        }
    }

    /// The base-two logarithm of the width in bytes.
    pub fn log_width(self) -> u64 {
        self.0 & Self::LOG_WIDTH
    }

    /// The value a load at `address` returns, read from the 64-bit cell holding it.
    pub fn eval(self, cell: u64, address: u64) -> u64 {
        let bits = 8 << self.log_width();

        // Bring the addressed byte down to bit 0.
        let x = cell >> (8 * (address & 7));

        // Keep the width, extended as the flags say.
        if bits == 64 {
            x
        } else if self.0 & Self::SIGNED != 0 {
            (((x << (64 - bits)) as i64) >> (64 - bits)) as u64
        } else {
            x & ((1 << bits) - 1)
        }
    }
}

/// A store's function, selected by its flag word: the width.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Store(pub u64);

impl Store {
    /// The bits holding the base-two logarithm of the width in bytes.
    pub const LOG_WIDTH: u64 = 0b11;

    /// The legal words: every width.
    pub const LEGAL: [u64; 4] = [0, 1, 2, 3];

    /// The base-two logarithm of the width in bytes.
    pub fn log_width(self) -> u64 {
        self.0 & Self::LOG_WIDTH
    }

    /// The cell a store of `value` at `address` leaves.
    pub fn eval(self, cell: u64, address: u64, value: u64) -> u64 {
        let bits = 8 << self.log_width();
        if bits == 64 {
            return value;
        }

        // Replace the addressed bytes, keep the others.
        let mask = ((1u64 << bits) - 1) << (8 * (address & 7));
        (cell & !mask) | ((value << (8 * (address & 7))) & mask)
    }
}

/// The low multiplication's function, selected by its flag word.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Mul(pub u64);

impl Mul {
    /// Sign-extend the low 32 bits of the product.
    pub const WORD: u64 = 1 << 0;

    /// The legal words.
    pub const LEGAL: [u64; 2] = [0, Self::WORD];

    /// The low word of the product.
    pub fn eval(self, v1: u64, v2: u64) -> u64 {
        let product = v1.wrapping_mul(v2);
        if self.0 & Self::WORD != 0 {
            sext32(product)
        } else {
            product
        }
    }
}

/// The high multiplication's function, selected by its flag word: which operands are signed.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Mulh(pub u64);

impl Mulh {
    /// The first operand is signed.
    pub const SIGNED_1: u64 = 1 << 0;
    /// The second operand is signed.
    pub const SIGNED_2: u64 = 1 << 1;

    /// The legal words: `mulh`, `mulhsu`, `mulhu`.
    pub const LEGAL: [u64; 3] = [Self::SIGNED_1 | Self::SIGNED_2, Self::SIGNED_1, 0];

    /// The high word of the 128-bit product.
    pub fn eval(self, v1: u64, v2: u64) -> u64 {
        let widen = |v: u64, signed: bool| if signed { v as i64 as i128 } else { v as i128 };
        let (s1, s2) = (self.0 & Self::SIGNED_1 != 0, self.0 & Self::SIGNED_2 != 0);
        (widen(v1, s1).wrapping_mul(widen(v2, s2)) >> 64) as u64
    }
}

/// The division's function, selected by its flag word.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Div(pub u64);

impl Div {
    /// Divide signed operands.
    pub const SIGNED: u64 = 1 << 0;
    /// Output the remainder instead of the quotient.
    pub const REM: u64 = 1 << 1;
    /// Divide the low 32 bits, then sign-extend the low 32 bits of the result.
    pub const WORD: u64 = 1 << 2;

    /// The legal words: every combination.
    pub const LEGAL: [u64; 8] = [0, 1, 2, 3, 4, 5, 6, 7];

    /// The quotient or the remainder, as RISC-V defines them.
    ///
    /// - Dividing by zero gives all ones, and its remainder is the dividend.
    /// - The one signed overflow, `-2^63 / -1`, wraps to `-2^63` with remainder zero.
    /// - A word division extends the low 32 bits of both operands, divides, and sign-extends the result.
    pub fn eval(self, v1: u64, v2: u64) -> u64 {
        let on = |flag: u64| self.0 & flag != 0;
        let (signed, rem, word) = (on(Self::SIGNED), on(Self::REM), on(Self::WORD));

        // A word division's operands, extended to 64 bits.
        let extend = |v: u64| match (word, signed) {
            (false, _) => v,
            (true, true) => sext32(v),
            (true, false) => v as u32 as u64,
        };
        let (n, d) = (extend(v1), extend(v2));

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

    /// The magnitudes of the quotient and the remainder.
    ///
    /// The prover supplies them to the division circuit, which checks them rather than computes them.
    ///
    /// Both are zero for a zero divisor, which the circuit ignores.
    pub fn hints(self, v1: u64, v2: u64) -> (u64, u64) {
        let (signed, word) = (self.0 & Self::SIGNED != 0, self.0 & Self::WORD != 0);

        // The operands' magnitudes, on 32 bits for a word division.
        let magnitude = |v: u64| match (word, signed) {
            (false, false) => v,
            (false, true) => (v as i64).unsigned_abs(),
            (true, false) => v as u32 as u64,
            (true, true) => (v as i32 as i64).unsigned_abs(),
        };
        let (n, d) = (magnitude(v1), magnitude(v2));
        n.checked_div(d).map_or((0, 0), |q| (q, n % d))
    }
}

/// The BLAKE2s compression, `blake2s rs1, rs2`, selected by its flag word: the finalization word.
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
pub struct Hash(pub u64);

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
    /// The legal words.
    pub const LEGAL: [u64; 2] = [0, Self::FINAL];

    /// The compression of a block with counter `t`, as the four words the instruction writes back.
    pub fn compress(self, block: &[u64; Self::WORDS], t: u64) -> [u64; 4] {
        debug_assert!(Self::LEGAL.contains(&self.0));

        // Split each 64-bit word into its two 32-bit halves, low first.
        let mut h: [u32; 8] = std::array::from_fn(|i| (block[i / 2] >> (32 * (i % 2))) as u32);
        let m: [u32; 16] = std::array::from_fn(|i| (block[8 + i / 2] >> (32 * (i % 2))) as u32);

        // Compress, then pair the halves back into words.
        primitives::hash::compress(&mut h, &m, t, self.0 == Self::FINAL);
        std::array::from_fn(|i| h[2 * i] as u64 | (h[2 * i + 1] as u64) << 32)
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

impl BlockAccess {
    /// The compression of `block` with counter `t` and finalization word `flags`.
    pub fn compress(block: [u64; Hash::WORDS], t: u64, flags: u64) -> Self {
        Self {
            block,
            out: Hash(flags).compress(&block, t),
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
        // A load's or a store's address, and its access to the cell.
        let address = WordAccess::address(v1, self.imm);
        let access = |new: u64, log_width: u64| WordAccess {
            address: WordAccess::bus_address(address, log_width),
            old: cell,
            new,
        };

        // The class's function, and the access of a memory class.
        let flags = self.flags;
        let (out, taken, access) = match self.class {
            Class::Alu => {
                let (out, taken) = Alu(flags).eval(v1, v2, self.imm);
                (out, taken, None)
            }
            Class::Shift => (Shift(flags).eval(v1, v2, self.imm), false, None),
            Class::Mul => (Mul(flags).eval(v1, v2), false, None),
            Class::Mulh => (Mulh(flags).eval(v1, v2), false, None),
            Class::Div => (Div(flags).eval(v1, v2), false, None),
            Class::Load => {
                let load = Load(flags);
                (load.eval(cell, address), false, Some(access(cell, load.log_width())))
            }
            Class::Store => {
                let store = Store(flags);
                let new = store.eval(cell, address, v2);
                (0, false, Some(access(new, store.log_width())))
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

    proptest! {
        #[test]
        fn a_load_reads_back_what_a_store_wrote(cell in any::<u64>(), value in edge_word(), offset in 0u64..8, signed in any::<bool>(), log_width in 0u64..4) {
            // Fixture: an aligned access of 2^log_width bytes in one cell.
            let address = 0x4000_0000 + (offset & !((1 << log_width) - 1));
            let bits = 8u32 << log_width;

            // A store, then a load of the same width at the same address.
            let flags = if signed && log_width < 3 { Load::SIGNED | log_width } else { log_width };
            let got = Load(flags).eval(Store(log_width).eval(cell, address, value), address);

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
            prop_assert_eq!(Store(log_width).eval(cell, address, value) & !covered, cell & !covered);
        }

        #[test]
        fn the_bus_address_is_the_cell_exactly_when_aligned(address in any::<u64>(), log_width in 0u64..4) {
            // An aligned access names its cell, a misaligned one names no multiple of 8.
            let bus = WordAccess::bus_address(address, log_width);
            prop_assert_eq!(bus.is_multiple_of(8), WordAccess::is_aligned(address, log_width));
            prop_assert_eq!(bus & !7, address & !7);
        }

        #[test]
        fn div_hints_satisfy_the_division_identity(v1 in edge_word(), v2 in edge_word(), flags in select(&Div::LEGAL[..])) {
            // Invariant: |n| = q * |d| + r with r < |d|, over the integers.
            let (q, r) = Div(flags).hints(v1, v2);
            let word = flags & Div::WORD != 0;
            let signed = flags & Div::SIGNED != 0;
            let magnitude = |v: u64| match (word, signed) {
                (false, false) => v as u128,
                (false, true) => (v as i64).unsigned_abs() as u128,
                (true, false) => v as u32 as u128,
                (true, true) => (v as i32 as i64).unsigned_abs() as u128,
            };
            let (n, d) = (magnitude(v1), magnitude(v2));
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
            prop_assert_eq!(Alu(Alu::WORD).eval(v1, v2, 0).0, w(a.wrapping_add(b)));
            prop_assert_eq!(Mul(Mul::WORD).eval(v1, v2), w(a.wrapping_mul(b)));
            prop_assert_eq!(Shift(Shift::WORD).eval(v1, v2, 0), w(a << (b & 31)));
            prop_assert_eq!(Shift(Shift::WORD | Shift::RIGHT).eval(v1, v2, 0), w(a >> (b & 31)));
            let sra = Shift(Shift::WORD | Shift::RIGHT | Shift::ARITH).eval(v1, v2, 0);
            prop_assert_eq!(sra, w(((a as i32) >> (b & 31)) as u32));
            if let (Some(q), Some(r)) = (a.checked_div(b), a.checked_rem(b)) {
                prop_assert_eq!(Div(Div::WORD).eval(v1, v2), w(q));
                prop_assert_eq!(Div(Div::WORD | Div::REM).eval(v1, v2), w(r));
            }
        }

        #[test]
        fn mulh_is_the_high_half_of_the_wide_product(v1 in edge_word(), v2 in edge_word()) {
            // The unsigned and signed high words, from 128-bit integers.
            prop_assert_eq!(Mulh(0).eval(v1, v2), ((v1 as u128 * v2 as u128) >> 64) as u64);
            let signed = Mulh(Mulh::SIGNED_1 | Mulh::SIGNED_2).eval(v1, v2);
            prop_assert_eq!(signed, ((v1 as i64 as i128 * v2 as i64 as i128) >> 64) as u64);
        }
    }

    #[test]
    fn division_edge_cases_follow_the_specification() {
        let min = i64::MIN as u64;

        // A zero divisor: all ones, and the remainder is the dividend.
        assert_eq!(Div(0).eval(7, 0), u64::MAX);
        assert_eq!(Div(Div::REM).eval(7, 0), 7);

        // The signed overflow: -2^63 / -1 wraps, remainder zero.
        assert_eq!(Div(Div::SIGNED).eval(min, u64::MAX), min);
        assert_eq!(Div(Div::SIGNED | Div::REM).eval(min, u64::MAX), 0);

        // The same on 32 bits: -2^31 / -1 wraps to -2^31, sign-extended.
        let min32 = i32::MIN as i64 as u64;
        assert_eq!(Div(Div::SIGNED | Div::WORD).eval(min32, u64::MAX), min32);
    }
}
