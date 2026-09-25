//! What each [`Class`](super::Class) computes: the reference its circuit is tested
//! against, and what the interpreter runs. Defined on a class's legal flags only.

use super::{alu, div, hash, load, mul, mulh, shift, store};

fn sext32(x: u64) -> u64 {
    x as u32 as i32 as i64 as u64
}

/// `(out, taken)`.
pub fn alu(v1: u64, v2: u64, imm: u64, flags: u64) -> (u64, bool) {
    let on = |flag: u64| flags & flag != 0;
    let b = v2 ^ imm;
    let sum = if on(alu::SUB) {
        v1.wrapping_sub(b)
    } else {
        v1.wrapping_add(b)
    };
    let (lt, ltu, eq) = ((v1 as i64) < (b as i64), v1 < b, v1 == b);
    let mut out = if on(alu::SEL_LT) {
        lt as u64
    } else if on(alu::SEL_LTU) {
        ltu as u64
    } else if on(alu::SEL_AND) {
        v1 & b
    } else if on(alu::SEL_OR) {
        v1 | b
    } else if on(alu::SEL_XOR) {
        v1 ^ b
    } else if on(alu::WORD) {
        sext32(sum)
    } else {
        sum
    };
    if on(alu::CLEAR_BIT0) {
        out &= !1;
    }
    let taken = on(alu::ALWAYS)
        || (on(alu::BR_EQ) && eq)
        || (on(alu::BR_NE) && !eq)
        || (on(alu::BR_LT) && lt)
        || (on(alu::BR_GE) && !lt)
        || (on(alu::BR_LTU) && ltu)
        || (on(alu::BR_GEU) && !ltu);
    (out, taken)
}

pub fn shift(v1: u64, v2: u64, imm: u64, flags: u64) -> u64 {
    let (right, arith, word) = (
        flags & shift::RIGHT != 0,
        flags & shift::ARITH != 0,
        flags & shift::WORD != 0,
    );
    let amount = (v2 ^ imm) & if word { 31 } else { 63 };
    let x = match (word, arith) {
        (false, _) => v1,
        (true, true) => sext32(v1),
        (true, false) => v1 as u32 as u64,
    };
    let out = match (right, arith) {
        (false, _) => x << amount,
        (true, false) => x >> amount,
        (true, true) => ((x as i64) >> amount) as u64,
    };
    if word { sext32(out) } else { out }
}

/// A load or store's address, `v1 + imm`.
pub fn address(v1: u64, imm: u64) -> u64 {
    v1.wrapping_add(imm)
}

/// What a load or a store puts on the memory bus for `address`: the byte address of
/// its 64-bit cell, with the bits that misalign the access left in. A cell's address
/// is a multiple of 8, so a misaligned access names no cell at all.
pub fn bus_address(address: u64, log_width: u64) -> u64 {
    (address & !7) | (address & ((1 << log_width) - 1))
}

/// Whether an access of `2^log_width` bytes at `address` is naturally aligned.
pub fn is_aligned(address: u64, log_width: u64) -> bool {
    address & ((1 << log_width) - 1) == 0
}

/// The value a load at `address` returns, from the 64-bit cell holding it.
pub fn load(cell: u64, address: u64, flags: u64) -> u64 {
    let bits = 8 << (flags & load::LOG_WIDTH);
    let x = cell >> (8 * (address & 7));
    if bits == 64 {
        x
    } else if flags & load::SIGNED != 0 {
        (((x << (64 - bits)) as i64) >> (64 - bits)) as u64
    } else {
        x & ((1 << bits) - 1)
    }
}

/// The cell a store of `value` at `address` leaves.
pub fn store(cell: u64, address: u64, value: u64, flags: u64) -> u64 {
    let bits = 8 << (flags & store::LOG_WIDTH);
    if bits == 64 {
        return value;
    }
    let mask = ((1u64 << bits) - 1) << (8 * (address & 7));
    (cell & !mask) | ((value << (8 * (address & 7))) & mask)
}

pub fn mul(v1: u64, v2: u64, flags: u64) -> u64 {
    let product = v1.wrapping_mul(v2);
    if flags & mul::WORD != 0 {
        sext32(product)
    } else {
        product
    }
}

pub fn mulh(v1: u64, v2: u64, flags: u64) -> u64 {
    let widen = |v: u64, signed: bool| if signed { v as i64 as i128 } else { v as i128 };
    let product = widen(v1, flags & mulh::SIGNED_1 != 0).wrapping_mul(widen(v2, flags & mulh::SIGNED_2 != 0));
    (product >> 64) as u64
}

/// What the prover tells [`super::circuits::div`] beyond the operands: the magnitudes of
/// the quotient and the remainder, which the circuit checks rather than computes.
pub fn div_hints(v1: u64, v2: u64, flags: u64) -> (u64, u64) {
    let (signed, word) = (flags & div::SIGNED != 0, flags & div::WORD != 0);
    let magnitude = |v: u64| match (word, signed) {
        (false, false) => v,
        (false, true) => (v as i64).unsigned_abs(),
        (true, false) => v as u32 as u64,
        (true, true) => (v as i32 as i64).unsigned_abs(),
    };
    let (n, d) = (magnitude(v1), magnitude(v2));
    n.checked_div(d).map_or((0, 0), |q| (q, n % d))
}

/// One rule for the word forms: extend the low 32 bits of both operands, divide as
/// 64-bit, sign-extend the low 32 bits of the result.
pub fn div(v1: u64, v2: u64, flags: u64) -> u64 {
    let (signed, rem, word) = (flags & div::SIGNED != 0, flags & div::REM != 0, flags & div::WORD != 0);
    let extend = |v: u64| match (word, signed) {
        (false, _) => v,
        (true, true) => sext32(v),
        (true, false) => v as u32 as u64,
    };
    let (n, d) = (extend(v1), extend(v2));
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

/// The 32-bit words of `words`, little-endian.
fn halves<const N: usize>(words: &[u64]) -> [u32; N] {
    std::array::from_fn(|i| (words[i / 2] >> (32 * (i % 2))) as u32)
}

/// [`super::Class::Hash`]: the compression of the block's chaining value and message
/// with the counter `t` and the finalization word `flags`, as the four words the row
/// writes back. `block` is the block's sixteen words.
pub fn blake2s(block: &[u64; hash::WORDS], t: u64, flags: u64) -> [u64; 4] {
    let mut h: [u32; 8] = halves(&block[..4]);
    let m: [u32; 16] = halves(&block[8..]);
    debug_assert!(hash::LEGAL.contains(&flags));
    primitives::hash::compress(&mut h, &m, t, flags == hash::FINAL);
    std::array::from_fn(|i| h[2 * i] as u64 | (h[2 * i + 1] as u64) << 32)
}
