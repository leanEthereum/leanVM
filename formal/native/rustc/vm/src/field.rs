//! `K` and `E` on machine words (`NativeVm/Model/Field.lean`): a `K` element is its lane, an `E`
//! element its two limb lanes (`EW`). The products are `crates/verifier/src/field.rs`'s: the
//! carry-less product by integer multiplication, then the reduction.

/// The low 64 bits of a 64x64 carry-less product, by integer multiplication of the four classes
/// of bit positions mod 4 (`clmul_low`, `crates/verifier/src/field.rs`).
#[inline(always)]
const fn clmul_low(a: u64, b: u64) -> u64 {
    const M0: u64 = 0x1111_1111_1111_1111;
    const M1: u64 = M0 << 1;
    const M2: u64 = M0 << 2;
    const M3: u64 = M0 << 3;
    let (x0, x1, x2, x3) = (a & M0, a & M1, a & M2, a & M3);
    let (y0, y1, y2, y3) = (b & M0, b & M1, b & M2, b & M3);
    let z0 = x0.wrapping_mul(y0) ^ x1.wrapping_mul(y3) ^ x2.wrapping_mul(y2) ^ x3.wrapping_mul(y1);
    let z1 = x0.wrapping_mul(y1) ^ x1.wrapping_mul(y0) ^ x2.wrapping_mul(y3) ^ x3.wrapping_mul(y2);
    let z2 = x0.wrapping_mul(y2) ^ x1.wrapping_mul(y1) ^ x2.wrapping_mul(y0) ^ x3.wrapping_mul(y3);
    let z3 = x0.wrapping_mul(y3) ^ x1.wrapping_mul(y2) ^ x2.wrapping_mul(y1) ^ x3.wrapping_mul(y0);
    z0 & M0 | z1 & M1 | z2 & M2 | z3 & M3
}

/// The 128-bit carry-less product, low and high words: the high half is the low half of the
/// bit-reversed operands' product, reversed back (`clmul`).
#[inline(always)]
const fn clmul(a: u64, b: u64) -> (u64, u64) {
    let low = clmul_low(a, b);
    let high = clmul_low(a.reverse_bits(), b.reverse_bits()).reverse_bits() >> 1;
    (low, high)
}

/// A 128-bit carry-less product modulo `x^64 + x^4 + x^3 + x + 1` (`reduce`).
#[inline(always)]
const fn reduce(lo: u64, hi: u64) -> u64 {
    let spill = (hi >> 63) ^ (hi >> 61) ^ (hi >> 60);
    let v = hi ^ spill;
    lo ^ v ^ (v << 1) ^ (v << 3) ^ (v << 4)
}

/// `kmul`: the product in `K`.
#[inline(never)]
pub const fn kmul(a: u64, b: u64) -> u64 {
    let (lo, hi) = clmul(a, b);
    reduce(lo, hi)
}

/// `kmul a a`.
#[inline(always)]
fn ksquare(a: u64) -> u64 {
    kmul(a, a)
}

/// `kpow`: `a^n` in `K`, square-and-multiply from the low bit (`kpowAux`).
#[inline(never)]
pub fn kpow(a: u64, n: u64) -> u64 {
    let (mut base, mut acc, mut n) = (a, 1u64, n);
    while n != 0 {
        if n & 1 == 1 {
            acc = kmul(acc, base);
        }
        base = kmul(base, base);
        n >>= 1;
    }
    acc
}

/// `kinv`: `a^(2^64 - 2)`, `0` at `0`, by Itoh-Tsujii (`K::inv`, `crates/verifier/src/field.rs`).
#[inline(never)]
pub fn kinv(a: u64) -> u64 {
    #[inline(never)]
    fn sq(mut v: u64, n: u32) -> u64 {
        let mut i = 0;
        while i < n {
            v = ksquare(v);
            i += 1;
        }
        v
    }
    let t1 = a;
    let t2 = kmul(sq(t1, 1), t1);
    let t3 = kmul(sq(t2, 1), t1);
    let t6 = kmul(sq(t3, 3), t3);
    let t12 = kmul(sq(t6, 6), t6);
    let t24 = kmul(sq(t12, 12), t12);
    let t48 = kmul(sq(t24, 24), t24);
    let t60 = kmul(sq(t48, 12), t12);
    let t63 = kmul(sq(t60, 3), t3);
    sq(t63, 1)
}

/// `gpowK`: `g^n` as a lane.
#[inline(always)]
pub fn gpow_k(n: u64) -> u64 {
    kpow(2, n)
}

/// `EW`: an `E` element as its two limb lanes, limb `0` first.
#[derive(Clone, Copy, PartialEq, Eq, Debug, Default)]
#[repr(C)]
pub struct EW {
    pub c0: u64,
    pub c1: u64,
}

pub const ZERO: EW = EW::new(0, 0);
pub const ONE: EW = EW::new(1, 0);
/// `gen`: `g` in limb `0`.
pub const GEN: EW = EW::new(2, 0);

impl EW {
    #[inline(always)]
    pub const fn new(c0: u64, c1: u64) -> Self {
        Self { c0, c1 }
    }

    /// `EW.ofK`.
    #[inline(always)]
    pub const fn of_k(a: u64) -> Self {
        Self::new(a, 0)
    }

    /// `EW.add`.
    #[inline(always)]
    pub const fn add(self, b: Self) -> Self {
        Self::new(self.c0 ^ b.c0, self.c1 ^ b.c1)
    }

    /// `EW.mul`: `y² = x·y + 1`, Karatsuba over the carry-less products (`Mul for E`).
    #[inline(never)]
    pub fn mul(self, b: Self) -> Self {
        let (p0l, p0h) = clmul(self.c0, b.c0);
        let (p1l, p1h) = clmul(self.c1, b.c1);
        let (ml, mh) = clmul(self.c0 ^ self.c1, b.c0 ^ b.c1);
        let (ml, mh) = (ml ^ p0l ^ p1l, mh ^ p0h ^ p1h);
        // middle + p1 << 1, as 128 bits.
        let (sl, sh) = (p1l << 1, (p1h << 1) | (p1l >> 63));
        Self::new(reduce(p0l ^ p1l, p0h ^ p1h), reduce(ml ^ sl, mh ^ sh))
    }

    /// `EW.scale`: the product by a `K` lane, limb by limb.
    #[inline(always)]
    pub fn scale(k: u64, x: Self) -> Self {
        Self::new(kmul(k, x.c0), kmul(k, x.c1))
    }

    /// `EW.sqIter`: `x^(2^k)`.
    #[inline(never)]
    pub fn sq_iter(k: usize, mut x: Self) -> Self {
        let mut i = 0;
        while i < k {
            x = x.mul(x);
            i += 1;
        }
        x
    }
}

impl core::ops::Add for EW {
    type Output = Self;
    #[inline(always)]
    fn add(self, b: Self) -> Self {
        EW::add(self, b)
    }
}

impl core::ops::Mul for EW {
    type Output = Self;
    #[inline(always)]
    fn mul(self, b: Self) -> Self {
        EW::mul(self, b)
    }
}

/// `gpow`: `g^index` in limb `0`.
#[inline(always)]
pub fn gpow(index: u64) -> EW {
    EW::of_k(gpow_k(index))
}

/// `sumE`.
#[inline(never)]
pub fn sum_e(values: &[EW]) -> EW {
    values.iter().fold(ZERO, |acc, &v| acc + v)
}

/// `prodE`.
#[inline(never)]
pub fn prod_e(values: &[EW]) -> EW {
    values.iter().fold(ONE, |acc, &v| acc * v)
}

/// `powers`: `1, base, base², …`, as many as `out` holds.
#[inline(never)]
pub fn powers(base: EW, out: &mut [EW]) {
    let mut power = ONE;
    for slot in out.iter_mut() {
        *slot = power;
        power = power * base;
    }
}

/// `eqKernel`: the `2^|point|` equality weights, the first coordinate the lowest bit; `None` when
/// `out` is shorter. The kernel fills `out[..2^|point|]`.
#[inline(never)]
pub fn eq_kernel(point: &[EW], out: &mut [EW]) -> Option<usize> {
    let size = 1usize.checked_shl(u32::try_from(point.len()).ok()?)?;
    if out.len() < size {
        return None;
    }
    let first = out.first_mut()?;
    *first = ONE;
    let mut n = 1;
    for &r in point {
        // out.map (· * (1 + r)) ++ out.map (· * r), in place: the high half first, then
        // `lo·(1 + r) = lo + lo·r`, one product a pair.
        let (low, high) = out.split_at_mut_checked(n)?;
        for (lo, hi) in low.iter_mut().zip(high.iter_mut()) {
            *hi = *lo * r;
            *lo = *lo + *hi;
        }
        n *= 2;
    }
    Some(size)
}

/// `multilinearEval`: `point.foldl foldPairs mle`, its first entry or `0`. Folded as the entries
/// arrive, one pending entry per level: entry `i` of level `k` pairs with entry `i + 1` when `i` is
/// even, as `foldPairs` pairs them, and an unpaired last entry is dropped as `foldPairs` drops it.
#[inline(never)]
pub fn multilinear_eval_by(n: usize, entry: impl Fn(usize) -> EW, point: &[EW]) -> EW {
    let m = point.len();
    if m >= 64 {
        // Level `m` would need `2^m` entries.
        return ZERO;
    }
    let mut pending = [ZERO; 64];
    let mut full = [false; 64]; // level `k` holds a pending entry
    for i in 0..n {
        let mut value = entry(i);
        let mut level = 0;
        loop {
            if level >= m {
                // The first entry to reach level `m` is the result.
                return value;
            }
            let Some(f) = full.get_mut(level) else { return ZERO };
            if !*f {
                *f = true;
                if let Some(slot) = pending.get_mut(level) {
                    *slot = value;
                }
                break;
            }
            *f = false;
            let (a, r) = match (pending.get(level), point.get(level)) {
                (Some(&a), Some(&r)) => (a, r),
                _ => return ZERO,
            };
            value = a * (ONE + r) + value * r;
            level += 1;
        }
    }
    ZERO
}

/// `multilinearEval` of an array.
#[inline(always)]
pub fn multilinear_eval(mle: &[EW], point: &[EW]) -> EW {
    multilinear_eval_by(mle.len(), |i| mle.get(i).copied().unwrap_or(ZERO), point)
}

/// `eqEval`: `Π (1 + x + y)` over the common length.
#[inline(never)]
pub fn eq_eval(left: &[EW], right: &[EW]) -> EW {
    left.iter().zip(right).fold(ONE, |acc, (&x, &z)| acc * (ONE + x + z))
}

/// `eqEval` with its left side given by index, `n` entries of it.
#[inline(never)]
pub fn eq_eval_fn(n: usize, left: impl Fn(usize) -> EW, right: &[EW]) -> EW {
    right.iter().take(n).enumerate().fold(ONE, |acc, (k, &z)| acc * (ONE + left(k) + z))
}

/// `dot`: `Σ x·y` over the common length.
#[inline(never)]
pub fn dot(left: &[EW], right: &[EW]) -> EW {
    left.iter().zip(right).fold(ZERO, |acc, (&x, &y)| acc + x * y)
}

/// The bit length of `v` (`0` at `0`), by halving the range: no bit-scan instruction (`bsr`,
/// `bsf`, `clz`), which Kraken's x86-64 lacks.
#[inline(never)]
pub const fn bit_length(v: u64) -> usize {
    let (mut n, mut v, mut s) = (0, v, 32);
    while s > 0 {
        if v >> s != 0 {
            n += s;
            v >>= s;
        }
        s /= 2;
    }
    n + (v != 0) as usize
}

/// `n >>> s` on `Nat`s below `2^64`.
#[inline(always)]
pub fn shr(n: u64, s: usize) -> u64 {
    if s >= 64 { 0 } else { n >> s }
}

/// `EW.ofNat ((n >>> k) % 2)`.
#[inline(always)]
pub fn bit_e(n: u64, k: usize) -> EW {
    EW::of_k(shr(n, k) & 1)
}

/// `paddingWeight`: the multilinear extension of `[z ≥ n]`, from the low bit.
#[inline(never)]
pub fn padding_weight(point: &[EW], n: u64) -> EW {
    let mut pad = ONE;
    for (k, &r) in point.iter().enumerate() {
        let b = bit_e(n, k);
        pad = (ONE + b) * r + (ONE + b + r) * pad;
    }
    (ONE + bit_e(n, point.len())) * pad
}

/// `indexMleFrom`.
#[inline(never)]
pub fn index_mle_from(generator_power: EW, point: &[EW]) -> EW {
    let (mut acc, mut power) = (ONE, generator_power);
    for &r in point {
        acc = acc * (ONE + r * (ONE + power));
        power = power * power;
    }
    acc
}

/// `indexMle`.
#[inline(always)]
pub fn index_mle(point: &[EW]) -> EW {
    index_mle_from(GEN, point)
}

/// `polyEval`: Horner's rule, constant first.
#[inline(never)]
pub fn poly_eval(coefficients: &[EW], point: EW) -> EW {
    coefficients.iter().rev().fold(ZERO, |acc, &c| acc * point + c)
}

/// `selectorPoint`: the low `out.len()` bits of `selector`, lowest first.
#[inline(never)]
pub fn selector_point(selector: u64, out: &mut [EW]) {
    for (bit, slot) in out.iter_mut().enumerate() {
        *slot = bit_e(selector, bit);
    }
}
