//! Runtime hint machinery: the resolved hint ops an [`isa::Program`] carries ([`RHint`], from the `isa` crate the
//! compiler shares), and the g-power table + reverse index the hint interpreter grows on demand.

use primitives::field::{F64, div_by_g, mul_by_g};
use std::collections::HashMap;
use std::hash::{BuildHasherDefault, Hasher};

pub(crate) use isa::{BitsDest, BufSize, RHint};

/// The cells a provable run can address, which the [`GPow`] index covers: a memory of `2^29`
/// cells would overflow the `2^30` stack with its three columns, so no larger one can be committed.
pub(crate) const MAX_CELLS: u32 = 1 << (verifier::MAX_STACKED_LOG - 2);

/// The exponents the [`GPow`] table can cover: an address below [`MAX_CELLS`], or a `pc` (a return
/// target `pc + 2` too) of a bytecode a stack commits, below `2^30`.
pub(crate) const MAX_INDEX: usize = 1 << verifier::MAX_LOG_BYTECODE;

/// The `g^k` table paired with a reverse index `g^k ↦ k`, both grown on demand
/// (recursion depth, and so the address range, is unbounded).
///
/// The interpreter needs both directions: a cell index becomes the address `g^k`,
/// and a pointer word read back out of memory must be inverted to the index it
/// addresses. The reverse index holds the exponents [`Self::note`] announces, the
/// bases of the frames and buffers the run stores as pointers, and every `STRIDE`th
/// one: a lookup that misses divides by `g` until it meets one of those, then
/// announces the result. Past the table, a hinted g-power or a range check's
/// complement, it falls back to `bounded_dlog` below the caller's bound.
pub struct GPow {
    pow: Vec<F64>,
    /// `g^k ↦ k` for the announced `k`.
    index: WordMap,
    /// The same for every multiple `k` of `STRIDE` that `pow` covers.
    coarse: WordMap,
}

/// A map for the interpreter's hot lookups, by field element, cell or stream name, which the default hasher would
/// make cost more than the step that looks them up. The keys are not chosen by an adversary.
pub(crate) type QuickMap<K, V> = HashMap<K, V, BuildHasherDefault<QuickHasher>>;
type WordMap = QuickMap<u64, u32>;

/// One multiply per word, FNV-1a over bytes.
#[derive(Default)]
pub(crate) struct QuickHasher(u64);

impl Hasher for QuickHasher {
    fn write(&mut self, bytes: &[u8]) {
        for &b in bytes {
            self.0 = (self.0 ^ u64::from(b)).wrapping_mul(0x0100_0000_01b3);
        }
    }

    fn write_u32(&mut self, x: u32) {
        self.write_u64(x.into());
    }

    fn write_u64(&mut self, x: u64) {
        self.0 = (self.0 ^ x ^ (x >> 32)).wrapping_mul(0x9E37_79B9_7F4A_7C15);
    }

    fn finish(&self) -> u64 {
        self.0
    }
}

/// Spacing of the coarse index, and so the most divisions a missed lookup costs.
const STRIDE: usize = 64;

impl GPow {
    /// Seeded with `g^0 = 1`, grown to cover index `upto`, nothing announced.
    pub fn new(upto: usize) -> Self {
        let mut g = Self {
            pow: vec![F64::ONE],
            index: WordMap::default(),
            coarse: WordMap::from_iter([(F64::ONE.0, 0)]),
        };
        g.grow_to(upto);
        g
    }

    /// `g^k`. Panics past the grown range, which is the honest outcome: every
    /// index the interpreter reads has been covered by a [`Self::grow_to`].
    pub fn pow(&self, k: usize) -> F64 {
        self.pow[k]
    }

    /// Extend the forward table to cover index `upto`.
    pub fn grow_to(&mut self, upto: usize) {
        if upto < self.pow.len() {
            return;
        }
        assert!(upto < MAX_INDEX, "address space overflow (program too large)");
        // ×g is ×x = `mul_by_g` (shift+fold), not a full product.
        for k in self.pow.len()..=upto {
            let p = mul_by_g(self.pow[k - 1]);
            self.pow.push(p);
            if k.is_multiple_of(STRIDE) {
                self.coarse.insert(p.0, k as u32);
            }
        }
    }

    /// Announce that `g^k` may come back for inversion, because the interpreter
    /// is about to store it in memory as an address. Covers `k` first.
    pub fn note(&mut self, k: usize) {
        self.grow_to(k);
        self.index.insert(self.pow[k].0, k as u32);
    }

    /// The discrete log of `x`, if it is a g-power below `MAX_CELLS`, covering it.
    pub fn log(&mut self, x: F64) -> Option<u32> {
        self.log_below(x, MAX_CELLS as usize)
    }

    /// The discrete log of `x`, if it is a g-power below `bound` (at most `MAX_INDEX`), covering it.
    pub(crate) fn log_below(&mut self, x: F64, bound: usize) -> Option<u32> {
        debug_assert!(bound <= MAX_INDEX);
        if let Some(k) = self.lookup(x) {
            return ((k as usize) < bound).then_some(k);
        }
        let k = self
            .resolve(x)
            .or_else(|| bounded_dlog(x, crate::log2_ceil_usize(bound) as u32).map(|k| k as usize))?;
        (k < bound).then(|| {
            self.note(k);
            k as u32
        })
    }

    /// The exponent of `x` if announced.
    pub(crate) fn lookup(&self, x: F64) -> Option<u32> {
        self.index.get(&x.0).copied()
    }

    /// The exponent of `x` if it is not announced: divide by `g` down to a multiple of
    /// `STRIDE`. Past the table by fewer than `STRIDE` too, so that a run of addresses
    /// climbing past the table stays off the discrete log.
    fn resolve(&self, x: F64) -> Option<usize> {
        let mut y = x;
        for j in 0..STRIDE {
            if let Some(&k) = self.coarse.get(&y.0) {
                return Some(k as usize + j);
            }
            y = div_by_g(y);
        }
        None
    }
}

/// Find `n < 2^nbits` with `g^n = x` (for `nbits` below 17, any `n < 2^17`), by
/// baby-step giant-step: a baby table of `g^j` for `j < 2^17`, built once per
/// process, and the giant step `×g^(-2^17)`.
pub(crate) fn bounded_dlog(x: F64, nbits: u32) -> Option<u128> {
    const LOG_BABY: u32 = 17;
    static TABLE: std::sync::OnceLock<(GPow, F64)> = std::sync::OnceLock::new();
    let (baby, giant) = TABLE.get_or_init(|| {
        let mut baby = GPow::new((1usize << LOG_BABY) - 1);
        for j in 0..1usize << LOG_BABY {
            baby.note(j);
        }
        // g^(2^17), one past the table; its inverse is the giant step.
        let giant = mul_by_g(baby.pow((1usize << LOG_BABY) - 1)).inv();
        (baby, giant)
    });
    let mut y = x;
    let max_giant = if nbits > LOG_BABY {
        1u64 << (nbits - LOG_BABY)
    } else {
        1
    };
    for a in 0..max_giant {
        if let Some(j) = baby.lookup(y) {
            return Some((a as u128) << LOG_BABY | j as u128);
        }
        y *= *giant;
    }
    None
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Every covered exponent resolves through the coarse index without being announced.
    #[test]
    fn log_resolves_unannounced_exponents() {
        let mut g = GPow::new(10_000);
        for k in [0, 1, 63, 64, 65, 4_095, 9_999, 10_000] {
            assert_eq!(g.log(g.pow(k)), Some(k as u32));
        }
        // Past the covered range, a bounded discrete log finds it and the table grows.
        let past = mul_by_g(g.pow(10_000));
        assert_eq!(g.log(past), Some(10_001));
        assert_eq!(g.pow(10_001), past);
        assert_eq!(g.log(F64::ZERO), None);
    }

    /// An announced exponent at or past the bound is refused, so a return target past `MAX_CELLS`
    /// never reads as an address.
    #[test]
    fn log_below_refuses_exponents_past_its_bound() {
        let mut g = GPow::new(200);
        g.note(100);
        assert_eq!(g.log_below(g.pow(100), 100), None);
        assert_eq!(g.log_below(g.pow(100), 101), Some(100));
        assert_eq!(g.log(F64::G.pow(MAX_CELLS as u128 + 5)), None);
    }
}
