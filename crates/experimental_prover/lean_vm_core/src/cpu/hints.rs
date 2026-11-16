//! Runtime hint machinery: the resolved hint ops an [`isa::Program`] carries ([`RHint`], from the `isa` crate the
//! compiler shares), and the g-power table + reverse index the hint interpreter grows on demand.

use primitives::field::{F64, div_by_g, g_pow, mul_by_g};

pub use isa::{BitsDest, RHint};

/// The cells a provable run can address, which the [`GPow`] index covers: a memory of `2^29`
/// cells would overflow the `2^30` stack with its three columns, so no larger one can be committed.
pub(crate) const MAX_CELLS: u32 = 1 << (verifier::MAX_STACKED_LOG - 2);

/// The exponents the [`GPow`] table can cover: an address below [`MAX_CELLS`], or a `pc` (a return
/// target `pc + 2` too) of a bytecode a stack commits, below `2^30`.
pub(crate) const MAX_INDEX: usize = 1 << verifier::MAX_LOG_BYTECODE;

/// The powers `g^k` paired with a reverse index `g^k ↦ k`, both grown on demand
/// (recursion depth, and so the address range, is unbounded).
///
/// The interpreter needs both directions: a cell index becomes the address `g^k`,
/// and a pointer word read back out of memory must be inverted to the index it
/// addresses. Three things keep this cheap.
///
/// The forward table holds `g^(STRIDE·j)` and `g^0` to `g^(STRIDE - 1)`, so `g^k` is
/// one product: a table of every power would span the address space, built on the
/// interpreter's one thread (the trace fill builds its own, on the pool).
///
/// It indexes only the exponents [`Self::note`] announces, or a lookup resolved:
/// a run addresses millions of cells but stores only the few thousand bases of
/// its frames and buffers, and one random write per addressable cell into a table
/// far too large for cache is what building the whole inverse costs.
///
/// A lookup that misses divides the address by `g` until it meets a coarse index
/// of every `STRIDE`th exponent, then announces the result, so an address the
/// interpreter could not label, a jump target or a pointer into a buffer, costs at
/// most `STRIDE` probes once. One past the table, a hinted g-power or a range
/// check's complement, is found by `bounded_dlog` below the caller's bound, and the
/// table grows to cover it.
pub struct GPow {
    /// `g^(STRIDE·j)` for every multiple of `STRIDE` covered.
    strides: Vec<F64>,
    /// `g^0` to `g^(STRIDE - 1)`.
    first: [F64; STRIDE],
    /// The announced exponents.
    index: Index,
    /// Every multiple of `STRIDE` covered.
    coarse: Index,
}

/// Spacing of the coarse index and the forward strides, and so the most probes a missed lookup costs.
const STRIDE: usize = 64;

/// Exponents by their g-power: linear probing, at most half full. A slot holds its key, zero when
/// empty (no g-power is zero); keys are field elements, effectively uniform, so one multiplicative
/// mix places them.
///
/// Bit `t` of `tags[s]` is set once a key with home slot `s` and tag `t`, three more bits of its
/// mix, is in. So most lookups of an absent key, which `resolve` and `bounded_dlog` make many of,
/// read one byte, from a table that stays in cache where the slots do not.
struct Index {
    slots: Vec<(F64, u32)>,
    tags: Vec<u8>,
    len: usize,
}

impl Index {
    fn new() -> Self {
        Self {
            slots: vec![(F64::ZERO, 0); 16],
            tags: vec![0; 16],
            len: 0,
        }
    }

    /// The home slot of `x` and its tag bit.
    #[inline(always)]
    fn home(&self, x: F64) -> (usize, u8) {
        // Bits 32..64 of the mix are the well-distributed ones.
        let mix = (x.0.wrapping_mul(0x9E37_79B9_7F4A_7C15) >> 32) as usize;
        let slots = self.slots.len();
        (mix & (slots - 1), 1 << ((mix >> slots.trailing_zeros()) & 7))
    }

    #[inline]
    fn find(&self, x: F64) -> Option<u32> {
        let (mut i, tag) = self.home(x);
        if self.tags[i] & tag == 0 {
            return None;
        }
        loop {
            match self.slots[i] {
                (key, _) if key == F64::ZERO => return None,
                (key, k) if key == x => return Some(k),
                _ => i = (i + 1) & (self.slots.len() - 1),
            }
        }
    }

    /// Add `x = g^k`, which is not in the index yet.
    fn insert(&mut self, x: F64, k: u32) {
        if 2 * (self.len + 1) > self.slots.len() {
            let n = 2 * self.slots.len();
            let old = std::mem::replace(&mut self.slots, vec![(F64::ZERO, 0); n]);
            self.tags = vec![0; n];
            self.len = 0;
            for (x, k) in old.into_iter().filter(|&(x, _)| x != F64::ZERO) {
                self.insert(x, k);
            }
        }
        let (mut i, tag) = self.home(x);
        self.tags[i] |= tag;
        while self.slots[i].0 != F64::ZERO {
            i = (i + 1) & (self.slots.len() - 1);
        }
        self.slots[i] = (x, k);
        self.len += 1;
    }
}

impl GPow {
    /// Seeded with `g^0 = 1`, grown to cover index `upto`, nothing announced.
    pub fn new(upto: usize) -> Self {
        let mut g = Self {
            strides: vec![F64::ONE],
            first: std::array::from_fn(g_pow),
            index: Index::new(),
            coarse: Index::new(),
        };
        g.coarse.insert(F64::ONE, 0);
        g.grow_to(upto);
        g
    }

    /// [`Self::new`] with every exponent up to `upto` announced, so that
    /// [`Self::lookup`] alone finds any of them.
    pub(crate) fn dense(upto: usize) -> Self {
        let mut g = Self::new(upto);
        for k in 0..=upto {
            g.note(k);
        }
        g
    }

    /// `g^k`. Panics past the last stride covered, which is the honest outcome: every
    /// index the interpreter reads has been covered by a [`Self::grow_to`].
    #[inline(always)]
    pub fn pow(&self, k: usize) -> F64 {
        self.strides[k / STRIDE] * self.first[k % STRIDE]
    }

    /// Cover index `upto`.
    #[inline]
    pub fn grow_to(&mut self, upto: usize) {
        if upto / STRIDE >= self.strides.len() {
            self.extend(upto);
        }
    }

    #[cold]
    fn extend(&mut self, upto: usize) {
        assert!(upto < MAX_INDEX, "address space overflow (program too large)");
        let step = g_pow(STRIDE);
        for j in self.strides.len()..=upto / STRIDE {
            let p = self.strides[j - 1] * step;
            self.strides.push(p);
            self.coarse.insert(p, (j * STRIDE) as u32);
        }
    }

    /// Announce that `g^k` may come back for inversion, because the interpreter
    /// is about to store it in memory as an address. Covers `k` first. Idempotent.
    pub fn note(&mut self, k: usize) {
        self.grow_to(k);
        let x = self.pow(k);
        if self.index.find(x).is_none() {
            self.index.insert(x, k as u32);
        }
    }

    /// The discrete log of `x`, if it is a g-power below `MAX_CELLS`, covering it.
    #[inline]
    pub fn log(&mut self, x: F64) -> Option<u32> {
        self.log_below(x, MAX_CELLS as usize)
    }

    /// The discrete log of `x`, if it is a g-power below `bound` (at most `MAX_INDEX`), covering it.
    #[inline]
    pub(crate) fn log_below(&mut self, x: F64, bound: usize) -> Option<u32> {
        debug_assert!(bound <= MAX_INDEX);
        match self.lookup(x) {
            Some(k) => ((k as usize) < bound).then_some(k),
            None => self.log_miss(x, bound),
        }
    }

    /// `log_below` for an exponent not announced: the coarse index, else a bounded discrete
    /// log, then cover and announce it.
    #[cold]
    #[inline(never)]
    fn log_miss(&mut self, x: F64, bound: usize) -> Option<u32> {
        let k = self
            .resolve(x)
            .or_else(|| bounded_dlog(x, crate::log2_ceil_usize(bound) as u32).map(|k| k as usize))?;
        (k < bound).then(|| {
            self.note(k);
            k as u32
        })
    }

    /// The exponent of `x` if announced: any covered one, for a table built by [`Self::dense`].
    #[inline]
    pub(crate) fn lookup(&self, x: F64) -> Option<u32> {
        self.index.find(x)
    }

    /// The exponent of `x` if it is not announced: divide by `g` down to a multiple of
    /// `STRIDE`. Past the table by fewer than `STRIDE` too, so that a run of addresses
    /// climbing past the table stays off the discrete log.
    fn resolve(&self, x: F64) -> Option<usize> {
        let mut y = x;
        for j in 0..STRIDE {
            if let Some(k) = self.coarse.find(y) {
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
        let baby = GPow::dense((1usize << LOG_BABY) - 1);
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
