//! Runtime hint machinery shared by the interpreter and the compiler: the
//! resolved hint ops a [`super::Program`] carries ([`RHint`]), and the g-power
//! table + reverse index the hint interpreter grows on demand.

use primitives::field::{F64, div_by_g, mul_by_g};
use std::collections::HashMap;

/// Frame-relative offset operand (matches the compiler's `ir::Off`).
pub type Off = u32;

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
    index: HashMap<u64, u32>,
    /// The same for every multiple `k` of `STRIDE` that `pow` covers.
    coarse: HashMap<u64, u32>,
}

/// Spacing of the coarse index, and so the most divisions a missed lookup costs.
const STRIDE: usize = 64;

impl GPow {
    /// Seeded with `g^0 = 1`, grown to cover index `upto`, nothing announced.
    pub fn new(upto: usize) -> Self {
        let mut g = Self {
            pow: vec![F64::ONE],
            index: HashMap::new(),
            coarse: HashMap::from([(F64::ONE.0, 0)]),
        };
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

    /// `g^k`. Panics past the grown range, which is the honest outcome: every
    /// index the interpreter reads has been covered by a [`Self::grow_to`].
    pub fn pow(&self, k: usize) -> F64 {
        self.pow[k]
    }

    /// The forward table, `g^0` to `g^{covered - 1}`.
    pub(crate) fn into_powers(self) -> Vec<F64> {
        self.pow
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

    /// The exponent of `x` if announced: any covered one, for a table built by [`Self::dense`].
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

/// Where a computed-advice bit buffer lives. Frame cells are ordinary memory, so
/// a run of them serves as well as a heap region and costs no `DEREF` to index at
/// a compile-time offset; the heap form stays for a buffer indexed at run time.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum BitsDest {
    /// Frame cells `fp+base+k`.
    Stack(Off),
    /// Heap cells `m[fp+ptr]·g^k`, the pointer read at run time.
    Heap(Off),
}

/// A hint resolved to concrete offsets/sizes, keyed by global program counter.
#[derive(Clone, Debug)]
pub enum RHint {
    /// Announce a pointer into a reserved run of frames.
    FrameAddress { offset: Off },
    /// Reserve `log_g(m[end] * start_inverse)` consecutive frames of `size` cells,
    /// then the `tail` cells the final, untaken call writes of one more.
    AllocFrames {
        ptr: Off,
        size: u32,
        end: Off,
        start_inverse: F64,
        tail: u32,
    },
    /// Allocate a fresh region of `size` cells and write `g^{base}` to the cell.
    Alloc { ptr: Off, size: u32 },
    /// `Alloc` with the cell count read at runtime as the g-power exponent of
    /// `m[fp+size]`.
    AllocDyn { ptr: Off, size: Off },
    /// Pop stream `name`'s next entry (`len` values) into frame cells `fp+base+k`.
    WitnessStack { name: String, base: Off, len: u32 },
    /// Pop stream `name`'s next entry (`len` values) into heap cells `m[fp+ptr]·g^{lo+k}`.
    WitnessHeap { name: String, ptr: Off, lo: u32, len: u32 },
    /// Write `g^max(log2_ceil(value), floor)` into `fp+dst`, where `value` is the
    /// integer reconstructed from the `nbits` bits at `bits`.
    Log2Ceil {
        bits: BitsDest,
        dst: Off,
        nbits: u32,
        floor: u32,
    },
    /// Write the low `nbits` bits of `m[fp+value]` into `bits`.
    BitDecompose { value: Off, bits: BitsDest, nbits: u32 },
    /// Write the `nbits` bits of `n`, where `m[fp+value] = g^n` (a bounded
    /// discrete log at witness generation), into `bits`.
    BitDecomposeExp { value: Off, bits: BitsDest, nbits: u32 },
    /// Write `g^d_j` for the `ndigits` base-`2^digit_bits` digits `d_j` of `n >> s` into
    /// `dst`, where `m[fp+value] = g^n` with `n < 2^nbits` and `s` is `start` or, given
    /// `start_cell`, the exponent of `m[fp+start_cell]`.
    DigitDecomposeExp {
        value: Off,
        dst: BitsDest,
        nbits: u32,
        ndigits: u32,
        digit_bits: u32,
        start: u32,
        start_cell: Option<Off>,
    },
    /// Write `count` windows of `width` bits of `m[fp+value]`, from bit `start` on, into
    /// `dest` from cell `at` on, as g-powers: window `i` is `g^n` for `n` its bits read as an integer.
    WindowsExp {
        value: Off,
        dest: BitsDest,
        at: u32,
        start: u32,
        width: u32,
        count: u32,
    },
    /// Write the first `len` K-coordinate limbs of `m[fp+value]` to
    /// `m[fp+base..]`. Computed advice; callers constrain the result.
    FieldLimbs { value: Off, base: Off, len: u32 },
    /// Write `m[fp+value]⁻¹` to `m[fp+dst]`, or `0` when the value is zero.
    /// Untrusted: `assert a != b` multiplies the two back together and asserts
    /// `1`, which a zero value cannot satisfy (`FnLower::lower_assert_ne`).
    Inverse { value: Off, dst: Off },
    /// Prover-side debug print (`print(...)` in the zkDSL): display the value
    /// of `m[fp+cell]` at this program point. Witness generation only.
    Print { label: String, cell: Off },
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
