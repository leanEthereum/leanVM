//! Runtime hint machinery shared by the interpreter and the compiler: the
//! resolved hint ops a [`super::Program`] carries ([`RHint`]), and the g-power
//! table + reverse index the hint interpreter grows on demand.

use primitives::field::{F64, mul_by_g};

/// Frame-relative offset operand (matches the compiler's `ir::Off`).
pub type Off = u32;

/// Cells a program can address: [`GPow`] covers no more.
pub(crate) const MAX_CELLS: u32 = 1 << 28;

/// The `g^k` table paired with a reverse index `g^k ↦ k`, both grown on demand
/// (recursion depth, and so the address range, is unbounded).
///
/// The interpreter needs both directions: a cell index becomes the address `g^k`,
/// and a pointer word read back out of memory must be inverted to the index it
/// addresses. Three things keep this cheap.
///
/// A reverse-index slot holds the key beside its exponent, so a probe reads the
/// slot alone: confirming a candidate against the forward table, as large as the
/// address space, would cost a cache miss per probe. Keys are field elements,
/// hence effectively uniform, which is all the placement asks for: one
/// multiplicative mix, then linear probing. The table stays at most half full to
/// keep probing short.
///
/// It indexes only the exponents [`Self::note`] announces, or a lookup resolved:
/// a run addresses millions of cells but stores only the few thousand bases of
/// its frames and buffers, and one random write per addressable cell into a table
/// far too large for cache is what building the whole inverse costs.
///
/// A lookup that misses divides the address by `g` until it meets a coarse index
/// of every `STRIDE`th exponent, then announces the result, so an address the
/// interpreter could not label, a jump target or a pointer into a buffer, costs at
/// most `STRIDE` probes once.
pub struct GPow {
    pow: Vec<F64>,
    /// The announced exponents.
    index: Index,
    /// Every multiple of `STRIDE` that `pow` covers.
    coarse: Index,
}

/// Spacing of the coarse index, and so the most probes a missed lookup costs.
const STRIDE: usize = 64;

/// Exponents by their g-power, open-addressed. A zero key marks an empty slot: no
/// g-power is zero.
///
/// Bit `t` of `tags[s]` is set when a key mixing to home slot `s` and tag `t`, three
/// more bits of its mix, is in. A lookup of an absent key almost always misses its
/// tag and reads no slot, which is what a [`GPow::log`] that resolves does on all
/// but one of its probes: the tags are a sixteenth of the slots' size, so they stay
/// in cache where the slots do not.
struct Index {
    slots: Vec<(u64, u32)>,
    tags: Vec<u8>,
    len: usize,
}

impl Index {
    fn new(slots: usize) -> Self {
        Self {
            slots: vec![(0, 0); slots],
            tags: vec![0; slots],
            len: 0,
        }
    }

    /// The home slot of `key` and its tag bit.
    #[inline(always)]
    fn home(&self, key: u64) -> (usize, u8) {
        // Bits 32..64 of the mix are the well-distributed ones.
        let mix = (key.wrapping_mul(0x9E37_79B9_7F4A_7C15) >> 32) as usize;
        let slots = self.slots.len();
        (mix & (slots - 1), 1 << ((mix >> slots.trailing_zeros()) & 7))
    }

    #[inline]
    fn find(&self, x: F64) -> Option<u32> {
        let (mut i, tag) = self.home(x.0);
        if self.tags[i] & tag == 0 {
            return None;
        }
        let mask = self.slots.len() - 1;
        loop {
            let (key, k) = self.slots[i];
            if key == 0 {
                return None;
            }
            if key == x.0 {
                return Some(k);
            }
            i = (i + 1) & mask;
        }
    }

    /// Add `x = g^k`, which is not in the index yet.
    fn insert(&mut self, x: F64, k: usize) {
        self.reserve(self.len + 1);
        self.place(x.0, k as u32);
        self.len += 1;
    }

    /// Make room for `n` entries, staying at most half full.
    fn reserve(&mut self, n: usize) {
        if 2 * n > self.slots.len() {
            let slots = (2 * n).next_power_of_two();
            self.tags = vec![0; slots];
            for (key, k) in std::mem::replace(&mut self.slots, vec![(0, 0); slots]) {
                if key != 0 {
                    self.place(key, k);
                }
            }
        }
    }

    fn place(&mut self, key: u64, k: u32) {
        let (mut i, tag) = self.home(key);
        self.tags[i] |= tag;
        let mask = self.slots.len() - 1;
        while self.slots[i].0 != 0 {
            i = (i + 1) & mask;
        }
        self.slots[i] = (key, k);
    }
}

impl GPow {
    /// Seeded with `g^0 = 1`, grown to cover index `upto`, nothing announced.
    pub fn new(upto: usize) -> Self {
        let mut g = Self {
            pow: vec![F64::ONE],
            index: Index::new(1 << 13),
            coarse: Index::new(1 << 4),
        };
        g.coarse.insert(F64::ONE, 0);
        g.extend(upto);
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
    #[inline(always)]
    pub fn pow(&self, k: usize) -> F64 {
        self.pow[k]
    }

    /// The forward table, `g^0` to `g^{covered - 1}`.
    pub(crate) fn into_powers(self) -> Vec<F64> {
        self.pow
    }

    /// Extend the forward table to cover index `upto`.
    #[inline]
    pub fn grow_to(&mut self, upto: usize) {
        if upto >= self.pow.len() {
            self.extend(upto);
        }
    }

    #[cold]
    fn extend(&mut self, upto: usize) {
        assert!(upto < MAX_CELLS as usize, "address space overflow (program too large)");
        // At least double, and a quarter more than a large jump asks: the small
        // extends that follow fill spare capacity instead of copying the table.
        let n = self.pow.len();
        if upto >= self.pow.capacity() {
            let target = (2 * self.pow.capacity())
                .max(upto + 1 + (upto + 1) / 4)
                .min(MAX_CELLS as usize);
            self.pow.reserve_exact(target - n);
        }
        // ×g is ×x = `mul_by_g` (shift+fold), not a PMULL.
        let mut p = *self.pow.last().unwrap();
        self.pow.extend((n..=upto).map(|_| {
            p = mul_by_g(p);
            p
        }));
        let to = self.pow.len().div_ceil(STRIDE);
        self.coarse.reserve(to);
        for j in n.div_ceil(STRIDE)..to {
            self.coarse.insert(self.pow[j * STRIDE], j * STRIDE);
        }
    }

    /// Announce that `g^k` may come back for inversion, because the interpreter
    /// is about to store it in memory as an address. Covers `k` first. Idempotent.
    pub fn note(&mut self, k: usize) {
        self.grow_to(k);
        let x = self.pow[k];
        if self.index.find(x).is_none() {
            self.index.insert(x, k);
        }
    }

    /// The discrete log of `x`, if it is a covered g-power.
    #[inline]
    pub fn log(&mut self, x: F64) -> Option<u32> {
        self.lookup(x).or_else(|| self.resolve(x))
    }

    /// The exponent of `x` if announced: any covered one, for a table built by [`Self::dense`].
    #[inline]
    pub(crate) fn lookup(&self, x: F64) -> Option<u32> {
        self.index.find(x)
    }

    /// `log` for an address that is not announced: divide by `g` down to a
    /// multiple of `STRIDE`, then announce the exponent.
    #[cold]
    fn resolve(&mut self, x: F64) -> Option<u32> {
        let mut y = x;
        for j in 0..STRIDE {
            if let Some(k) = self.coarse.find(y) {
                let k = k as usize + j;
                return (k < self.pow.len()).then(|| {
                    self.note(k);
                    k as u32
                });
            }
            y = div_by_g(y);
        }
        None
    }
}

/// The inverse of [`mul_by_g`]: bit 0 of its output says whether it folded.
#[inline(always)]
fn div_by_g(a: F64) -> F64 {
    F64(if a.0 & 1 == 1 {
        (a.0 ^ 0x1B) >> 1 | 1 << 63
    } else {
        a.0 >> 1
    })
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
        assert_eq!(g.log(mul_by_g(g.pow(10_000))), None);
    }
}
