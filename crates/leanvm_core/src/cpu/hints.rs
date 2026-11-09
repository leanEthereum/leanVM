//! Runtime hint machinery shared by the interpreter and the compiler: the
//! resolved hint ops a [`super::Program`] carries ([`RHint`]), and the g-power
//! table + reverse index the hint interpreter grows on demand.

use primitives::field::{F64, div_by_g, mul_by_g};

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
/// The reverse index holds nothing but the exponent, confirming a candidate slot
/// against the forward table, so a slot is four bytes where a `HashMap` bucket is
/// sixteen plus a control byte. Keys are field elements, hence effectively
/// uniform, which is all the placement asks for: one multiplicative mix, then
/// linear probing. The table stays at most half full to keep probing short.
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
    /// `k + 1` at the slot `g^k` mixes to, for the announced `k`; 0 marks an empty
    /// slot. Power-of-two length.
    index: Vec<u32>,
    announced: usize,
    /// The same for every multiple `k` of `STRIDE` that `pow` covers.
    coarse: Vec<u32>,
}

/// Spacing of the coarse index, and so the most probes a missed lookup costs.
const STRIDE: usize = 64;

impl GPow {
    /// Seeded with `g^0 = 1`, grown to cover index `upto`, nothing announced.
    pub fn new(upto: usize) -> Self {
        let mut g = Self {
            pow: vec![F64::ONE],
            index: vec![0; 1 << 13],
            announced: 0,
            coarse: Vec::new(),
        };
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
        let (mut from, to) = (n.div_ceil(STRIDE), self.pow.len().div_ceil(STRIDE));
        if 2 * to > self.coarse.len() {
            self.coarse = vec![0; (2 * to).next_power_of_two()];
            from = 0;
        }
        for j in from..to {
            insert(&mut self.coarse, self.pow[j * STRIDE], j * STRIDE);
        }
    }

    /// Announce that `g^k` may come back for inversion, because the interpreter
    /// is about to store it in memory as an address. Covers `k` first. Idempotent.
    pub fn note(&mut self, k: usize) {
        self.grow_to(k);
        if find(&self.index, &self.pow, self.pow[k]).is_some() {
            return;
        }
        if 2 * (self.announced + 1) > self.index.len() {
            let wider = vec![0; 2 * self.index.len()];
            let old = std::mem::replace(&mut self.index, wider);
            for e in old.into_iter().filter(|&e| e != 0) {
                insert(&mut self.index, self.pow[e as usize - 1], e as usize - 1);
            }
        }
        insert(&mut self.index, self.pow[k], k);
        self.announced += 1;
    }

    /// The discrete log of `x`, if it is a covered g-power.
    #[inline]
    pub fn log(&mut self, x: F64) -> Option<u32> {
        self.lookup(x).or_else(|| self.resolve(x))
    }

    /// The exponent of `x` if announced: any covered one, for a table built by [`Self::dense`].
    #[inline]
    pub(crate) fn lookup(&self, x: F64) -> Option<u32> {
        find(&self.index, &self.pow, x)
    }

    /// `log` for an address that is not announced: divide by `g` down to a
    /// multiple of `STRIDE`, then announce the exponent.
    #[cold]
    fn resolve(&mut self, x: F64) -> Option<u32> {
        let mut y = x;
        for j in 0..STRIDE {
            if let Some(k) = find(&self.coarse, &self.pow, y) {
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

/// The `k` of a slot of `table` that holds `x = pow[k]`.
#[inline]
fn find(table: &[u32], pow: &[F64], x: F64) -> Option<u32> {
    let mask = table.len() - 1;
    let mut i = slot_of(x.0, mask);
    while table[i] != 0 {
        let k = table[i] - 1;
        if pow[k as usize] == x {
            return Some(k);
        }
        i = (i + 1) & mask;
    }
    None
}

/// Put `k` in the first free slot of `table` from where `g^k = key` mixes to.
fn insert(table: &mut [u32], key: F64, k: usize) {
    let mask = table.len() - 1;
    let mut i = slot_of(key.0, mask);
    while table[i] != 0 {
        i = (i + 1) & mask;
    }
    table[i] = k as u32 + 1;
}

/// Bits 32..64 of the mix are the well-distributed ones; the mask keeps as many
/// of them as the table is wide.
#[inline(always)]
fn slot_of(key: u64, mask: usize) -> usize {
    (key.wrapping_mul(0x9E37_79B9_7F4A_7C15) >> 32) as usize & mask
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
