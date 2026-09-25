// CREDIT: https://github.com/succinctlabs/flock (flock-prover), MIT OR Apache-2.0.
//! Bit-packing and R1CS-row helpers for the monolithic hash R1CS modules
//! (only `hash` in this vendored subset).

use primitives::bits::transpose_8_u64s_to_64_bytes;
use zk_alloc::ArenaVec;

/// OR the low 32 bits of `val` into `buf` starting at bit-offset `bit_off`.
/// Handles u64 straddling when `bit_off % 64 > 32`.
#[inline(always)]
pub(crate) fn or_u32_at_bit(buf: &mut [u64], bit_off: usize, val: u32) {
    let u64_idx = bit_off >> 6;
    let shift = bit_off & 63;
    buf[u64_idx] |= (val as u64) << shift;
    if shift > 32 {
        buf[u64_idx + 1] |= (val as u64) >> (64 - shift);
    }
}

/// Set bit `bit_off` of `buf` (low-bit-first within each u64).
#[inline(always)]
pub(crate) fn or_bit_at(buf: &mut [u64], bit_off: usize) {
    buf[bit_off >> 6] |= 1u64 << (bit_off & 63);
}

/// A `64·NW`-bit record composed in registers and flushed into the block once.
pub(crate) struct BitRecord<const NW: usize> {
    w: [u64; NW],
}

impl<const NW: usize> BitRecord<NW> {
    #[inline(always)]
    pub(crate) fn new() -> Self {
        Self { w: [0u64; NW] }
    }

    /// OR a (pre-masked) value into record bits `[POS, POS + width)`.
    /// `POS` is const so the straddle branch and shifts fold at compile time.
    #[inline(always)]
    pub(crate) fn push<const POS: usize>(&mut self, val: u32) {
        let v = val as u64;
        let idx = POS >> 6;
        let s = POS & 63;
        self.w[idx] |= v << s;
        if s > 32 {
            self.w[idx + 1] |= v >> (64 - s);
        }
    }

    /// OR the record into `buf` starting at bit `base_bit`.
    #[inline(always)]
    pub(crate) fn flush(&self, buf: &mut [u64], base_bit: usize) {
        let bi = base_bit >> 6;
        let s = base_bit & 63;
        let mut spill = 0u64;
        for j in 0..NW {
            buf[bi + j] |= (self.w[j] << s) | spill;
            // `(x >> 1) >> (63 - s)` = `x >> (64 - s)` without the s = 0 UB.
            spill = (self.w[j] >> 1) >> (63 - s);
        }
        buf[bi + NW] |= spill;
    }
}

/// One 32-bit ADD's witness parts: `(sum, left, right, carry_aux)` with
/// `left/right/carry_aux` masked to the low 31 bits (bit 31 is the discarded
/// mod-2³² carry-out; the carry slot is 31 bits wide).
#[inline(always)]
pub(crate) fn add_carry_parts(x: u32, y: u32) -> (u32, u32, u32, u32) {
    let sum = x.wrapping_add(y);
    let cin = sum ^ x ^ y;
    const MASK_LO31: u32 = 0x7FFF_FFFF;
    let left = (x ^ cin) & MASK_LO31;
    let right = (y ^ cin) & MASK_LO31;
    let carry_aux = left & right;
    (sum, left, right, carry_aux)
}

/// One fused three-operand ADD's witness parts (see
/// `gf2::walk_add3_fused` for the row algebra): the sum, then each
/// layer's `(left, right, product)` triple.
///
/// The majority triple is masked to bits 0..=30. The ripple triple is masked
/// to bits 1..=30 **and shifted down by one**, so its slot `j` holds bit
/// `j + 1`, matching the 30-slot ripple run.
#[inline(always)]
pub(crate) fn add3_fused_parts(x: u32, y: u32, z: u32) -> (u32, (u32, u32, u32), (u32, u32, u32)) {
    const MASK_LO31: u32 = 0x7FFF_FFFF;
    const MASK_LO30: u32 = 0x3FFF_FFFF;
    let maj_left = (x ^ z) & MASK_LO31;
    let maj_right = (y ^ z) & MASK_LO31;
    let maj_aux = maj_left & maj_right;
    // p + 2·maj, where maj[i] = maj_aux[i] ⊕ z[i] is the bitwise majority.
    let p = x ^ y ^ z;
    let q = (maj_aux ^ (z & MASK_LO31)) << 1;
    let sum = p.wrapping_add(q);
    let cin = sum ^ p ^ q;
    let rip_left = ((p ^ cin) >> 1) & MASK_LO30;
    let rip_right = ((q ^ cin) >> 1) & MASK_LO30;
    let rip_aux = rip_left & rip_right;
    (sum, (maj_left, maj_right, maj_aux), (rip_left, rip_right, rip_aux))
}

/// Write a 32-bit lin-id (or input) slot: (z, a) = val, b = all-ones.
/// **c is not written**: since `C = I`, `c == z` byte-for-byte.
#[inline]
pub(crate) fn write_lin_word_ab_packed(bit_off: usize, val: u32, z: &mut [u64], a: &mut [u64], b: &mut [u64]) {
    or_u32_at_bit(z, bit_off, val);
    or_u32_at_bit(a, bit_off, val);
    or_u32_at_bit(b, bit_off, 0xFFFF_FFFF);
}

/// of the `u64` words on a little-endian target.
pub(crate) fn packed_bytes(words: &[u64]) -> &[u8] {
    const _: () = assert!(
        cfg!(target_endian = "little"),
        "packed witness bytes assume little-endian"
    );
    // SAFETY: `u64` has no padding or invalid bit patterns, and `u8`'s
    // alignment divides `u64`'s, so the words are a valid `8 · len` byte slice.
    unsafe { core::slice::from_raw_parts(words.as_ptr().cast::<u8>(), words.len() * 8) }
}

// ---------------------------------------------------------------------------
// Generic witness packing driver.
// ---------------------------------------------------------------------------

/// Drive the parallel chunked witness build for `n_blocks` instances padded
/// to `2^n_blocks_log` slots. Returns `(z, a, b, z_lincheck)`: the three
/// bit-packed `u64` tables (`K / 64` words per instance) and the lincheck
/// byte stripe.
///
/// `per_block(initial, z_u64, a_u64, b_u64)` populates one block's worth of
/// `(z, a, b)` data: 3 zero-initialized `u64`-buffers of length `K / 64`.
/// `K` is derived from `k_log`. `initial_states.len()` may be less than
/// `2^n_blocks_log`.
///
/// `padding` controls what fills the trailing `2^n_blocks_log −
/// initial_states.len()` slots:
/// - `None`: leave them all-zero (trivial constraint satisfaction).
/// - `Some(p)`: build a real block from `p` in every padding slot. Encoders
///   that pin a constant wire need this so the constant column is all-ones
///   across *every* batched instance (see `lincheck's `LincheckCircuit::const_pin_col``).
pub(crate) fn drive_witness_packed_and_lincheck<S: Sync, F>(
    initial_states: &[S],
    padding: Option<&S>,
    n_blocks_log: usize,
    k_log: usize,
    per_block: F,
) -> (ArenaVec<u64>, ArenaVec<u64>, ArenaVec<u64>, ArenaVec<u8>)
where
    F: Fn(&S, &mut [u64], &mut [u64], &mut [u64]) + Sync,
{
    let k = 1usize << k_log;
    let u64_per_block = k / 64;
    let n_total = 1usize << n_blocks_log;
    let n_blocks = initial_states.len();
    assert!(
        n_blocks <= n_total,
        "{n_blocks} blocks > 2^{n_blocks_log} = {n_total} slots"
    );
    assert!(
        n_total >= 8 && n_total.is_multiple_of(8),
        "lincheck stripe layout requires n_total ≥ 8 and divisible by 8"
    );

    let total_words = n_total * u64_per_block;
    // Zero inside the parallel loop because the builders OR bits into each group.
    // SAFETY (x3): the parallel loop below writes every element of z/a/b before
    // any is read: each group memsets its own slice, then ORs bits into it.
    let mut z = unsafe { ArenaVec::<u64>::uninitialized(total_words) };
    let mut a = unsafe { ArenaVec::<u64>::uninitialized(total_words) };
    let mut b = unsafe { ArenaVec::<u64>::uninitialized(total_words) };
    // SAFETY: group `g` writes chunk `g` of the stripe table in full, since the
    // transpose stores all 64 bytes of each of the `u64_per_block` destination
    // windows and `u64_per_block * 64 == k == stripe.len()`. The chunk counts
    // match, so every chunk is claimed by exactly one group.
    let mut z_lincheck = unsafe { ArenaVec::<u8>::uninitialized((n_total / 8) * k) };

    // Four output tables at two widths, indexed by the same group: `z`/`a`/`b`
    // take eight blocks' packed words, `z_lincheck` takes one byte stripe.
    let z_chunks = parallel::Chunks::new(&mut z, 8 * u64_per_block);
    let a_chunks = parallel::Chunks::new(&mut a, 8 * u64_per_block);
    let b_chunks = parallel::Chunks::new(&mut b, 8 * u64_per_block);
    let stripe_chunks = parallel::Chunks::new(&mut z_lincheck, k);
    debug_assert_eq!(z_chunks.count(), stripe_chunks.count());
    parallel::for_each(z_chunks.count(), |g| {
        // SAFETY: each group `g` takes chunk `g` of each table exactly once, and
        // all four tables stay borrowed for the whole dispatch.
        let (z_grp, a_grp, b_grp, stripe) =
            unsafe { (z_chunks.get(g), a_chunks.get(g), b_chunks.get(g), stripe_chunks.get(g)) };
        z_grp.fill(0);
        a_grp.fill(0);
        b_grp.fill(0);
        for k_in in 0..8 {
            let global_idx = 8 * g + k_in;
            let init: &S = if global_idx < n_blocks {
                &initial_states[global_idx]
            } else if let Some(p) = padding {
                // Fill the padding slot with a real block so its constant
                // wire is set (see `padding` docs above).
                p
            } else {
                // No padding block, leave this slot zero.
                continue;
            };
            let range = k_in * u64_per_block..(k_in + 1) * u64_per_block;
            let z_u64 = &mut z_grp[range.clone()];
            let a_u64 = &mut a_grp[range.clone()];
            let b_u64 = &mut b_grp[range];
            per_block(init, z_u64, a_u64, b_u64);
        }

        // Bit-transpose 8 z chunks into the lincheck stripe.
        for i in 0..u64_per_block {
            let lanes: [u64; 8] = [
                z_grp[i],
                z_grp[u64_per_block + i],
                z_grp[2 * u64_per_block + i],
                z_grp[3 * u64_per_block + i],
                z_grp[4 * u64_per_block + i],
                z_grp[5 * u64_per_block + i],
                z_grp[6 * u64_per_block + i],
                z_grp[7 * u64_per_block + i],
            ];
            transpose_8_u64s_to_64_bytes(&lanes, &mut stripe[i * 64..i * 64 + 64]);
        }
    });

    (z, a, b, z_lincheck)
}
