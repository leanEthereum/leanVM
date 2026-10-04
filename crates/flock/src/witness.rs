// CREDIT: https://github.com/succinctlabs/flock (flock-prover), MIT OR Apache-2.0.
//! Bit-packing and R1CS-row helpers for the monolithic hash R1CS modules
//! (only `hash` in this vendored subset).

use primitives::bits::bit_transpose_64bytes;
use primitives::stream::Stream;

/// OR the low 32 bits of `val` into `buf` starting at bit-offset `bit_off`.
/// Handles u64 straddling when `bit_off % 64 > 32`.
#[inline(always)]
pub(crate) const fn or_u32_at_bit(buf: &mut [u64], bit_off: usize, val: u32) {
    let u64_idx = bit_off >> 6;
    let shift = bit_off & 63;
    buf[u64_idx] |= (val as u64) << shift;
    if shift > 32 {
        buf[u64_idx + 1] |= (val as u64) >> (64 - shift);
    }
}

/// Set bit `bit_off` of `buf` (low-bit-first within each u64).
#[inline(always)]
pub(crate) const fn or_bit_at(buf: &mut [u64], bit_off: usize) {
    buf[bit_off >> 6] |= 1u64 << (bit_off & 63);
}

/// A `64·NW`-bit record composed in registers and flushed into the block once.
pub(crate) struct BitRecord<const NW: usize> {
    w: [u64; NW],
}

impl<const NW: usize> BitRecord<NW> {
    #[inline(always)]
    pub(crate) const fn new() -> Self {
        Self { w: [0u64; NW] }
    }

    /// OR a (pre-masked) value into record bits `[POS, POS + width)`.
    /// `POS` is const so the straddle branch and shifts fold at compile time.
    #[inline(always)]
    pub(crate) const fn push<const POS: usize>(&mut self, val: u32) {
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
pub(crate) const fn add_carry_parts(x: u32, y: u32) -> (u32, u32, u32, u32) {
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
pub(crate) const fn add3_fused_parts(x: u32, y: u32, z: u32) -> (u32, (u32, u32, u32), (u32, u32, u32)) {
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
pub(crate) const fn write_lin_word_ab_packed(bit_off: usize, val: u32, z: &mut [u64], a: &mut [u64], b: &mut [u64]) {
    or_u32_at_bit(z, bit_off, val);
    or_u32_at_bit(a, bit_off, val);
    or_u32_at_bit(b, bit_off, 0xFFFF_FFFF);
}

/// of the `u64` words on a little-endian target.
pub(crate) const fn packed_bytes(words: &[u64]) -> &[u8] {
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

/// One group's share of the four witness tables, in its worker's scratch.
pub(crate) struct GroupTables<'a> {
    /// `z`, `A·z` and `B·z`: `2^k_log / 64` packed words per instance, instance-major.
    pub z: &'a mut [u64],
    pub a: &'a mut [u64],
    pub b: &'a mut [u64],
    /// Lincheck's byte stripes: `2^k_log` bytes per 8 instances.
    pub stripes: &'a mut [u8],
}

/// The four witness tables of `2^n_blocks_log` instances, built `group` instances at a time.
///
/// - The fill closure writes every word and byte of the group starting at the instance it is given.
/// - Each worker keeps one scratch state, built once and reused across its groups.
///
/// A group builds in its worker's buffers, which stay in cache, then streams out.
///
/// Building in place instead would fetch every output line before writing it.
pub(crate) fn drive_witness_groups<St, I, F>(
    n_blocks_log: usize,
    k_log: usize,
    group: usize,
    init: I,
    fill: F,
) -> (Vec<u64>, Vec<u64>, Vec<u64>, Vec<u8>)
where
    St: Send,
    I: Fn() -> St + Sync,
    F: Fn(&mut St, usize, GroupTables<'_>) + Sync,
{
    let k = 1usize << k_log;
    let n_total = 1usize << n_blocks_log;
    assert!(
        n_total >= 8 && n_total.is_multiple_of(8),
        "lincheck stripe layout requires n_total ≥ 8 and divisible by 8"
    );
    assert!(
        group.is_multiple_of(8) && n_total.is_multiple_of(group),
        "a group of {group} instances must tile 2^{n_blocks_log} in whole stripes"
    );

    let total_words = n_total * (k / 64);
    // SAFETY: group `g` publishes chunk `g` of every table in full below, and the chunk counts match.
    let (mut z, mut a, mut b, mut z_lincheck) = unsafe {
        (
            primitives::uninit_vec::<u64>(total_words),
            primitives::uninit_vec::<u64>(total_words),
            primitives::uninit_vec::<u64>(total_words),
            primitives::uninit_vec::<u8>((n_total / 8) * k),
        )
    };

    // A group's share: its packed words in each table, and one stripe per 8 instances.
    let group_words = group * (k / 64);
    let group_bytes = (group / 8) * k;
    let z_chunks = parallel::Chunks::new(&mut z, group_words);
    let a_chunks = parallel::Chunks::new(&mut a, group_words);
    let b_chunks = parallel::Chunks::new(&mut b, group_words);
    let stripe_chunks = parallel::Chunks::new(&mut z_lincheck, group_bytes);
    debug_assert_eq!(z_chunks.count(), stripe_chunks.count());

    parallel::map_reduce_with_state(
        z_chunks.count(),
        || (vec![0u64; 3 * group_words], vec![0u8; group_bytes], init()),
        || (),
        |(scratch, stripes, state), (), g| {
            // Build the group in the worker's buffers.
            let (z_grp, rest) = scratch.split_at_mut(group_words);
            let (a_grp, b_grp) = rest.split_at_mut(group_words);
            fill(
                state,
                g * group,
                GroupTables {
                    z: z_grp,
                    a: a_grp,
                    b: b_grp,
                    stripes,
                },
            );

            let stream = Stream::new();
            // SAFETY: each group `g` takes chunk `g` of each table exactly once, and
            // all four tables stay borrowed for the whole dispatch.
            unsafe {
                stream.copy(z_chunks.get(g), z_grp);
                stream.copy(a_chunks.get(g), a_grp);
                stream.copy(b_chunks.get(g), b_grp);
                stream.copy(stripe_chunks.get(g), stripes);
            }
        },
        |(), ()| (),
    );

    (z, a, b, z_lincheck)
}

/// Drive the parallel chunked witness build for `n_blocks` instances padded
/// to `2^n_blocks_log` slots, one instance at a time. Returns `(z, a, b, z_lincheck)`:
/// the three bit-packed `u64` tables (`K / 64` words per instance) and the lincheck
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
) -> (Vec<u64>, Vec<u64>, Vec<u64>, Vec<u8>)
where
    F: Fn(&S, &mut [u64], &mut [u64], &mut [u64]) + Sync,
{
    let u64_per_block = (1usize << k_log) / 64;
    let n_blocks = initial_states.len();
    assert!(
        n_blocks <= 1 << n_blocks_log,
        "{n_blocks} blocks > 2^{n_blocks_log} slots"
    );

    // Eight blocks per group, the lincheck stripe of one group being their bit transpose.
    drive_witness_groups(
        n_blocks_log,
        k_log,
        8,
        || (),
        |(), first, t| {
            // A block only sets bits, so it starts from zero.
            t.z.fill(0);
            t.a.fill(0);
            t.b.fill(0);
            for k_in in 0..8 {
                let init: &S = match (initial_states.get(first + k_in), padding) {
                    (Some(state), _) => state,
                    // Fill the padding slot with a real block so its constant
                    // wire is set (see `padding` docs above).
                    (None, Some(p)) => p,
                    // No padding block, leave this slot zero.
                    (None, None) => continue,
                };
                let range = k_in * u64_per_block..(k_in + 1) * u64_per_block;
                per_block(init, &mut t.z[range.clone()], &mut t.a[range.clone()], &mut t.b[range]);
            }

            // Bit-transpose 8 z chunks into the lincheck stripe.
            for (i, out) in t.stripes.as_chunks_mut::<64>().0.iter_mut().enumerate() {
                let rows: [[u8; 8]; 8] = std::array::from_fn(|l| t.z[l * u64_per_block + i].to_le_bytes());
                bit_transpose_64bytes(rows.as_flattened().try_into().expect("64 bytes"), out);
            }
        },
    )
}

/// Build native witnesses eight instances at a time, then pack their byte stripe.
pub(crate) fn drive_witness_batched<S: Sync>(
    rows: &[S],
    padding: &S,
    n_blocks_log: usize,
    k_log: usize,
    batch: impl Fn([&S; 8], &mut [u64], &mut [u64], &mut [u64]) + Sync,
) -> (Vec<u64>, Vec<u64>, Vec<u64>, Vec<u8>) {
    assert!(rows.len() <= 1 << n_blocks_log, "more rows than instances");
    let words = (1usize << k_log) / 64;
    drive_witness_groups(
        n_blocks_log,
        k_log,
        8,
        || (),
        |(), first, t| {
            // The callback ORs product runs into a fresh group of eight instances.
            t.z.fill(0);
            t.a.fill(0);
            t.b.fill(0);
            let inputs = std::array::from_fn(|l| rows.get(first + l).unwrap_or(padding));
            batch(inputs, t.z, t.a, t.b);

            // Each output stripe carries one witness bit from each of the eight instances.
            for (i, out) in t.stripes.as_chunks_mut::<64>().0.iter_mut().enumerate() {
                let bits: [[u8; 8]; 8] = std::array::from_fn(|l| t.z[l * words + i].to_le_bytes());
                bit_transpose_64bytes(bits.as_flattened().try_into().expect("eight word lanes"), out);
            }
        },
    )
}
