// CREDIT: https://github.com/succinctlabs/flock (flock-prover), MIT OR Apache-2.0.
//! The packed witness drivers every circuit's witness generation runs through.

use parallel::Chunks;
use primitives::bits::bit_transpose_64bytes;
use primitives::stream::Stream;

/// The bytes of the `u64` words on a little-endian target.
pub(crate) const fn packed_bytes(words: &[u64]) -> &[u8] {
    const _: () = assert!(
        cfg!(target_endian = "little"),
        "packed witness bytes assume little-endian"
    );
    // SAFETY: `u64` has no padding or invalid bit patterns, and `u8`'s
    // alignment divides `u64`'s, so the words are a valid `8 · len` byte slice.
    unsafe { core::slice::from_raw_parts(words.as_ptr().cast::<u8>(), words.len() * 8) }
}

/// One circuit's witness over a batch of instances, as the prover holds it.
///
/// `z`, `A·z` and `B·z` pack 64 bits a word, `2^k_log / 64` words per instance, instance-major.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct Witness {
    /// The witness bits.
    pub z: Vec<u64>,
    /// `A·z`.
    pub az: Vec<u64>,
    /// `B·z`.
    pub bz: Vec<u64>,
    /// `z` again in lincheck's byte stripes: `2^k_log` bytes per eight instances.
    pub stripes: Vec<u8>,
}

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
) -> Witness
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
    let mut z = Box::<[u64]>::new_uninit_slice(total_words);
    let mut a = Box::<[u64]>::new_uninit_slice(total_words);
    let mut b = Box::<[u64]>::new_uninit_slice(total_words);
    let mut all_stripes = Box::<[u8]>::new_uninit_slice((n_total / 8) * k);

    // A group's share: its packed words in each table, and one stripe per 8 instances.
    let group_words = group * (k / 64);
    let group_bytes = (group / 8) * k;
    let z_chunks = Chunks::new(&mut z, group_words);
    let a_chunks = Chunks::new(&mut a, group_words);
    let b_chunks = Chunks::new(&mut b, group_words);
    let stripe_chunks = Chunks::new(&mut all_stripes, group_bytes);
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
                stream.write(z_chunks.get(g), z_grp);
                stream.write(a_chunks.get(g), a_grp);
                stream.write(b_chunks.get(g), b_grp);
                stream.write(stripe_chunks.get(g), stripes);
            }
        },
        |(), ()| (),
    );

    // SAFETY: group `g` wrote chunk `g` of every table in full, and the chunk counts match.
    unsafe {
        Witness {
            z: z.assume_init().into_vec(),
            az: a.assume_init().into_vec(),
            bz: b.assume_init().into_vec(),
            stripes: all_stripes.assume_init().into_vec(),
        }
    }
}

/// Drive the parallel chunked witness build for `n_blocks` instances padded
/// to `2^n_blocks_log` slots, one instance at a time.
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
) -> Witness
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
) -> Witness {
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
