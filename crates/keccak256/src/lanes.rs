//! The permutation over any lane type, and the batched entry points that permute [`LANES`] states at once, one
//! vector register per state lane: AVX-512 (eight states), AVX2 (four), NEON (two, with the SHA3 instructions where
//! the target has them), or one at a time elsewhere. Every batched function is byte-identical to its one-input form.

use crate::{END_BIT, OUT_LEN, PAD_FIRST, RATE, RATE_LANES, RC, STATE_LANES, hash_from_state_offset, keccak_f};
use core::ops::Range;

/// One state lane across [`Lane::WIDTH`] states. The permutation is written once over this trait.
pub(crate) trait Lane: Copy {
    const WIDTH: usize;

    /// The lane of every state, from `src`, which holds exactly `WIDTH` words.
    fn load(src: &[u64]) -> Self;
    /// The inverse of [`load`](Self::load).
    fn store(self, dst: &mut [u64]);
    fn splat(x: u64) -> Self;
    fn xor(self, o: Self) -> Self;
    /// Rotate left by `N`, with `R = 64 - N` (`1 <= N < 64`).
    fn rotl<const N: i32, const R: i32>(self) -> Self;
    /// `(a ^ b).rotl::<N, R>()`, with `R = 64 - N` (`1 <= N < 64`).
    #[inline(always)]
    fn xor_rotl<const N: i32, const R: i32>(a: Self, b: Self) -> Self {
        a.xor(b).rotl::<N, R>()
    }
    /// χ on one lane: `a ^ (!b & c)`.
    fn chi(a: Self, b: Self, c: Self) -> Self;

    #[inline(always)]
    fn xor5(a: Self, b: Self, c: Self, d: Self, e: Self) -> Self {
        a.xor(b).xor(c).xor(d).xor(e)
    }

    /// θ's column effect: `c_prev ^ rotl(c_next, 1)`.
    #[inline(always)]
    fn theta_d(c_prev: Self, c_next: Self) -> Self {
        c_prev.xor(c_next.rotl::<1, 63>())
    }
}

/// The 24 rounds of θ, ρ, π, χ and ι, on x86. Straight-line, so every rotation is an immediate and every lane a
/// register.
///
/// Each round reads one state and writes the other, a whole output row at a time: its five lanes, rotated by their ρ
/// from where π takes them, then χ, then the row is stored and folded into the next round's column parities. A row
/// at a time keeps about sixteen values live, which fits AVX2's sixteen registers, where forming all twenty-five lanes
/// before χ spills.
// The rounds go in pairs, one into each state.
#[cfg(target_arch = "x86_64")]
const _: () = assert!(RC.len().is_multiple_of(2));

#[cfg(target_arch = "x86_64")]
#[inline(always)]
pub(crate) fn permute<S: Lane>(a: &mut [S; STATE_LANES]) {
    let mut c: [S; 5] = core::array::from_fn(|x| S::xor5(a[x], a[x + 5], a[x + 10], a[x + 15], a[x + 20]));
    let mut e = *a;
    for &[rc0, rc1] in RC.as_chunks::<2>().0 {
        round::<S, 5>(a, &mut e, &mut c, rc0);
        round::<S, 5>(&e, a, &mut c, rc1);
    }
}

/// [`permute`] where only the first row of the result is read, as a digest, a grind's lane or a challenge reads it:
/// lanes `0..5` come out permuted, the others are left stale. The last round computes that row alone.
#[cfg(target_arch = "x86_64")]
#[inline(always)]
pub(crate) fn permute_first_row<S: Lane>(a: &mut [S; STATE_LANES]) {
    let c: [S; 5] = core::array::from_fn(|x| S::xor5(a[x], a[x + 5], a[x + 10], a[x + 15], a[x + 20]));
    permute_first_row_with_c(a, c);
}

#[cfg(target_arch = "x86_64")]
#[inline(always)]
fn permute_first_row_with_c<S: Lane>(a: &mut [S; STATE_LANES], mut c: [S; 5]) {
    let mut e = *a;
    for &[rc0, rc1] in RC[..RC.len() - 2].as_chunks::<2>().0 {
        round::<S, 5>(a, &mut e, &mut c, rc0);
        round::<S, 5>(&e, a, &mut c, rc1);
    }
    round::<S, 5>(a, &mut e, &mut c, RC[RC.len() - 2]);
    round::<S, 1>(&e, a, &mut c, RC[RC.len() - 1]);
}

/// One round from `a` into the first `ROWS` rows of `out`, `c` holding the column parities of `a` on entry and, for a
/// whole round, of `out` on exit.
#[cfg(target_arch = "x86_64")]
#[inline(always)]
fn round<S: Lane, const ROWS: usize>(a: &[S; STATE_LANES], out: &mut [S; STATE_LANES], c: &mut [S; 5], rc: u64) {
    let d: [S; 5] = core::array::from_fn(|x| S::theta_d(c[(x + 4) % 5], c[(x + 1) % 5]));
    // Row `y` of the output takes the lanes π sends there, each rotated by its ρ.
    let mut row = |y: usize, [b0, b1, b2, b3, b4]: [S; 5]| {
        let mut r = [
            S::chi(b0, b1, b2),
            S::chi(b1, b2, b3),
            S::chi(b2, b3, b4),
            S::chi(b3, b4, b0),
            S::chi(b4, b0, b1),
        ];
        if y == 0 {
            r[0] = r[0].xor(S::splat(rc));
        }
        for x in 0..5 {
            out[5 * y + x] = r[x];
            c[x] = if y == 0 { r[x] } else { c[x].xor(r[x]) };
        }
    };
    row(
        0,
        [
            a[0].xor(d[0]),
            S::xor_rotl::<44, 20>(a[6], d[1]),
            S::xor_rotl::<43, 21>(a[12], d[2]),
            S::xor_rotl::<21, 43>(a[18], d[3]),
            S::xor_rotl::<14, 50>(a[24], d[4]),
        ],
    );
    if ROWS > 1 {
        row(
            1,
            [
                S::xor_rotl::<28, 36>(a[3], d[3]),
                S::xor_rotl::<20, 44>(a[9], d[4]),
                S::xor_rotl::<3, 61>(a[10], d[0]),
                S::xor_rotl::<45, 19>(a[16], d[1]),
                S::xor_rotl::<61, 3>(a[22], d[2]),
            ],
        );
    }
    if ROWS > 2 {
        row(
            2,
            [
                S::xor_rotl::<1, 63>(a[1], d[1]),
                S::xor_rotl::<6, 58>(a[7], d[2]),
                S::xor_rotl::<25, 39>(a[13], d[3]),
                S::xor_rotl::<8, 56>(a[19], d[4]),
                S::xor_rotl::<18, 46>(a[20], d[0]),
            ],
        );
    }
    if ROWS > 3 {
        row(
            3,
            [
                S::xor_rotl::<27, 37>(a[4], d[4]),
                S::xor_rotl::<36, 28>(a[5], d[0]),
                S::xor_rotl::<10, 54>(a[11], d[1]),
                S::xor_rotl::<15, 49>(a[17], d[2]),
                S::xor_rotl::<56, 8>(a[23], d[3]),
            ],
        );
    }
    if ROWS > 4 {
        row(
            4,
            [
                S::xor_rotl::<62, 2>(a[2], d[2]),
                S::xor_rotl::<55, 9>(a[8], d[3]),
                S::xor_rotl::<39, 25>(a[14], d[4]),
                S::xor_rotl::<41, 23>(a[15], d[0]),
                S::xor_rotl::<2, 62>(a[21], d[1]),
            ],
        );
    }
}

/// The 24 rounds of θ, ρ, π, χ and ι, elsewhere. Straight-line, so every rotation is an immediate and every lane a
/// register.
///
/// ρ and π are written by output row, χ takes the rows in turn, and the next round's column parities accumulate from
/// the lanes χ writes, which schedules better than forming every lane before χ and every parity after it. With 32
/// vector registers (NEON) nothing spills, and the x86 form's second state only adds loads and stores.
#[cfg(not(target_arch = "x86_64"))]
#[inline(always)]
fn round_non_x86<S: Lane>(a: &mut [S; STATE_LANES], c: &mut [S; 5], rc: u64) {
    let d: [S; 5] = core::array::from_fn(|x| S::theta_d(c[(x + 4) % 5], c[(x + 1) % 5]));
    // Row `y` holds the lanes π sends there, each rotated by its ρ.
    #[rustfmt::skip]
    let rows: [[S; 5]; 5] = [
        [a[0].xor(d[0]), S::xor_rotl::<44, 20>(a[6], d[1]), S::xor_rotl::<43, 21>(a[12], d[2]), S::xor_rotl::<21, 43>(a[18], d[3]), S::xor_rotl::<14, 50>(a[24], d[4])],
        [S::xor_rotl::<28, 36>(a[3], d[3]), S::xor_rotl::<20, 44>(a[9], d[4]), S::xor_rotl::<3, 61>(a[10], d[0]), S::xor_rotl::<45, 19>(a[16], d[1]), S::xor_rotl::<61, 3>(a[22], d[2])],
        [S::xor_rotl::<1, 63>(a[1], d[1]), S::xor_rotl::<6, 58>(a[7], d[2]), S::xor_rotl::<25, 39>(a[13], d[3]), S::xor_rotl::<8, 56>(a[19], d[4]), S::xor_rotl::<18, 46>(a[20], d[0])],
        [S::xor_rotl::<27, 37>(a[4], d[4]), S::xor_rotl::<36, 28>(a[5], d[0]), S::xor_rotl::<10, 54>(a[11], d[1]), S::xor_rotl::<15, 49>(a[17], d[2]), S::xor_rotl::<56, 8>(a[23], d[3])],
        [S::xor_rotl::<62, 2>(a[2], d[2]), S::xor_rotl::<55, 9>(a[8], d[3]), S::xor_rotl::<39, 25>(a[14], d[4]), S::xor_rotl::<41, 23>(a[15], d[0]), S::xor_rotl::<2, 62>(a[21], d[1])],
    ];
    for (y, &[b0, b1, b2, b3, b4]) in rows.iter().enumerate() {
        let mut row = [
            S::chi(b0, b1, b2),
            S::chi(b1, b2, b3),
            S::chi(b2, b3, b4),
            S::chi(b3, b4, b0),
            S::chi(b4, b0, b1),
        ];
        if y == 0 {
            row[0] = row[0].xor(S::splat(rc));
        }
        for x in 0..5 {
            a[5 * y + x] = row[x];
            c[x] = if y == 0 { row[x] } else { c[x].xor(row[x]) };
        }
    }
}

#[cfg(not(target_arch = "x86_64"))]
#[inline(always)]
pub(crate) fn permute<S: Lane>(a: &mut [S; STATE_LANES]) {
    let mut c: [S; 5] = core::array::from_fn(|x| S::xor5(a[x], a[x + 5], a[x + 10], a[x + 15], a[x + 20]));
    for &rc in &RC {
        round_non_x86(a, &mut c, rc);
    }
}

/// [`permute`] where only the first row of the result is read: the last round computes row 0 alone.
#[cfg(not(target_arch = "x86_64"))]
#[inline(always)]
pub(crate) fn permute_first_row<S: Lane>(a: &mut [S; STATE_LANES]) {
    let c: [S; 5] = core::array::from_fn(|x| S::xor5(a[x], a[x + 5], a[x + 10], a[x + 15], a[x + 20]));
    permute_first_row_with_c(a, c);
}

#[cfg(not(target_arch = "x86_64"))]
#[inline(always)]
fn permute_first_row_with_c<S: Lane>(a: &mut [S; STATE_LANES], mut c: [S; 5]) {
    for &rc in &RC[..RC.len() - 1] {
        round_non_x86(a, &mut c, rc);
    }
    let d: [S; 5] = core::array::from_fn(|x| S::theta_d(c[(x + 4) % 5], c[(x + 1) % 5]));
    let [b0, b1, b2, b3, b4] = [
        a[0].xor(d[0]),
        S::xor_rotl::<44, 20>(a[6], d[1]),
        S::xor_rotl::<43, 21>(a[12], d[2]),
        S::xor_rotl::<21, 43>(a[18], d[3]),
        S::xor_rotl::<14, 50>(a[24], d[4]),
    ];
    a[0] = S::chi(b0, b1, b2).xor(S::splat(RC[RC.len() - 1]));
    a[1] = S::chi(b1, b2, b3);
    a[2] = S::chi(b2, b3, b4);
    a[3] = S::chi(b3, b4, b0);
    a[4] = S::chi(b4, b0, b1);
}

/// One state: the scalar permutation, and the batched one where no vector backend applies.
impl Lane for u64 {
    const WIDTH: usize = 1;

    #[inline(always)]
    fn load(src: &[u64]) -> Self {
        src[0]
    }
    #[inline(always)]
    fn store(self, dst: &mut [u64]) {
        dst[0] = self;
    }
    #[inline(always)]
    fn splat(x: u64) -> Self {
        x
    }
    #[inline(always)]
    fn xor(self, o: Self) -> Self {
        self ^ o
    }
    #[inline(always)]
    fn rotl<const N: i32, const R: i32>(self) -> Self {
        const { assert!(N > 0 && N < 64 && N + R == 64) };
        self.rotate_left(N as u32)
    }
    #[inline(always)]
    fn chi(a: Self, b: Self, c: Self) -> Self {
        a ^ (!b & c)
    }
}

cfg_select! {
    all(target_arch = "x86_64", target_feature = "avx512f") => {
        type Backend = x86::Avx512;
    }
    all(target_arch = "x86_64", target_feature = "avx2") => {
        type Backend = x86::Avx2;
    }
    target_arch = "aarch64" => {
        type Backend = arm::Neon;
    }
    _ => {
        type Backend = u64;
    }
}

/// States the batched entry points permute together. They take any count and permute the remainder one at a time.
pub const LANES: usize = Backend::WIDTH;

/// Keccak-f\[1600\] of every state in place, [`LANES`] at a time.
pub fn keccak_f_many(states: &mut [[u64; STATE_LANES]]) {
    let (groups, rest) = states.as_chunks_mut::<LANES>();
    for group in groups {
        // Register `i` holds lane `i` of every state.
        let mut st: [Backend; STATE_LANES] =
            core::array::from_fn(|i| Backend::load(&core::array::from_fn::<u64, LANES, _>(|l| group[l][i])));
        permute(&mut st);
        for (i, lane) in st.iter().enumerate() {
            let mut words = [0; LANES];
            lane.store(&mut words);
            for (state, word) in group.iter_mut().zip(words) {
                state[i] = word;
            }
        }
    }
    rest.iter_mut().for_each(keccak_f);
}

/// The first of `nonces` that, written into lane `at` of `template`, leaves lane `out` of the permuted state zero under
/// `mask`, [`LANES`] nonces at a time.
pub fn first_nonce(template: &[u64; STATE_LANES], at: usize, nonces: Range<u64>, out: usize, mask: u64) -> Option<u64> {
    assert!(
        out < 5,
        "the tested lane is in the first row, all the permutation computes in full"
    );
    let col = at % 5;
    let c_base: [Backend; 5] = core::array::from_fn(|x| {
        let mut p = 0u64;
        for row in 0..5 {
            let idx = x + 5 * row;
            if idx != at {
                p ^= template[idx];
            }
        }
        Backend::splat(p)
    });
    let template: [Backend; STATE_LANES] = core::array::from_fn(|i| Backend::splat(template[i]));
    let mut first = nonces.start;
    while first < nonces.end {
        let mut st = template;
        let nonce = Backend::load(&core::array::from_fn::<u64, LANES, _>(|l| first.wrapping_add(l as u64)));
        st[at] = nonce;
        let mut c = c_base;
        c[col] = c[col].xor(nonce);
        permute_first_row_with_c(&mut st, c);
        let mut words = [0; LANES];
        st[out].store(&mut words);
        let n = (nonces.end - first).min(LANES as u64) as usize;
        if let Some(l) = words[..n].iter().position(|w| w & mask == 0) {
            return Some(first + l as u64);
        }
        first = first.saturating_add(LANES as u64);
    }
    None
}

/// Batched Keccak-256 of `data` split into `len`-byte inputs, writing one 32-byte digest per input to `out`.
pub fn hash_many(data: &[u8], len: usize, out: &mut [u8]) {
    hash_many_from_state(data, len, &[0; STATE_LANES], out);
}

/// [`hash_many`] continued from one sponge state shared by every input, which has absorbed whole blocks (see
/// [`zero_prefix_state`](crate::zero_prefix_state)). Byte-identical to hashing each full image.
pub fn hash_many_from_state(data: &[u8], len: usize, state: &[u64; STATE_LANES], out: &mut [u8]) {
    let n = out.len() / OUT_LEN;
    assert_eq!((data.len(), out.len()), (n * len, n * OUT_LEN));
    for (g, digests) in out.as_chunks_mut::<{ LANES * OUT_LEN }>().0.iter_mut().enumerate() {
        hash_group(&data[g * LANES * len..][..LANES * len], len, state, digests);
    }
    for i in n / LANES * LANES..n {
        out[i * OUT_LEN..][..OUT_LEN].copy_from_slice(&hash_from_state_offset(&data[i * len..][..len], state, 0));
    }
}

/// [`hash_many_from_state`] where each input is preceded by `start_word` zero words (`start_word < RATE_LANES`) in
/// its first block after `state`. Byte-identical to zero-extending each input by `8 * start_word` leading bytes.
pub fn hash_many_from_state_offset(
    data: &[u8],
    len: usize,
    state: &[u64; STATE_LANES],
    start_word: usize,
    out: &mut [u8],
) {
    assert!(start_word < RATE_LANES, "offset stays within one rate block");
    if start_word == 0 {
        return hash_many_from_state(data, len, state, out);
    }
    let n = out.len() / OUT_LEN;
    assert_eq!((data.len(), out.len()), (n * len, n * OUT_LEN));
    for (g, digests) in out.as_chunks_mut::<{ LANES * OUT_LEN }>().0.iter_mut().enumerate() {
        hash_group_offset(&data[g * LANES * len..][..LANES * len], len, state, start_word, digests);
    }
    for i in n / LANES * LANES..n {
        out[i * OUT_LEN..][..OUT_LEN].copy_from_slice(&hash_from_state_offset(
            &data[i * len..][..len],
            state,
            start_word,
        ));
    }
}

/// The digests of [`LANES`] inputs of `len` bytes, input `l` at `inputs[l * len..]`.
#[inline(always)]
fn hash_group(inputs: &[u8], len: usize, state: &[u64; STATE_LANES], out: &mut [u8; LANES * OUT_LEN]) {
    let mut st: [Backend; STATE_LANES] = core::array::from_fn(|i| Backend::splat(state[i]));
    let (blocks, tail) = (len / RATE, len % RATE);
    for b in 0..blocks {
        absorb_at(&mut st, 0, inputs, len, b * RATE, RATE_LANES);
        permute(&mut st);
    }
    // The final block: the tail's whole words, its last partial word, then the padding, the same in every input.
    let (words, part) = (tail / 8, tail % 8);
    absorb_at(&mut st, 0, inputs, len, blocks * RATE, words);
    if part > 0 {
        st[words] = st[words].xor(word(inputs, len, blocks * RATE + 8 * words, part));
    }
    st[words] = st[words].xor(Backend::splat(u64::from(PAD_FIRST) << (8 * part)));
    st[RATE_LANES - 1] = st[RATE_LANES - 1].xor(Backend::splat(END_BIT));
    permute_first_row(&mut st);
    digests(&st, out);
}

/// The digests of [`LANES`] inputs of `len` bytes, input `l` at `inputs[l * len..]`, with `start_word > 0` leading
/// zero words in the first block.
#[inline(always)]
fn hash_group_offset(
    inputs: &[u8],
    len: usize,
    state: &[u64; STATE_LANES],
    start_word: usize,
    out: &mut [u8; LANES * OUT_LEN],
) {
    let mut st: [Backend; STATE_LANES] = core::array::from_fn(|i| Backend::splat(state[i]));
    let first_words = RATE_LANES - start_word;
    let first_bytes = 8 * first_words;
    if len < first_bytes {
        let (words, part) = (len / 8, len % 8);
        absorb_at(&mut st, start_word, inputs, len, 0, words);
        let pad_lane = start_word + words;
        if part > 0 {
            st[pad_lane] = st[pad_lane].xor(word(inputs, len, 8 * words, part));
        }
        st[pad_lane] = st[pad_lane].xor(Backend::splat(u64::from(PAD_FIRST) << (8 * part)));
        st[RATE_LANES - 1] = st[RATE_LANES - 1].xor(Backend::splat(END_BIT));
        permute_first_row(&mut st);
        digests(&st, out);
        return;
    }
    absorb_at(&mut st, start_word, inputs, len, 0, first_words);
    permute(&mut st);
    let rem = len - first_bytes;
    let (blocks, tail) = (rem / RATE, rem % RATE);
    for b in 0..blocks {
        absorb_at(&mut st, 0, inputs, len, first_bytes + b * RATE, RATE_LANES);
        permute(&mut st);
    }
    let (words, part) = (tail / 8, tail % 8);
    let tail_at = first_bytes + blocks * RATE;
    absorb_at(&mut st, 0, inputs, len, tail_at, words);
    if part > 0 {
        st[words] = st[words].xor(word(inputs, len, tail_at + 8 * words, part));
    }
    st[words] = st[words].xor(Backend::splat(u64::from(PAD_FIRST) << (8 * part)));
    st[RATE_LANES - 1] = st[RATE_LANES - 1].xor(Backend::splat(END_BIT));
    permute_first_row(&mut st);
    digests(&st, out);
}

/// The first `n < 8` bytes of every input from byte `at` on, as a little-endian word.
#[inline(always)]
fn word(inputs: &[u8], len: usize, at: usize, n: usize) -> Backend {
    Backend::load(&core::array::from_fn::<u64, LANES, _>(|l| {
        let mut bytes = [0u8; 8];
        bytes[..n].copy_from_slice(&inputs[l * len + at..][..n]);
        u64::from_le_bytes(bytes)
    }))
}

cfg_select! {
    all(target_arch = "x86_64", target_feature = "avx2") => {
        use x86::{absorb_at, digests};
    }
    target_arch = "aarch64" => {
        use arm::{absorb_at, digests};
    }
    _ => {
        /// XOR the `words` little-endian words of every input from byte `at` on into `st[start..start + words]`.
        #[inline(always)]
        fn absorb_at(
            st: &mut [Backend; STATE_LANES],
            start: usize,
            inputs: &[u8],
            len: usize,
            at: usize,
            words: usize,
        ) {
            for (w, lane) in st[start..start + words].iter_mut().enumerate() {
                *lane = lane.xor(Backend::load(&core::array::from_fn::<u64, LANES, _>(|l| {
                    u64::from_le_bytes(*inputs[l * len + at + 8 * w..].first_chunk().unwrap())
                })));
            }
        }

        /// Every input's digest, the first [`OUT_LEN`] bytes of its state, input `l`'s at `out[l * OUT_LEN..]`.
        #[inline(always)]
        fn digests(st: &[Backend; STATE_LANES], out: &mut [u8; LANES * OUT_LEN]) {
            let mut words = [[0u64; LANES]; OUT_LEN / 8];
            for (lane, words) in st.iter().zip(&mut words) {
                lane.store(words);
            }
            for (l, digest) in out.as_chunks_mut::<OUT_LEN>().0.iter_mut().enumerate() {
                for (w, bytes) in digest.as_chunks_mut::<8>().0.iter_mut().enumerate() {
                    *bytes = words[w][l].to_le_bytes();
                }
            }
        }
    }
}

/// The first 128 bits of the digest, little endian, of `template`'s input with `values[i]` XORed into its lanes `at`
/// and `at + 1`, into `out[i]`, [`LANES`] values at a time. `template` is that input's
/// [`final_state`](crate::final_state) with those 16 bytes zero, so a value costs one permutation.
pub fn digest_halves_from(template: &[u64; STATE_LANES], at: usize, values: &[u128], out: &mut [u128]) {
    // The final block ends in padding, so the value stops before its last lane.
    assert!(at + 2 < RATE_LANES && values.len() == out.len());
    let (groups, rest) = values.as_chunks::<LANES>();
    for (values, out) in groups.iter().zip(out.as_chunks_mut::<LANES>().0) {
        let mut st: [Backend; STATE_LANES] = core::array::from_fn(|i| Backend::splat(template[i]));
        for (j, shift) in [(0, 0), (1, 64)] {
            st[at + j] = st[at + j].xor(Backend::load(&values.map(|v| (v >> shift) as u64)));
        }
        permute_first_row(&mut st);
        let mut words = [[0u64; LANES]; 2];
        st[0].store(&mut words[0]);
        st[1].store(&mut words[1]);
        *out = core::array::from_fn(|l| u128::from(words[0][l]) | u128::from(words[1][l]) << 64);
    }
    for (&value, out) in rest.iter().zip(&mut out[values.len() - rest.len()..]) {
        let mut state = *template;
        state[at] ^= value as u64;
        state[at + 1] ^= (value >> 64) as u64;
        keccak_f(&mut state);
        *out = u128::from(state[0]) | u128::from(state[1]) << 64;
    }
}

#[cfg(all(target_arch = "x86_64", target_feature = "avx2"))]
mod x86 {
    use super::Lane;
    use crate::{OUT_LEN, RATE_LANES, STATE_LANES};
    use core::arch::x86_64::*;

    /// Four states in a YMM register. No 64-bit rotate before AVX-512, so a rotation is an immediate shift pair.
    #[cfg(not(target_feature = "avx512f"))]
    #[derive(Clone, Copy)]
    pub(super) struct Avx2(__m256i);

    #[cfg(not(target_feature = "avx512f"))]
    impl Lane for Avx2 {
        const WIDTH: usize = 4;

        #[inline(always)]
        fn load(src: &[u64]) -> Self {
            let src: &[u64; 4] = src.try_into().unwrap();
            // SAFETY: the module's cfg enables avx2, and `src` is 32 readable bytes.
            Self(unsafe { _mm256_loadu_si256(src.as_ptr().cast()) })
        }
        #[inline(always)]
        fn store(self, dst: &mut [u64]) {
            let dst: &mut [u64; 4] = dst.try_into().unwrap();
            // SAFETY: the module's cfg enables avx2, and `dst` is 32 writable bytes.
            unsafe { _mm256_storeu_si256(dst.as_mut_ptr().cast(), self.0) }
        }
        #[inline(always)]
        fn splat(x: u64) -> Self {
            // SAFETY: the module's cfg enables avx2.
            Self(unsafe { _mm256_set1_epi64x(x as i64) })
        }
        #[inline(always)]
        fn xor(self, o: Self) -> Self {
            // SAFETY: the module's cfg enables avx2.
            Self(unsafe { _mm256_xor_si256(self.0, o.0) })
        }
        #[inline(always)]
        fn rotl<const N: i32, const R: i32>(self) -> Self {
            const { assert!(N > 0 && N < 64 && N + R == 64) };
            // SAFETY: the module's cfg enables avx2, and 1 <= N < 64 with R = 64 - N.
            unsafe {
                let l = if N == 1 {
                    _mm256_add_epi64(self.0, self.0)
                } else {
                    _mm256_slli_epi64::<N>(self.0)
                };
                let r = _mm256_srli_epi64::<R>(self.0);
                Self(_mm256_or_si256(l, r))
            }
        }
        #[inline(always)]
        fn chi(a: Self, b: Self, c: Self) -> Self {
            // SAFETY: the module's cfg enables avx2.
            Self(unsafe { _mm256_xor_si256(a.0, _mm256_andnot_si256(b.0, c.0)) })
        }
    }

    /// The 4x4 transpose of 64-bit words: word `j` of row `i` becomes word `i` of row `j`.
    #[cfg(not(target_feature = "avx512f"))]
    #[inline(always)]
    fn transpose4(r: [__m256i; 4]) -> [__m256i; 4] {
        // SAFETY: the module's cfg enables avx2.
        unsafe {
            let a0 = _mm256_unpacklo_epi64(r[0], r[1]);
            let a1 = _mm256_unpackhi_epi64(r[0], r[1]);
            let a2 = _mm256_unpacklo_epi64(r[2], r[3]);
            let a3 = _mm256_unpackhi_epi64(r[2], r[3]);
            [
                _mm256_permute2x128_si256::<0x20>(a0, a2),
                _mm256_permute2x128_si256::<0x20>(a1, a3),
                _mm256_permute2x128_si256::<0x31>(a0, a2),
                _mm256_permute2x128_si256::<0x31>(a1, a3),
            ]
        }
    }

    /// The generic `absorb_at` on four inputs: groups of four words per input transposed into four state lanes.
    #[cfg(not(target_feature = "avx512f"))]
    #[inline(always)]
    pub(super) fn absorb_at(
        st: &mut [Avx2; STATE_LANES],
        start: usize,
        inputs: &[u8],
        len: usize,
        at: usize,
        words: usize,
    ) {
        assert!(start + words <= RATE_LANES && at + 8 * words <= len);
        let groups = words / 4;
        for g in 0..groups {
            let rows: [__m256i; 4] = core::array::from_fn(|l| {
                let row = &inputs[l * len + at + 32 * g..][..32];
                // SAFETY: the module's cfg enables avx2, and `row` is 32 readable bytes.
                unsafe { _mm256_loadu_si256(row.as_ptr().cast()) }
            });
            for (lane, col) in st[start + 4 * g..start + 4 * g + 4].iter_mut().zip(transpose4(rows)) {
                *lane = lane.xor(Avx2(col));
            }
        }
        for w in 4 * groups..words {
            st[start + w] = st[start + w].xor(Avx2::load(&core::array::from_fn::<u64, 4, _>(|l| {
                u64::from_le_bytes(*inputs[l * len + at + 8 * w..].first_chunk().unwrap())
            })));
        }
    }

    /// The generic `digests` on four inputs: the four digest lanes transposed directly into four 32-byte stores.
    #[cfg(not(target_feature = "avx512f"))]
    #[inline(always)]
    pub(super) fn digests(st: &[Avx2; STATE_LANES], out: &mut [u8; 4 * OUT_LEN]) {
        let rows = transpose4([st[0].0, st[1].0, st[2].0, st[3].0]);
        for (row, bytes) in rows.iter().zip(out.as_chunks_mut::<OUT_LEN>().0) {
            // SAFETY: the module's cfg enables avx2, and `bytes` is 32 writable bytes.
            unsafe { _mm256_storeu_si256(bytes.as_mut_ptr().cast(), *row) }
        }
    }

    /// Eight states in a ZMM register, with a native rotate and `vpternlogq` for χ and the column parity.
    #[cfg(target_feature = "avx512f")]
    #[derive(Clone, Copy)]
    pub(super) struct Avx512(__m512i);

    #[cfg(target_feature = "avx512f")]
    impl Lane for Avx512 {
        const WIDTH: usize = 8;

        #[inline(always)]
        fn load(src: &[u64]) -> Self {
            let src: &[u64; 8] = src.try_into().unwrap();
            // SAFETY: the module's cfg enables avx512f, and `src` is 64 readable bytes.
            Self(unsafe { _mm512_loadu_si512(src.as_ptr().cast()) })
        }
        #[inline(always)]
        fn store(self, dst: &mut [u64]) {
            let dst: &mut [u64; 8] = dst.try_into().unwrap();
            // SAFETY: the module's cfg enables avx512f, and `dst` is 64 writable bytes.
            unsafe { _mm512_storeu_si512(dst.as_mut_ptr().cast(), self.0) }
        }
        #[inline(always)]
        fn splat(x: u64) -> Self {
            // SAFETY: the module's cfg enables avx512f.
            Self(unsafe { _mm512_set1_epi64(x as i64) })
        }
        #[inline(always)]
        fn xor(self, o: Self) -> Self {
            // SAFETY: the module's cfg enables avx512f.
            Self(unsafe { _mm512_xor_si512(self.0, o.0) })
        }
        #[inline(always)]
        fn rotl<const N: i32, const R: i32>(self) -> Self {
            const { assert!(N > 0 && N < 64 && N + R == 64) };
            // SAFETY: the module's cfg enables avx512f.
            Self(unsafe { _mm512_rol_epi64::<N>(self.0) })
        }
        #[inline(always)]
        fn chi(a: Self, b: Self, c: Self) -> Self {
            // The truth table of `a ^ (!b & c)` over (a, b, c) = (0xF0, 0xCC, 0xAA).
            // SAFETY: the module's cfg enables avx512f.
            Self(unsafe { _mm512_ternarylogic_epi64::<0xD2>(a.0, b.0, c.0) })
        }
        #[inline(always)]
        fn xor5(a: Self, b: Self, c: Self, d: Self, e: Self) -> Self {
            // SAFETY: the module's cfg enables avx512f.
            unsafe {
                let t = _mm512_ternarylogic_epi64::<0x96>(a.0, b.0, c.0);
                Self(_mm512_ternarylogic_epi64::<0x96>(t, d.0, e.0))
            }
        }
    }

    /// The generic `absorb_at` on eight inputs: each input's words in rows of eight, transposed into one register per
    /// word.
    #[cfg(target_feature = "avx512f")]
    #[inline(always)]
    pub(super) fn absorb_at(
        st: &mut [Avx512; STATE_LANES],
        start: usize,
        inputs: &[u8],
        len: usize,
        at: usize,
        words: usize,
    ) {
        assert!(start + words <= RATE_LANES && at + 8 * words <= len);
        for g in 0..words.div_ceil(8) {
            let n = (words - 8 * g).min(8);
            let rows: [__m512i; 8] = core::array::from_fn(|l| {
                let row = &inputs[l * len + at + 64 * g..][..8 * n];
                // SAFETY: the module's cfg enables avx512f, and the mask reads the row's `n` words and no others.
                unsafe { _mm512_maskz_loadu_epi64(((1u32 << n) - 1) as __mmask8, row.as_ptr().cast()) }
            });
            for (lane, col) in st[start + 8 * g..start + 8 * g + n].iter_mut().zip(transpose8(rows)) {
                *lane = lane.xor(Avx512(col));
            }
        }
    }

    /// The generic `digests` on eight inputs: the four digest lanes transposed into rows, two inputs' rows per store.
    #[cfg(target_feature = "avx512f")]
    #[inline(always)]
    pub(super) fn digests(st: &[Avx512; STATE_LANES], out: &mut [u8; 8 * OUT_LEN]) {
        // SAFETY: the module's cfg enables avx512f.
        let zero = unsafe { _mm512_setzero_si512() };
        let rows = transpose8([st[0].0, st[1].0, st[2].0, st[3].0, zero, zero, zero, zero]);
        for ([first, second], bytes) in rows.as_chunks::<2>().0.iter().zip(out.as_chunks_mut::<64>().0) {
            // SAFETY: the module's cfg enables avx512f, and `bytes` is 64 writable bytes.
            unsafe { _mm512_storeu_si512(bytes.as_mut_ptr().cast(), _mm512_shuffle_i64x2::<0x44>(*first, *second)) }
        }
    }

    /// The 8x8 transpose of 64-bit words: word `j` of row `i` becomes word `i` of row `j`.
    #[cfg(target_feature = "avx512f")]
    #[inline(always)]
    fn transpose8(r: [__m512i; 8]) -> [__m512i; 8] {
        // SAFETY: the module's cfg enables avx512f.
        unsafe {
            // Pairs of words, then 128-bit lane picks to finish.
            let (a0, a1) = (_mm512_unpacklo_epi64(r[0], r[1]), _mm512_unpackhi_epi64(r[0], r[1]));
            let (a2, a3) = (_mm512_unpacklo_epi64(r[2], r[3]), _mm512_unpackhi_epi64(r[2], r[3]));
            let (a4, a5) = (_mm512_unpacklo_epi64(r[4], r[5]), _mm512_unpackhi_epi64(r[4], r[5]));
            let (a6, a7) = (_mm512_unpacklo_epi64(r[6], r[7]), _mm512_unpackhi_epi64(r[6], r[7]));
            let b0 = _mm512_shuffle_i64x2::<0x88>(a0, a2);
            let b1 = _mm512_shuffle_i64x2::<0x88>(a1, a3);
            let b2 = _mm512_shuffle_i64x2::<0xDD>(a0, a2);
            let b3 = _mm512_shuffle_i64x2::<0xDD>(a1, a3);
            let b4 = _mm512_shuffle_i64x2::<0x88>(a4, a6);
            let b5 = _mm512_shuffle_i64x2::<0x88>(a5, a7);
            let b6 = _mm512_shuffle_i64x2::<0xDD>(a4, a6);
            let b7 = _mm512_shuffle_i64x2::<0xDD>(a5, a7);
            [
                _mm512_shuffle_i64x2::<0x88>(b0, b4),
                _mm512_shuffle_i64x2::<0x88>(b1, b5),
                _mm512_shuffle_i64x2::<0x88>(b2, b6),
                _mm512_shuffle_i64x2::<0x88>(b3, b7),
                _mm512_shuffle_i64x2::<0xDD>(b0, b4),
                _mm512_shuffle_i64x2::<0xDD>(b1, b5),
                _mm512_shuffle_i64x2::<0xDD>(b2, b6),
                _mm512_shuffle_i64x2::<0xDD>(b3, b7),
            ]
        }
    }
}

#[cfg(target_arch = "aarch64")]
mod arm {
    use super::Lane;
    use crate::{OUT_LEN, RATE_LANES, STATE_LANES};
    use core::arch::aarch64::*;

    /// Two states in a NEON register. With the SHA3 extension, χ is one `BCAX`, the column parity two `EOR3` and θ's
    /// rotate-and-XOR one `RAX1`.
    #[derive(Clone, Copy)]
    pub(super) struct Neon(uint64x2_t);

    impl Lane for Neon {
        const WIDTH: usize = 2;

        #[inline(always)]
        fn load(src: &[u64]) -> Self {
            let src: &[u64; 2] = src.try_into().unwrap();
            // SAFETY: `src` is 16 readable bytes, and NEON is in the aarch64 baseline.
            Self(unsafe { vld1q_u64(src.as_ptr()) })
        }
        #[inline(always)]
        fn store(self, dst: &mut [u64]) {
            let dst: &mut [u64; 2] = dst.try_into().unwrap();
            // SAFETY: `dst` is 16 writable bytes, and NEON is in the aarch64 baseline.
            unsafe { vst1q_u64(dst.as_mut_ptr(), self.0) }
        }
        #[inline(always)]
        fn splat(x: u64) -> Self {
            // SAFETY: NEON is in the aarch64 baseline.
            Self(unsafe { vdupq_n_u64(x) })
        }
        #[inline(always)]
        fn xor(self, o: Self) -> Self {
            // SAFETY: NEON is in the aarch64 baseline.
            Self(unsafe { veorq_u64(self.0, o.0) })
        }
        #[inline(always)]
        fn rotl<const N: i32, const R: i32>(self) -> Self {
            const { assert!(N > 0 && N < 64 && N + R == 64) };
            // SAFETY: NEON is in the aarch64 baseline, and 1 <= N < 64 with R = 64 - N.
            unsafe { Self(vsriq_n_u64::<R>(vshlq_n_u64::<N>(self.0), self.0)) }
        }
        #[cfg(target_feature = "sha3")]
        #[inline(always)]
        fn xor_rotl<const N: i32, const R: i32>(a: Self, b: Self) -> Self {
            const { assert!(N > 0 && N < 64 && N + R == 64) };
            // XAR rotates right by `R = 64 - N`, which is a left rotation by `N`.
            // SAFETY: the cfg enables sha3, and 1 <= R < 64.
            Self(unsafe { vxarq_u64::<R>(a.0, b.0) })
        }
        #[inline(always)]
        fn chi(a: Self, b: Self, c: Self) -> Self {
            #[cfg(target_feature = "sha3")]
            // BCAX(a, c, b) = a ^ (c & !b).
            // SAFETY: the cfg enables sha3.
            return Self(unsafe { vbcaxq_u64(a.0, c.0, b.0) });
            #[cfg(not(target_feature = "sha3"))]
            // SAFETY: NEON is in the aarch64 baseline.
            Self(unsafe { veorq_u64(a.0, vbicq_u64(c.0, b.0)) })
        }
        #[cfg(target_feature = "sha3")]
        #[inline(always)]
        fn xor5(a: Self, b: Self, c: Self, d: Self, e: Self) -> Self {
            // SAFETY: the cfg enables sha3.
            Self(unsafe { veor3q_u64(veor3q_u64(a.0, b.0, c.0), d.0, e.0) })
        }
        #[cfg(target_feature = "sha3")]
        #[inline(always)]
        fn theta_d(c_prev: Self, c_next: Self) -> Self {
            // SAFETY: the cfg enables sha3.
            Self(unsafe { vrax1q_u64(c_prev.0, c_next.0) })
        }
    }

    /// The generic `absorb_at` on two inputs: two words of each per load, `ZIP1` and `ZIP2` turning the two rows into
    /// two lanes.
    #[inline(always)]
    pub(super) fn absorb_at(
        st: &mut [Neon; STATE_LANES],
        start: usize,
        inputs: &[u8],
        len: usize,
        at: usize,
        words: usize,
    ) {
        assert!(start + words <= RATE_LANES && at + 8 * words <= len);
        let (a, b) = (&inputs[at..][..8 * words], &inputs[len + at..][..8 * words]);
        for (p, (x, y)) in a.as_chunks::<16>().0.iter().zip(b.as_chunks::<16>().0).enumerate() {
            // SAFETY: `x` and `y` are 16 readable bytes each, and NEON is in the aarch64 baseline.
            unsafe {
                let (x, y) = (vld1q_u64(x.as_ptr().cast()), vld1q_u64(y.as_ptr().cast()));
                st[start + 2 * p] = Neon(veorq_u64(st[start + 2 * p].0, vzip1q_u64(x, y)));
                st[start + 2 * p + 1] = Neon(veorq_u64(st[start + 2 * p + 1].0, vzip2q_u64(x, y)));
            }
        }
        if words % 2 == 1 {
            let w = words - 1;
            let word = |input: &[u8]| u64::from_le_bytes(*input[8 * w..].first_chunk().unwrap());
            st[start + w] = st[start + w].xor(Neon::load(&[word(a), word(b)]));
        }
    }

    /// The generic `digests` on two inputs: `ZIP1` of two digest lanes is two words of the first input, `ZIP2` of
    /// the second.
    #[inline(always)]
    pub(super) fn digests(st: &[Neon; STATE_LANES], out: &mut [u8; 2 * OUT_LEN]) {
        // SAFETY: NEON is in the aarch64 baseline.
        let halves = unsafe {
            [
                vzip1q_u64(st[0].0, st[1].0),
                vzip1q_u64(st[2].0, st[3].0),
                vzip2q_u64(st[0].0, st[1].0),
                vzip2q_u64(st[2].0, st[3].0),
            ]
        };
        for (bytes, half) in out.as_chunks_mut::<16>().0.iter_mut().zip(halves) {
            // SAFETY: `bytes` is 16 writable bytes, and NEON is in the aarch64 baseline.
            unsafe { vst1q_u64(bytes.as_mut_ptr().cast(), half) }
        }
    }
}
