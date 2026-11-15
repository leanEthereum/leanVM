//! The permutation over any lane type, and the batched entry points that permute [`LANES`] states at once, one
//! vector register per state lane: AVX-512 (eight states), AVX2 (four), NEON (two, with the SHA3 instructions where
//! the target has them), or one at a time elsewhere. Every batched function is byte-identical to its one-input form.

use crate::{END_BIT, OUT_LEN, PAD_FIRST, RATE, RATE_LANES, RC, STATE_LANES, hash_from_state, keccak_f};

/// One state lane across [`Lane::WIDTH`] states. The permutation is written once over this trait.
pub(crate) trait Lane: Copy {
    const WIDTH: usize;

    /// The lane of every state, from `src`, which holds exactly `WIDTH` words.
    fn load(src: &[u64]) -> Self;
    /// The inverse of [`load`](Self::load).
    fn store(self, dst: &mut [u64]);
    fn splat(x: u64) -> Self;
    fn xor(self, o: Self) -> Self;
    /// Rotate left by `N`, `0 <= N < 64`.
    fn rotl<const N: i32>(self) -> Self;
    /// χ on one lane: `a ^ (!b & c)`.
    fn chi(a: Self, b: Self, c: Self) -> Self;

    #[inline(always)]
    fn xor5(a: Self, b: Self, c: Self, d: Self, e: Self) -> Self {
        a.xor(b).xor(c).xor(d).xor(e)
    }

    /// θ's column effect: `c_prev ^ rotl(c_next, 1)`.
    #[inline(always)]
    fn theta_d(c_prev: Self, c_next: Self) -> Self {
        c_prev.xor(c_next.rotl::<1>())
    }
}

/// The 24 rounds of θ, ρ, π, χ and ι. Straight-line, so every rotation is an immediate and every lane a register.
///
/// ρ and π are written by output row, χ takes the rows in turn, and the next round's column parities accumulate from
/// the lanes χ writes, which schedules better than forming every lane before χ and every parity after it.
#[inline(always)]
pub(crate) fn permute<S: Lane>(a: &mut [S; STATE_LANES]) {
    let mut c: [S; 5] = core::array::from_fn(|x| S::xor5(a[x], a[x + 5], a[x + 10], a[x + 15], a[x + 20]));
    for &rc in &RC {
        let d: [S; 5] = core::array::from_fn(|x| S::theta_d(c[(x + 4) % 5], c[(x + 1) % 5]));
        let t = |i: usize| a[i].xor(d[i % 5]);
        // Row `y` holds the lanes π sends there, each rotated by its ρ.
        #[rustfmt::skip]
        let rows: [[S; 5]; 5] = [
            [t(0), t(6).rotl::<44>(), t(12).rotl::<43>(), t(18).rotl::<21>(), t(24).rotl::<14>()],
            [t(3).rotl::<28>(), t(9).rotl::<20>(), t(10).rotl::<3>(), t(16).rotl::<45>(), t(22).rotl::<61>()],
            [t(1).rotl::<1>(), t(7).rotl::<6>(), t(13).rotl::<25>(), t(19).rotl::<8>(), t(20).rotl::<18>()],
            [t(4).rotl::<27>(), t(5).rotl::<36>(), t(11).rotl::<10>(), t(17).rotl::<15>(), t(23).rotl::<56>()],
            [t(2).rotl::<62>(), t(8).rotl::<55>(), t(14).rotl::<39>(), t(15).rotl::<41>(), t(21).rotl::<2>()],
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
    fn rotl<const N: i32>(self) -> Self {
        opaque(self.rotate_left(N as u32))
    }
    #[inline(always)]
    fn chi(a: Self, b: Self, c: Self) -> Self {
        a ^ (!b & c)
    }
}

/// `x`, through an empty assembly block LLVM cannot see into. On AVX-512 targets its SLP vectorizer otherwise packs
/// the scalar permutation's lanes into vector registers, which loses to plain scalar code.
#[inline(always)]
fn opaque(x: u64) -> u64 {
    cfg_select! {
        all(target_arch = "x86_64", target_feature = "avx512f") => {
            let mut x = x;
            // SAFETY: an empty block that reads and writes only `x`'s register.
            unsafe { core::arch::asm!("/* {x} */", x = inout(reg) x, options(pure, nomem, nostack, preserves_flags)) };
            x
        }
        _ => x,
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
        out[i * OUT_LEN..][..OUT_LEN].copy_from_slice(&hash_from_state(&data[i * len..][..len], state));
    }
}

/// The digests of [`LANES`] inputs of `len` bytes, input `l` at `inputs[l * len..]`.
#[inline(always)]
fn hash_group(inputs: &[u8], len: usize, state: &[u64; STATE_LANES], out: &mut [u8; LANES * OUT_LEN]) {
    let mut st: [Backend; STATE_LANES] = core::array::from_fn(|i| Backend::splat(state[i]));
    let (blocks, tail) = (len / RATE, len % RATE);
    for b in 0..blocks {
        absorb(&mut st, inputs, len, b * RATE, RATE_LANES);
        permute(&mut st);
    }
    // The final block: the tail's whole words, its last partial word, then the padding, the same in every input.
    let (words, part) = (tail / 8, tail % 8);
    absorb(&mut st, inputs, len, blocks * RATE, words);
    if part > 0 {
        st[words] = st[words].xor(word(inputs, len, blocks * RATE + 8 * words, part));
    }
    st[words] = st[words].xor(Backend::splat(u64::from(PAD_FIRST) << (8 * part)));
    st[RATE_LANES - 1] = st[RATE_LANES - 1].xor(Backend::splat(END_BIT));
    permute(&mut st);
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
    all(target_arch = "x86_64", target_feature = "avx512f") => {
        use x86::{absorb, digests};
    }
    target_arch = "aarch64" => {
        use arm::{absorb, digests};
    }
    _ => {
        /// XOR the `words` little-endian words of every input from byte `at` on into `st[..words]`.
        #[inline(always)]
        fn absorb(st: &mut [Backend; STATE_LANES], inputs: &[u8], len: usize, at: usize, words: usize) {
            for (w, lane) in st[..words].iter_mut().enumerate() {
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
        permute(&mut st);
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
    #[cfg(target_feature = "avx512f")]
    use crate::{OUT_LEN, RATE_LANES, STATE_LANES};
    use core::arch::x86_64::*;

    /// Four states in a YMM register. No 64-bit rotate before AVX-512, so a rotation is a shift pair.
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
        fn rotl<const N: i32>(self) -> Self {
            if N == 0 {
                return self;
            }
            // SAFETY: the module's cfg enables avx2.
            unsafe {
                let l = _mm256_sll_epi64(self.0, _mm_cvtsi32_si128(N));
                let r = _mm256_srl_epi64(self.0, _mm_cvtsi32_si128(64 - N));
                Self(_mm256_or_si256(l, r))
            }
        }
        #[inline(always)]
        fn chi(a: Self, b: Self, c: Self) -> Self {
            // SAFETY: the module's cfg enables avx2.
            Self(unsafe { _mm256_xor_si256(a.0, _mm256_andnot_si256(b.0, c.0)) })
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
        fn rotl<const N: i32>(self) -> Self {
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

    /// The generic `absorb` on eight inputs: each input's words in rows of eight, transposed into one register per
    /// word.
    #[cfg(target_feature = "avx512f")]
    #[inline(always)]
    pub(super) fn absorb(st: &mut [Avx512; STATE_LANES], inputs: &[u8], len: usize, at: usize, words: usize) {
        assert!(words <= RATE_LANES && at + 8 * words <= len);
        for g in 0..words.div_ceil(8) {
            let n = (words - 8 * g).min(8);
            let rows: [__m512i; 8] = core::array::from_fn(|l| {
                let row = &inputs[l * len + at + 64 * g..][..8 * n];
                // SAFETY: the module's cfg enables avx512f, and the mask reads the row's `n` words and no others.
                unsafe { _mm512_maskz_loadu_epi64(((1u32 << n) - 1) as __mmask8, row.as_ptr().cast()) }
            });
            for (lane, col) in st[8 * g..8 * g + n].iter_mut().zip(transpose8(rows)) {
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
        fn rotl<const N: i32>(self) -> Self {
            if N == 0 {
                return self;
            }
            // SAFETY: NEON is in the aarch64 baseline.
            unsafe {
                let l = vshlq_u64(self.0, vdupq_n_s64(N as i64));
                let r = vshlq_u64(self.0, vdupq_n_s64(N as i64 - 64));
                Self(vorrq_u64(l, r))
            }
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

    /// The generic `absorb` on two inputs: two words of each per load, `ZIP1` and `ZIP2` turning the two rows into
    /// two lanes.
    #[inline(always)]
    pub(super) fn absorb(st: &mut [Neon; STATE_LANES], inputs: &[u8], len: usize, at: usize, words: usize) {
        assert!(words <= RATE_LANES && at + 8 * words <= len);
        let (a, b) = (&inputs[at..][..8 * words], &inputs[len + at..][..8 * words]);
        for (p, (x, y)) in a.as_chunks::<16>().0.iter().zip(b.as_chunks::<16>().0).enumerate() {
            // SAFETY: `x` and `y` are 16 readable bytes each, and NEON is in the aarch64 baseline.
            unsafe {
                let (x, y) = (vld1q_u64(x.as_ptr().cast()), vld1q_u64(y.as_ptr().cast()));
                st[2 * p] = Neon(veorq_u64(st[2 * p].0, vzip1q_u64(x, y)));
                st[2 * p + 1] = Neon(veorq_u64(st[2 * p + 1].0, vzip2q_u64(x, y)));
            }
        }
        if words % 2 == 1 {
            let w = words - 1;
            let word = |input: &[u8]| u64::from_le_bytes(*input[8 * w..].first_chunk().unwrap());
            st[w] = st[w].xor(Neon::load(&[word(a), word(b)]));
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
