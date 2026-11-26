//! The permutation over any lane type, and the batched entry points that permute several states at once, one vector
//! register per state lane: AVX-512 (eight states), AVX2 (four), NEON on little-endian AArch64 (two, with the SHA3
//! instructions where the CPU has them), or one at a time elsewhere. Every batched function is byte-identical to its
//! one-input form.
//!
//! Each entry point takes the widest backend the CPU runs. With the `std` feature it asks the OS, so a build for the
//! architecture's baseline still uses every backend; without it, the build's target features decide.

use crate::{END_BIT, OUT_LEN, PAD_FIRST, RATE, RATE_LANES, RC, STATE_LANES, hash_from_state, keccak_f};
use core::mem::MaybeUninit;
use core::ops::Range;

/// One state lane across [`Lane::WIDTH`] states. The permutation is written once over this trait.
///
/// A vector backend's methods run its feature's instructions from safe code: only call code generic over one after
/// `cpu_has!` has found that feature, as `dispatch!` does.
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

    /// XOR the `words` little-endian words of every input from byte `at` on into `st[..words]`, input `l` at
    /// `inputs[l * len..]`.
    #[inline(always)]
    fn absorb(st: &mut [Self; STATE_LANES], inputs: &[u8], len: usize, at: usize, words: usize) {
        for (w, lane) in st[..words].iter_mut().enumerate() {
            *lane = lane.xor(gather(|l| {
                u64::from_le_bytes(*inputs[l * len + at + 8 * w..].first_chunk().unwrap())
            }));
        }
    }

    /// Every input's digest, the first [`OUT_LEN`] bytes of its state, input `l`'s at `out[l * OUT_LEN..]`.
    #[inline(always)]
    fn digests(st: &[Self; STATE_LANES], out: &mut [MaybeUninit<u8>]) {
        let mut words = [[0; MAX_WIDTH]; OUT_LEN / 8];
        for (words, &lane) in words.iter_mut().zip(st) {
            *words = scatter(lane);
        }
        for (l, digest) in out.as_chunks_mut::<OUT_LEN>().0.iter_mut().enumerate() {
            for (w, bytes) in digest.as_chunks_mut::<8>().0.iter_mut().enumerate() {
                bytes.write_copy_of_slice(&words[w][l].to_le_bytes());
            }
        }
    }
}

/// The widest [`Lane::WIDTH`].
pub(crate) const MAX_WIDTH: usize = 8;

/// The lane holding `f(l)` in state `l`.
#[inline(always)]
fn gather<S: Lane>(f: impl Fn(usize) -> u64) -> S {
    let mut words = [0; MAX_WIDTH];
    for (l, word) in words[..S::WIDTH].iter_mut().enumerate() {
        *word = f(l);
    }
    S::load(&words[..S::WIDTH])
}

/// Every state a copy of `state`.
#[inline(always)]
fn splat_all<S: Lane>(state: &[u64; STATE_LANES]) -> [S; STATE_LANES] {
    let mut st = [S::splat(0); STATE_LANES];
    for (lane, &x) in st.iter_mut().zip(state) {
        *lane = S::splat(x);
    }
    st
}

/// Every state's word of `lane`, in the first [`Lane::WIDTH`] entries.
#[inline(always)]
fn scatter<S: Lane>(lane: S) -> [u64; MAX_WIDTH] {
    let mut words = [0; MAX_WIDTH];
    lane.store(&mut words[..S::WIDTH]);
    words
}

// The permutation's pieces are functions, not closures: `dispatch!` enables a backend's target feature on one function,
// and a closure is a function of its own that LLVM may leave out of line, without the feature, where every vector
// operation becomes a call.

/// The column parities of `a`.
#[inline(always)]
fn parities<S: Lane>(a: &[S; STATE_LANES]) -> [S; 5] {
    [
        S::xor5(a[0], a[5], a[10], a[15], a[20]),
        S::xor5(a[1], a[6], a[11], a[16], a[21]),
        S::xor5(a[2], a[7], a[12], a[17], a[22]),
        S::xor5(a[3], a[8], a[13], a[18], a[23]),
        S::xor5(a[4], a[9], a[14], a[19], a[24]),
    ]
}

/// θ's effect on each column, from the column parities `c`.
#[inline(always)]
fn theta<S: Lane>(c: &[S; 5]) -> [S; 5] {
    let mut d = *c;
    for (x, d) in d.iter_mut().enumerate() {
        *d = S::theta_d(c[(x + 4) % 5], c[(x + 1) % 5]);
    }
    d
}

/// Lane `i` of `a` after θ.
#[inline(always)]
fn t<S: Lane>(a: &[S; STATE_LANES], d: &[S; 5], i: usize) -> S {
    a[i].xor(d[i % 5])
}

/// Output row `y`'s lanes before χ: the lanes π sends there, after θ, each rotated by its ρ. `y` is a constant at every
/// call, so the match folds away.
#[inline(always)]
fn pi_row<S: Lane>(a: &[S; STATE_LANES], d: &[S; 5], y: usize) -> [S; 5] {
    match y {
        0 => [
            t(a, d, 0),
            t(a, d, 6).rotl::<44>(),
            t(a, d, 12).rotl::<43>(),
            t(a, d, 18).rotl::<21>(),
            t(a, d, 24).rotl::<14>(),
        ],
        1 => [
            t(a, d, 3).rotl::<28>(),
            t(a, d, 9).rotl::<20>(),
            t(a, d, 10).rotl::<3>(),
            t(a, d, 16).rotl::<45>(),
            t(a, d, 22).rotl::<61>(),
        ],
        2 => [
            t(a, d, 1).rotl::<1>(),
            t(a, d, 7).rotl::<6>(),
            t(a, d, 13).rotl::<25>(),
            t(a, d, 19).rotl::<8>(),
            t(a, d, 20).rotl::<18>(),
        ],
        3 => [
            t(a, d, 4).rotl::<27>(),
            t(a, d, 5).rotl::<36>(),
            t(a, d, 11).rotl::<10>(),
            t(a, d, 17).rotl::<15>(),
            t(a, d, 23).rotl::<56>(),
        ],
        _ => [
            t(a, d, 2).rotl::<62>(),
            t(a, d, 8).rotl::<55>(),
            t(a, d, 14).rotl::<39>(),
            t(a, d, 15).rotl::<41>(),
            t(a, d, 21).rotl::<2>(),
        ],
    }
}

/// Output row `y` from its lanes before χ (`pi_row`), each rotated by its ρ: χ, ι on row 0, stored into `out` and folded
/// into the column parities `c`.
#[inline(always)]
fn chi_row<S: Lane>(out: &mut [S; STATE_LANES], c: &mut [S; 5], y: usize, [b0, b1, b2, b3, b4]: [S; 5], rc: u64) {
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
}

// The x86 rounds go in pairs, one into each state.
#[cfg(target_arch = "x86_64")]
const _: () = assert!(RC.len().is_multiple_of(2));

/// The 24 rounds of θ, ρ, π, χ and ι, on x86. Straight-line, so every rotation is an immediate and every lane a
/// register.
///
/// Each round reads one state and writes the other, a whole output row at a time: its five lanes, rotated by their ρ
/// from where π takes them, then χ, then the row is stored and folded into the next round's column parities. A row
/// at a time keeps about sixteen values live, which fits AVX2's sixteen registers, where forming all twenty-five lanes
/// before χ spills.
#[cfg(target_arch = "x86_64")]
#[inline(always)]
pub(crate) fn permute<S: Lane>(a: &mut [S; STATE_LANES]) {
    let mut c = parities(a);
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
    let mut c = parities(a);
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
    let d = theta(c);
    chi_row(out, c, 0, pi_row(a, &d, 0), rc);
    if ROWS > 1 {
        chi_row(out, c, 1, pi_row(a, &d, 1), rc);
    }
    if ROWS > 2 {
        chi_row(out, c, 2, pi_row(a, &d, 2), rc);
    }
    if ROWS > 3 {
        chi_row(out, c, 3, pi_row(a, &d, 3), rc);
    }
    if ROWS > 4 {
        chi_row(out, c, 4, pi_row(a, &d, 4), rc);
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
pub(crate) fn permute<S: Lane>(a: &mut [S; STATE_LANES]) {
    let mut c = parities(a);
    for &rc in &RC {
        let d = theta(&c);
        let rows = [
            pi_row(a, &d, 0),
            pi_row(a, &d, 1),
            pi_row(a, &d, 2),
            pi_row(a, &d, 3),
            pi_row(a, &d, 4),
        ];
        for (y, &row) in rows.iter().enumerate() {
            chi_row(a, &mut c, y, row, rc);
        }
    }
}

/// The whole [`permute`]: every lane comes out permuted, which covers the first row the callers read.
#[cfg(not(target_arch = "x86_64"))]
#[inline(always)]
pub(crate) fn permute_first_row<S: Lane>(a: &mut [S; STATE_LANES]) {
    permute(a);
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
        self.rotate_left(N as u32)
    }
    #[inline(always)]
    fn chi(a: Self, b: Self, c: Self) -> Self {
        a ^ (!b & c)
    }
}

/// Whether the CPU runs target feature `$f`: the OS's answer with `std`, else whether the build enables it.
#[cfg(any(
    all(target_arch = "x86_64", target_feature = "sse2"),
    all(target_arch = "aarch64", target_endian = "little", target_feature = "neon")
))]
macro_rules! cpu_has {
    ($f:tt) => {
        cfg_select! {
            all(feature = "std", target_arch = "x86_64") => std::arch::is_x86_feature_detected!($f),
            all(feature = "std", target_arch = "aarch64") => std::arch::is_aarch64_feature_detected!($f),
            _ => cfg!(target_feature = $f),
        }
    };
}

/// `$with::<S>(args)` on the widest backend `S` the CPU runs, inlined into a function compiled with its feature. Only
/// where the architecture's vector registers are in the baseline: a soft-float target (`x86_64-unknown-none`,
/// `aarch64-unknown-none-softfloat`) cannot enable a vector feature on a function, so it hashes one state at a time,
/// as big-endian AArch64 does, whose NEON loads would read the input's bytes as big-endian words. It returns from the
/// calling function, so it is that function's last expression.
macro_rules! dispatch {
    ($with:ident($($arg:ident: $ty:ty),* $(,)?) $(-> $ret:ty)?) => {
        dispatch!(@arch $with, ($($arg: $ty),*), ($($arg),*), ($($ret)?))
    };
    (@arch $with:ident, $params:tt, $args:tt, $ret:tt) => {
        cfg_select! {
            all(target_arch = "x86_64", target_feature = "sse2") => {
                dispatch!(@first $with, $params, $args, $ret; "avx512f" => x86::Avx512, "avx2" => x86::Avx2; u64)
            }
            all(target_arch = "aarch64", target_endian = "little", target_feature = "neon") => {
                dispatch!(@first $with, $params, $args, $ret; "sha3" => arm::Neon<true>; arm::Neon<false>)
            }
            _ => $with::<u64> $args,
        }
    };
    (@first $with:ident, $params:tt, $args:tt, $ret:tt; $($f:tt => $S:ty),*; $fallback:ty) => {{
        $(
            if cpu_has!($f) {
                // `$ret` is the return type in parentheses, `()` for none.
                #[allow(unused_parens, clippy::unused_unit)]
                #[target_feature(enable = $f)]
                fn with $params -> $ret {
                    $with::<$S> $args
                }
                // SAFETY: the CPU runs the feature `with` is compiled with.
                return unsafe { with $args };
            }
        )*
        $with::<$fallback> $args
    }};
}

/// How many states the batched entry points permute at once on this CPU. They take any count, and permute the
/// remainder one at a time.
pub fn lanes() -> usize {
    dispatch!(lanes_with() -> usize)
}

#[inline(always)]
fn lanes_with<S: Lane>() -> usize {
    S::WIDTH
}

/// Keccak-f\[1600\] of every state in place.
pub fn keccak_f_many(states: &mut [[u64; STATE_LANES]]) {
    dispatch!(keccak_f_many_with(states: &mut [[u64; STATE_LANES]]))
}

/// [`keccak_f_many`] on backend `S`, [`Lane::WIDTH`] states at a time and the remainder one at a time.
#[inline(always)]
fn keccak_f_many_with<S: Lane>(states: &mut [[u64; STATE_LANES]]) {
    let mut groups = states.chunks_exact_mut(S::WIDTH);
    for group in &mut groups {
        // Register `i` holds lane `i` of every state.
        let mut st = [S::splat(0); STATE_LANES];
        for (i, lane) in st.iter_mut().enumerate() {
            *lane = gather(|l| group[l][i]);
        }
        permute(&mut st);
        for (i, &lane) in st.iter().enumerate() {
            for (state, word) in group.iter_mut().zip(scatter(lane)) {
                state[i] = word;
            }
        }
    }
    groups.into_remainder().iter_mut().for_each(keccak_f);
}

/// The first of `nonces` that, written into lane `at` of `template`, leaves lane `out` of the permuted state zero under
/// `mask`.
pub fn first_nonce(template: &[u64; STATE_LANES], at: usize, nonces: Range<u64>, out: usize, mask: u64) -> Option<u64> {
    assert!(
        out < 5,
        "the tested lane is in the first row, all the permutation computes in full"
    );
    dispatch!(
        first_nonce_with(
            template: &[u64; STATE_LANES],
            at: usize,
            nonces: Range<u64>,
            out: usize,
            mask: u64,
        ) -> Option<u64>
    )
}

/// [`first_nonce`] on backend `S`, [`Lane::WIDTH`] nonces at a time.
#[inline(always)]
fn first_nonce_with<S: Lane>(
    template: &[u64; STATE_LANES],
    at: usize,
    nonces: Range<u64>,
    out: usize,
    mask: u64,
) -> Option<u64> {
    let template = splat_all::<S>(template);
    let mut first = nonces.start;
    while first < nonces.end {
        let mut st = template;
        st[at] = gather(|l| first.wrapping_add(l as u64));
        permute_first_row(&mut st);
        let n = (nonces.end - first).min(S::WIDTH as u64) as usize;
        if let Some(l) = scatter(st[out])[..n].iter().position(|w| w & mask == 0) {
            return Some(first + l as u64);
        }
        first = first.saturating_add(S::WIDTH as u64);
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
    // SAFETY: the hash writes only whole digests, so the bytes stay initialized.
    let out = unsafe { &mut *(out as *mut [u8] as *mut [MaybeUninit<u8>]) };
    hash_many_from_state_uninit(data, len, state, out);
}

/// [`hash_many_from_state`] into bytes not yet written, every one of which it writes.
pub fn hash_many_from_state_uninit(data: &[u8], len: usize, state: &[u64; STATE_LANES], out: &mut [MaybeUninit<u8>]) {
    let n = out.len() / OUT_LEN;
    assert_eq!((data.len(), out.len()), (n * len, n * OUT_LEN));
    dispatch!(hash_many_with(data: &[u8], len: usize, state: &[u64; STATE_LANES], out: &mut [MaybeUninit<u8>]))
}

/// [`hash_many_from_state`] on backend `S`, [`Lane::WIDTH`] inputs at a time and the remainder one at a time.
#[inline(always)]
fn hash_many_with<S: Lane>(data: &[u8], len: usize, state: &[u64; STATE_LANES], out: &mut [MaybeUninit<u8>]) {
    let n = out.len() / OUT_LEN;
    for (g, digests) in out.chunks_exact_mut(S::WIDTH * OUT_LEN).enumerate() {
        hash_group::<S>(&data[g * S::WIDTH * len..][..S::WIDTH * len], len, state, digests);
    }
    for i in n / S::WIDTH * S::WIDTH..n {
        out[i * OUT_LEN..][..OUT_LEN].write_copy_of_slice(&hash_from_state(&data[i * len..][..len], state));
    }
}

/// The digests of [`Lane::WIDTH`] inputs of `len` bytes, input `l` at `inputs[l * len..]`.
#[inline(always)]
fn hash_group<S: Lane>(inputs: &[u8], len: usize, state: &[u64; STATE_LANES], out: &mut [MaybeUninit<u8>]) {
    let mut st = splat_all::<S>(state);
    let (blocks, tail) = (len / RATE, len % RATE);
    for b in 0..blocks {
        S::absorb(&mut st, inputs, len, b * RATE, RATE_LANES);
        permute(&mut st);
    }
    // The final block: the tail's whole words, its last partial word, then the padding, the same in every input.
    let (words, part) = (tail / 8, tail % 8);
    S::absorb(&mut st, inputs, len, blocks * RATE, words);
    if part > 0 {
        let at = blocks * RATE + 8 * words;
        st[words] = st[words].xor(gather(|l| {
            let mut bytes = [0u8; 8];
            bytes[..part].copy_from_slice(&inputs[l * len + at..][..part]);
            u64::from_le_bytes(bytes)
        }));
    }
    st[words] = st[words].xor(S::splat(u64::from(PAD_FIRST) << (8 * part)));
    st[RATE_LANES - 1] = st[RATE_LANES - 1].xor(S::splat(END_BIT));
    permute_first_row(&mut st);
    S::digests(&st, out);
}

/// The first 128 bits of the digest, little endian, of `template`'s input with `values[i]` XORed into its lanes `at`
/// and `at + 1`, into `out[i]`. `template` is that input's [`final_state`](crate::final_state) with those 16 bytes
/// zero, so a value costs one permutation.
pub fn digest_halves_from(template: &[u64; STATE_LANES], at: usize, values: &[u128], out: &mut [u128]) {
    // The final block ends in padding, so the value stops before its last lane.
    assert!(at + 2 < RATE_LANES && values.len() == out.len());
    dispatch!(digest_halves_with(template: &[u64; STATE_LANES], at: usize, values: &[u128], out: &mut [u128]))
}

/// [`digest_halves_from`] on backend `S`, [`Lane::WIDTH`] values at a time and the remainder one at a time.
#[inline(always)]
fn digest_halves_with<S: Lane>(template: &[u64; STATE_LANES], at: usize, values: &[u128], out: &mut [u128]) {
    let groups = values.chunks_exact(S::WIDTH);
    let rest = groups.remainder();
    for (values, out) in groups.zip(out.chunks_exact_mut(S::WIDTH)) {
        let mut st = splat_all::<S>(template);
        for (j, shift) in [(0, 0), (1, 64)] {
            st[at + j] = st[at + j].xor(gather(|l| (values[l] >> shift) as u64));
        }
        permute_first_row(&mut st);
        let (lo, hi) = (scatter(st[0]), scatter(st[1]));
        for (l, out) in out.iter_mut().enumerate() {
            *out = u128::from(lo[l]) | u128::from(hi[l]) << 64;
        }
    }
    for (&value, out) in rest.iter().zip(&mut out[values.len() - rest.len()..]) {
        let mut state = *template;
        state[at] ^= value as u64;
        state[at + 1] ^= (value >> 64) as u64;
        keccak_f(&mut state);
        *out = u128::from(state[0]) | u128::from(state[1]) << 64;
    }
}

/// The x86 backends. Their methods run only once `cpu_has!` has found their feature: inlined into the function
/// `dispatch!` compiles with it, or out of line in tests.
#[cfg(all(target_arch = "x86_64", target_feature = "sse2"))]
mod x86 {
    use super::Lane;
    use crate::{RATE_LANES, STATE_LANES};
    use core::arch::x86_64::*;

    /// Four states in a YMM register. No 64-bit rotate before AVX-512, so a rotation is a shift pair.
    #[derive(Clone, Copy)]
    pub(super) struct Avx2(__m256i);

    impl Lane for Avx2 {
        const WIDTH: usize = 4;

        #[inline(always)]
        fn load(src: &[u64]) -> Self {
            let src: &[u64; 4] = src.try_into().unwrap();
            // SAFETY: avx2 is on (see the module), and `src` is 32 readable bytes.
            Self(unsafe { _mm256_loadu_si256(src.as_ptr().cast()) })
        }
        #[inline(always)]
        fn store(self, dst: &mut [u64]) {
            let dst: &mut [u64; 4] = dst.try_into().unwrap();
            // SAFETY: avx2 is on (see the module), and `dst` is 32 writable bytes.
            unsafe { _mm256_storeu_si256(dst.as_mut_ptr().cast(), self.0) }
        }
        #[inline(always)]
        fn splat(x: u64) -> Self {
            // SAFETY: avx2 is on (see the module).
            Self(unsafe { _mm256_set1_epi64x(x as i64) })
        }
        #[inline(always)]
        fn xor(self, o: Self) -> Self {
            // SAFETY: avx2 is on (see the module).
            Self(unsafe { _mm256_xor_si256(self.0, o.0) })
        }
        #[inline(always)]
        fn rotl<const N: i32>(self) -> Self {
            if N == 0 {
                return self;
            }
            // SAFETY: avx2 is on (see the module).
            unsafe {
                let l = if N == 1 {
                    _mm256_add_epi64(self.0, self.0)
                } else {
                    _mm256_sll_epi64(self.0, _mm_cvtsi32_si128(N))
                };
                let r = _mm256_srl_epi64(self.0, _mm_cvtsi32_si128(64 - N));
                Self(_mm256_or_si256(l, r))
            }
        }
        #[inline(always)]
        fn chi(a: Self, b: Self, c: Self) -> Self {
            // SAFETY: avx2 is on (see the module).
            Self(unsafe { _mm256_xor_si256(a.0, _mm256_andnot_si256(b.0, c.0)) })
        }
    }

    /// Eight states in a ZMM register, with a native rotate and `vpternlogq` for χ and the column parity.
    #[derive(Clone, Copy)]
    pub(super) struct Avx512(__m512i);

    impl Lane for Avx512 {
        const WIDTH: usize = 8;

        #[inline(always)]
        fn load(src: &[u64]) -> Self {
            let src: &[u64; 8] = src.try_into().unwrap();
            // SAFETY: avx512f is on (see the module), and `src` is 64 readable bytes.
            Self(unsafe { _mm512_loadu_si512(src.as_ptr().cast()) })
        }
        #[inline(always)]
        fn store(self, dst: &mut [u64]) {
            let dst: &mut [u64; 8] = dst.try_into().unwrap();
            // SAFETY: avx512f is on (see the module), and `dst` is 64 writable bytes.
            unsafe { _mm512_storeu_si512(dst.as_mut_ptr().cast(), self.0) }
        }
        #[inline(always)]
        fn splat(x: u64) -> Self {
            // SAFETY: avx512f is on (see the module).
            Self(unsafe { _mm512_set1_epi64(x as i64) })
        }
        #[inline(always)]
        fn xor(self, o: Self) -> Self {
            // SAFETY: avx512f is on (see the module).
            Self(unsafe { _mm512_xor_si512(self.0, o.0) })
        }
        #[inline(always)]
        fn rotl<const N: i32>(self) -> Self {
            // SAFETY: avx512f is on (see the module).
            Self(unsafe { _mm512_rol_epi64::<N>(self.0) })
        }
        #[inline(always)]
        fn chi(a: Self, b: Self, c: Self) -> Self {
            // The truth table of `a ^ (!b & c)` over (a, b, c) = (0xF0, 0xCC, 0xAA).
            // SAFETY: avx512f is on (see the module).
            Self(unsafe { _mm512_ternarylogic_epi64::<0xD2>(a.0, b.0, c.0) })
        }
        #[inline(always)]
        fn xor5(a: Self, b: Self, c: Self, d: Self, e: Self) -> Self {
            // SAFETY: avx512f is on (see the module).
            unsafe {
                let t = _mm512_ternarylogic_epi64::<0x96>(a.0, b.0, c.0);
                Self(_mm512_ternarylogic_epi64::<0x96>(t, d.0, e.0))
            }
        }
        /// `absorb` on eight inputs: each input's words in rows of eight, transposed into one register per
        /// word.
        #[inline(always)]
        fn absorb(st: &mut [Self; STATE_LANES], inputs: &[u8], len: usize, at: usize, words: usize) {
            assert!(words <= RATE_LANES && at + 8 * words <= len);
            for g in 0..words.div_ceil(8) {
                let n = (words - 8 * g).min(8);
                // SAFETY: avx512f is on (see the module).
                let mut rows = [unsafe { _mm512_setzero_si512() }; 8];
                for (l, row) in rows.iter_mut().enumerate() {
                    let bytes = &inputs[l * len + at + 64 * g..][..8 * n];
                    // SAFETY: avx512f is on (see the module), and the mask reads the row's `n` words and no others.
                    *row = unsafe { _mm512_maskz_loadu_epi64(((1u32 << n) - 1) as __mmask8, bytes.as_ptr().cast()) };
                }
                for (lane, col) in st[8 * g..8 * g + n].iter_mut().zip(transpose8(rows)) {
                    *lane = lane.xor(Avx512(col));
                }
            }
        }

        /// `digests` on eight inputs: the four digest lanes transposed into rows, two inputs' rows per store.
        #[inline(always)]
        fn digests(st: &[Self; STATE_LANES], out: &mut [core::mem::MaybeUninit<u8>]) {
            // SAFETY: avx512f is on (see the module).
            let zero = unsafe { _mm512_setzero_si512() };
            let rows = transpose8([st[0].0, st[1].0, st[2].0, st[3].0, zero, zero, zero, zero]);
            for ([first, second], bytes) in rows.as_chunks::<2>().0.iter().zip(out.as_chunks_mut::<64>().0) {
                // SAFETY: avx512f is on (see the module), and `bytes` is 64 writable bytes.
                unsafe { _mm512_storeu_si512(bytes.as_mut_ptr().cast(), _mm512_shuffle_i64x2::<0x44>(*first, *second)) }
            }
        }
    }

    /// The 8x8 transpose of 64-bit words: word `j` of row `i` becomes word `i` of row `j`.
    #[inline(always)]
    fn transpose8(r: [__m512i; 8]) -> [__m512i; 8] {
        // SAFETY: avx512f is on (see the module).
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

#[cfg(all(target_arch = "aarch64", target_endian = "little", target_feature = "neon"))]
mod arm {
    use super::Lane;
    use crate::{RATE_LANES, STATE_LANES};
    use core::arch::aarch64::*;

    /// Two states in a NEON register. With `SHA3`, χ is one `BCAX`, the column parity two `EOR3` and θ's
    /// rotate-and-XOR one `RAX1`, so its methods run only once `cpu_has!` has found sha3: inlined into the
    /// function `dispatch!` compiles with it, or out of line in tests.
    #[derive(Clone, Copy)]
    pub(super) struct Neon<const SHA3: bool>(uint64x2_t);

    impl<const SHA3: bool> Lane for Neon<SHA3> {
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
            if SHA3 {
                // BCAX(a, c, b) = a ^ (c & !b).
                // SAFETY: sha3 is on (see the type).
                return Self(unsafe { vbcaxq_u64(a.0, c.0, b.0) });
            }
            // SAFETY: NEON is in the aarch64 baseline.
            Self(unsafe { veorq_u64(a.0, vbicq_u64(c.0, b.0)) })
        }
        #[inline(always)]
        fn xor5(a: Self, b: Self, c: Self, d: Self, e: Self) -> Self {
            if SHA3 {
                // SAFETY: sha3 is on (see the type).
                return Self(unsafe { veor3q_u64(veor3q_u64(a.0, b.0, c.0), d.0, e.0) });
            }
            a.xor(b).xor(c).xor(d).xor(e)
        }
        #[inline(always)]
        fn theta_d(c_prev: Self, c_next: Self) -> Self {
            if SHA3 {
                // SAFETY: sha3 is on (see the type).
                return Self(unsafe { vrax1q_u64(c_prev.0, c_next.0) });
            }
            c_prev.xor(c_next.rotl::<1>())
        }
        /// `absorb` on two inputs: two words of each per load, `ZIP1` and `ZIP2` turning the two rows into
        /// two lanes.
        #[inline(always)]
        fn absorb(st: &mut [Self; STATE_LANES], inputs: &[u8], len: usize, at: usize, words: usize) {
            assert!(words <= RATE_LANES && at + 8 * words <= len);
            let (a, b) = (&inputs[at..][..8 * words], &inputs[len + at..][..8 * words]);
            for (p, (x, y)) in a.as_chunks::<16>().0.iter().zip(b.as_chunks::<16>().0).enumerate() {
                // SAFETY: `x` and `y` are 16 readable bytes each, and NEON is in the aarch64 baseline.
                unsafe {
                    let (x, y) = (vld1q_u64(x.as_ptr().cast()), vld1q_u64(y.as_ptr().cast()));
                    st[2 * p] = Self(veorq_u64(st[2 * p].0, vzip1q_u64(x, y)));
                    st[2 * p + 1] = Self(veorq_u64(st[2 * p + 1].0, vzip2q_u64(x, y)));
                }
            }
            if words % 2 == 1 {
                let w = words - 1;
                let word = |input: &[u8]| u64::from_le_bytes(*input[8 * w..].first_chunk().unwrap());
                st[w] = st[w].xor(Self::load(&[word(a), word(b)]));
            }
        }

        /// `digests` on two inputs: `ZIP1` of two digest lanes is two words of the first input, `ZIP2` of
        /// the second.
        #[inline(always)]
        fn digests(st: &[Self; STATE_LANES], out: &mut [core::mem::MaybeUninit<u8>]) {
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
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Every batched entry point on backend `S` against one state at a time: whole groups and a remainder.
    fn matches_the_scalar_backend<S: Lane>() {
        let name = core::any::type_name::<S>();
        let w = MAX_WIDTH as u64;
        let template: [u64; STATE_LANES] = core::array::from_fn(|i| (i as u64).wrapping_mul(0x9E37_79B9_7F4A_7C15));

        let states: Vec<[u64; STATE_LANES]> = (0..2 * w + 1).map(|l| template.map(|x| x ^ (l << 32))).collect();
        let (mut got, mut want) = (states.clone(), states);
        keccak_f_many_with::<S>(&mut got);
        keccak_f_many_with::<u64>(&mut want);
        assert_eq!(got, want, "{name} keccak_f_many");

        for start in 0..2 * w {
            for end in start..start + 3 * w {
                assert_eq!(
                    first_nonce_with::<S>(&template, 4, start..end, 2, 0xf),
                    first_nonce_with::<u64>(&template, 4, start..end, 2, 0xf),
                    "{name} first_nonce {start}..{end}"
                );
            }
        }

        for len in [0usize, 8, 64, 135, 136, 137, 408] {
            let n = 2 * w as usize + 1;
            let data: Vec<u8> = (0..n * len).map(|i| (i * 31 + len) as u8).collect();
            let mut got = vec![MaybeUninit::uninit(); n * OUT_LEN];
            let mut want = vec![MaybeUninit::uninit(); n * OUT_LEN];
            hash_many_with::<S>(&data, len, &template, &mut got);
            hash_many_with::<u64>(&data, len, &template, &mut want);
            // SAFETY: the hash writes every byte of its output.
            let (got, want) = unsafe { (got.assume_init_ref(), want.assume_init_ref()) };
            assert_eq!(got, want, "{name} hash_many {len}");
        }

        let values: Vec<u128> = (1..4 * w as u128 + 4)
            .map(|i| i * 0x9E37_79B9_7F4A_7C15_F39C_C060)
            .collect();
        let (mut got, mut want) = (vec![0; values.len()], vec![0; values.len()]);
        digest_halves_with::<S>(&template, 3, &values, &mut got);
        digest_halves_with::<u64>(&template, 3, &values, &mut want);
        assert_eq!(got, want, "{name} digest_halves_from");
    }

    /// The entry points pick the widest backend the CPU runs, not a narrower one.
    #[test]
    fn the_widest_backend_runs() {
        let widest = cfg_select! {
            all(target_arch = "x86_64", target_feature = "sse2") => {
                if cpu_has!("avx512f") { 8 } else if cpu_has!("avx2") { 4 } else { 1 }
            }
            all(target_arch = "aarch64", target_endian = "little", target_feature = "neon") => 2,
            _ => 1,
        };
        assert_eq!(lanes(), widest);
    }

    /// Every backend this CPU runs, each of which the entry points may pick.
    #[test]
    fn every_backend_matches_the_scalar_one() {
        #[cfg(all(target_arch = "x86_64", target_feature = "sse2"))]
        {
            if cpu_has!("avx2") {
                matches_the_scalar_backend::<x86::Avx2>();
            }
            if cpu_has!("avx512f") {
                matches_the_scalar_backend::<x86::Avx512>();
            }
        }
        #[cfg(all(target_arch = "aarch64", target_endian = "little", target_feature = "neon"))]
        {
            matches_the_scalar_backend::<arm::Neon<false>>();
            if cpu_has!("sha3") {
                matches_the_scalar_backend::<arm::Neon<true>>();
            }
        }
    }
}
