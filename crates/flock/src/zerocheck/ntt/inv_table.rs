// CREDIT: https://github.com/succinctlabs/flock (flock-core), MIT OR Apache-2.0.
//! §2.1 single-table collapse of the LDE matrix `M = fwd_NTT_Λ ∘ inv_NTT_S`.
//!
//! Background: the URM round-1 needs to map each `ell`-bit row of the boolean
//! witness (packed as `n_chunks = ell/8` bytes) to `ell` evaluations on the
//! NTT domain `Λ`. The naive way computes inv_NTT on S then fwd_NTT on Λ for
//! every row, which is too slow.
//!
//! The optimization (§2.1 of the paper): `M = α · M̃` with `M̃` Cauchy and `α`
//! a scalar. The columns of `M` satisfy a XOR-shift relation, so the `n_chunks`
//! per-byte sub-tables collapse to a single 256-row base table `T_0`:
//!
//!   M[i', 8b + t]  =  T_0[bit-t-mask(8b+t)][i' ⊕ 8b]
//!
//! Per-byte-chunk b contributes `π_b(T_0[byte_b])` to the output, where
//! `π_b(i') = i' ⊕ 8b`.
//!
//! Storage: 256 × ell bytes (16 KB at k=6, 32 KB at k=7), which fits in L1.
//! Lookups per row: n_chunks (= ell/8), each load is `ell` contiguous bytes.

use primitives::PrimeCharacteristicRing;

use super::AdditiveNttGf8;
#[cfg(all(target_arch = "x86_64", target_feature = "avx2"))]
use core::arch::x86_64::*;
use primitives::{F8, F64, F192, phi8_192};

#[derive(Clone, Debug)]
pub(crate) struct InvNttTableByteSingleGf8 {
    pub(crate) k: usize,
    pub(crate) ell: usize,
    pub(crate) n_chunks: usize,
    /// `data[w * ell .. (w+1) * ell]` = T_0[w], the XOR-sum of columns of `M`
    /// indexed by the set bits of `w`.
    data: Vec<F8>,
    /// The same S/Λ butterflies, lifted through φ₈ into the base field, for
    /// extending the reduced E-valued C vector without Boolean bit planes.
    twiddles: Vec<F64>,
}

impl InvNttTableByteSingleGf8 {
    /// Build the table given the two NTT instances: `ntt_S` over the input
    /// domain, `ntt_L` over the output (extension) domain. Both must have the
    /// same `k`.
    pub(crate) fn new(ntt_s: &AdditiveNttGf8, ntt_l: &AdditiveNttGf8) -> Self {
        assert_eq!(ntt_s.k(), ntt_l.k(), "ntt_S and ntt_L must share k");
        let k = ntt_s.k();
        let ell = 1usize << k;
        assert!(ell >= 8, "ell must be ≥ 8 so n_chunks ≥ 1");
        let n_chunks = ell / 8;
        assert!(n_chunks <= 16, "n_chunks must fit the i'/chunk XOR encoding");

        let mut data = vec![F8::ZERO; 256 * ell];

        // Compute the 8 unit-column images cols[t] = fwd_NTT_Λ ∘ inv_NTT_S (e_t)
        // for t ∈ 0..8. The remaining columns of M are XOR-shifted versions.
        let mut tmp = vec![F8::ZERO; ell];
        let mut cols: Vec<Vec<F8>> = Vec::with_capacity(8);
        for t in 0..8 {
            tmp.iter_mut().for_each(|x| *x = F8::ZERO);
            tmp[t] = F8::ONE;
            ntt_s.inverse(&mut tmp);
            ntt_l.forward(&mut tmp);
            cols.push(tmp.clone());
        }

        // T_0[0] already zero. T_0[2^t] = cols[t]. Then for non-power-of-two w,
        // T_0[w] = T_0[w ^ lo_bit] ⊕ T_0[lo_bit]; this builds all 256 entries
        // with one XOR per entry.
        for (t, col) in cols.iter().enumerate() {
            let entry_start = (1usize << t) * ell;
            data[entry_start..entry_start + ell].copy_from_slice(col);
        }
        for w in 3usize..256 {
            if (w & (w - 1)) == 0 {
                continue; // skip powers of 2 (already written)
            }
            let lo_bit = 1usize << w.trailing_zeros();
            let parent = w ^ lo_bit;
            // Borrow-checker friendly: read parent + bit_v slices, then write entry.
            let (parent_off, bit_off, entry_off) = (parent * ell, lo_bit * ell, w * ell);
            for i in 0..ell {
                let v = data[parent_off + i] + data[bit_off + i];
                data[entry_off + i] = v;
            }
        }

        Self {
            k,
            ell,
            n_chunks,
            data,
            twiddles: ntt_s
                .twiddles
                .iter()
                .chain(&ntt_l.twiddles)
                .map(|&t| F64::new(phi8_192(t).coefficients()[0].to_bits()))
                .collect(),
        }
    }

    /// Extend E-valued evaluations from S to Λ in place. The GF8 embedding
    /// lies in K, so each butterfly multiplies the three E limbs by one K
    /// twiddle. These are the original GF8 domains and LCH basis, not the
    /// polynomial-basis domains of the GF64 NTT.
    pub(crate) fn extend_lifted(&self, v: &mut [F192]) {
        assert_eq!(v.len(), self.ell);
        let (twiddles_s, twiddles_l) = self.twiddles.split_at(self.ell - 1);

        // Inverse on S: children before parents in the twiddle tree.
        for level in (0..self.k).rev() {
            let nodes = 1usize << level;
            let size = self.ell >> level;
            let twiddles = &twiddles_s[nodes - 1..2 * nodes - 1];
            for (block, &lambda) in v.chunks_exact_mut(size).zip(twiddles) {
                let (lo, hi) = block.split_at_mut(size / 2);
                if lambda == F64::ZERO {
                    for (a, b) in lo.iter().zip(hi) {
                        *b += *a;
                    }
                } else {
                    for (a, b) in lo.iter_mut().zip(hi) {
                        *b += *a;
                        *a += *b * lambda;
                    }
                }
            }
        }

        // Forward on Λ: parents before children, with the same point order.
        for level in 0..self.k {
            let nodes = 1usize << level;
            let size = self.ell >> level;
            let twiddles = &twiddles_l[nodes - 1..2 * nodes - 1];
            for (block, &lambda) in v.chunks_exact_mut(size).zip(twiddles) {
                let (lo, hi) = block.split_at_mut(size / 2);
                if lambda == F64::ZERO {
                    for (a, b) in lo.iter().zip(hi) {
                        *b += *a;
                    }
                } else {
                    for (a, b) in lo.iter_mut().zip(hi) {
                        *a += *b * lambda;
                        *b += *a;
                    }
                }
            }
        }
    }

    /// Apply M to a single byte-packed row, in place.
    /// `bytes` is `n_chunks` bytes (the LCH-coefficient bits of the row);
    /// `out` will be filled with the `ell` evaluations on Λ.
    ///
    /// Dispatches: NEON on aarch64 / SSE2 on x86_64 when `ell ≥ 16`, which
    /// covers every supported arch at the protocol size (k_skip=6 ⇒ ell=64).
    /// The scalar arm is reachable only at `ell < 16`, i.e. k=3, which occurs
    /// only in tests.
    #[inline]
    pub(crate) fn apply(&self, bytes: &[u8], out: &mut [F8]) {
        #[cfg(target_arch = "aarch64")]
        if self.ell >= 16 {
            // SAFETY: aarch64 statically guarantees NEON; ell ≥ 16 ⇒ at least
            // one 128-bit chunk; method validates slice lengths.
            unsafe { self.apply_v128::<Neon>(bytes, out) };
            return;
        }
        #[cfg(all(target_arch = "x86_64", target_feature = "avx512f"))]
        if self.ell == 64 {
            // SAFETY: avx512f is enabled at compile time; the method validates
            // slice lengths and requires exactly this `ell`.
            unsafe { self.apply_avx512(bytes, out) };
            return;
        }
        #[cfg(all(target_arch = "x86_64", target_feature = "avx2", not(target_feature = "avx512f")))]
        if self.ell == 64 {
            // SAFETY: avx2 is enabled at compile time; the method validates
            // slice lengths and requires exactly this `ell`.
            unsafe { self.apply_avx2(bytes, out) };
            return;
        }
        #[cfg(target_arch = "x86_64")]
        if self.ell >= 16 {
            // SAFETY: x86_64 statically guarantees SSE2; ell ≥ 16 ⇒ at least
            // one 128-bit chunk; method validates slice lengths.
            unsafe { self.apply_v128::<Sse2>(bytes, out) };
            return;
        }
        self.apply_scalar(bytes, out);
    }

    /// [`apply`](Self::apply) at the protocol's `ell = 64`, one register wide.
    ///
    /// # Safety
    /// Requires AVX-512F, and `self.ell` must be 64. The method validates slice
    /// lengths.
    #[cfg(all(target_arch = "x86_64", target_feature = "avx512f"))]
    #[inline]
    #[target_feature(enable = "avx512f")]
    unsafe fn apply_avx512(&self, bytes: &[u8], out: &mut [F8]) {
        assert_eq!(out.len(), self.ell);
        let bytes: &[u8; 8] = bytes.try_into().expect("8 bytes at ell = 64");
        // SAFETY: the single store covers exactly `out`.
        unsafe { _mm512_storeu_si512(out.as_mut_ptr().cast(), self.apply_zmm(bytes)) };
    }

    /// The 64 evaluations of one 8-byte row as one ZMM, at `ell = 64`.
    ///
    /// Byte `b`'s row enters permuted by `i' ⊕ 8b`, an XOR of `b` on the qword index.
    /// The rows are summed as a tree, so each bit of `b` is one fixed shuffle:
    /// bit 0 swaps the qwords of each 128-bit lane, bits 1 and 2 swap lanes, and only those two cross a lane.
    ///
    /// # Panics
    /// Panics unless `self.ell` is 64.
    ///
    /// # Safety
    /// Requires AVX-512F, which the target enables wherever this is compiled.
    #[cfg(all(target_arch = "x86_64", target_feature = "avx512f"))]
    #[inline]
    #[target_feature(enable = "avx512f")]
    pub(crate) fn apply_zmm(&self, bytes: &[u8; 8]) -> __m512i {
        assert_eq!(self.ell, 64);
        let base = self.data.as_ptr().cast::<u8>();
        // SAFETY: every row offset is `byte * 64` into a `256 * 64` table.
        let row = |b: usize| unsafe { _mm512_loadu_si512(base.add(bytes[b] as usize * 64).cast()) };
        let swap_qwords = |v| _mm512_shuffle_epi32::<0x4E>(v);
        let swap_lanes = |v| _mm512_shuffle_i64x2::<0xB1>(v, v);
        let swap_halves = |v| _mm512_shuffle_i64x2::<0x4E>(v, v);
        let pair = |b: usize| _mm512_xor_si512(row(b), swap_qwords(row(b + 1)));
        let lo = _mm512_xor_si512(pair(0), swap_lanes(pair(2)));
        let hi = _mm512_xor_si512(pair(4), swap_lanes(pair(6)));
        _mm512_xor_si512(lo, swap_halves(hi))
    }

    /// [`apply`](Self::apply) at the protocol's `ell = 64`, two registers wide.
    ///
    /// The `i' ⊕ 8b` permutation is a qword-index XOR by `b`: bit 0 swaps the qwords of each lane, bit 1 the lanes, bit 2
    /// the registers.
    ///
    /// # Safety
    /// Requires AVX2, and `self.ell` must be 64. The method validates slice
    /// lengths.
    #[cfg(all(target_arch = "x86_64", target_feature = "avx2"))]
    #[cfg_attr(target_feature = "avx512f", allow(dead_code))]
    #[inline]
    #[target_feature(enable = "avx2")]
    unsafe fn apply_avx2(&self, bytes: &[u8], out: &mut [F8]) {
        assert_eq!(self.ell, 64);
        assert_eq!(bytes.len(), self.n_chunks);
        assert_eq!(out.len(), self.ell);
        // SAFETY: every row offset is `byte * 64` into a `256 * 64` table, and
        // the two stores cover exactly `out`.
        unsafe {
            let base = self.data.as_ptr().cast::<u8>();
            let row = |b: usize| {
                let p = base.add(bytes[b] as usize * 64);
                (_mm256_loadu_si256(p.cast()), _mm256_loadu_si256(p.add(32).cast()))
            };
            let (mut lo, mut hi) = row(0);
            for b in 1..8 {
                let (mut l, mut h) = row(b);
                if b & 1 != 0 {
                    (l, h) = (
                        _mm256_shuffle_epi32::<0b01_00_11_10>(l),
                        _mm256_shuffle_epi32::<0b01_00_11_10>(h),
                    );
                }
                if b & 2 != 0 {
                    (l, h) = (
                        _mm256_permute4x64_epi64::<0b01_00_11_10>(l),
                        _mm256_permute4x64_epi64::<0b01_00_11_10>(h),
                    );
                }
                if b & 4 != 0 {
                    (l, h) = (h, l);
                }
                lo = _mm256_xor_si256(lo, l);
                hi = _mm256_xor_si256(hi, h);
            }
            let dst = out.as_mut_ptr().cast::<u8>();
            _mm256_storeu_si256(dst.cast(), lo);
            _mm256_storeu_si256(dst.add(32).cast(), hi);
        }
    }

    /// Scalar reference. Kept public so tests can use it as the cross-check
    /// oracle for the NEON variant.
    pub(crate) fn apply_scalar(&self, bytes: &[u8], out: &mut [F8]) {
        assert_eq!(bytes.len(), self.n_chunks);
        assert_eq!(out.len(), self.ell);
        out.iter_mut().for_each(|x| *x = F8::ZERO);
        for (b, &byte_b) in bytes.iter().enumerate() {
            let row_off = byte_b as usize * self.ell;
            let row = &self.data[row_off..row_off + self.ell];
            let shift = 8 * b;
            for i in 0..self.ell {
                out[i] += row[i ^ shift];
            }
        }
    }

    /// SIMD variant of `apply`, operating in 16-byte chunks.
    ///
    /// For each output chunk `c ∈ 0..ell/16`:
    ///   * `b = 0`: straight 16-byte copy from `row0[c]`
    ///   * `b ≥ 1`: load `row_b[c ⊕ (b>>1)]`, half-swap if `b` is odd, XOR
    ///
    /// The `b>>1` chunk-XOR and the `8 · b` within-chunk shift together
    /// implement the `π_b(i') = i' ⊕ 8b` permutation that the §2.1 collapse
    /// requires.
    ///
    /// This is the URM round-1 inner loop and it must inline into flock's
    /// `shift_reduce_inner_ab_gfni`, hence `#[inline(always)]` here and on
    /// every [`Vec128`] method.
    ///
    /// # Safety
    /// `V`'s target features must be available (statically true at the
    /// dispatch site for both NEON on aarch64 and SSE2 on x86_64). The method
    /// validates slice lengths.
    #[cfg(any(target_arch = "aarch64", target_arch = "x86_64"))]
    #[inline(always)]
    unsafe fn apply_v128<V: Vec128>(&self, bytes: &[u8], out: &mut [F8]) {
        assert_eq!(bytes.len(), self.n_chunks);
        assert_eq!(out.len(), self.ell);
        let n128 = self.ell / 16; // 4 for ell = 64
        let base = self.data.as_ptr() as *const u8;
        let out_ptr = out.as_mut_ptr() as *mut u8;

        // SAFETY: the caller guarantees `V`'s features. `data` is `256 * ell` bytes and each row index is a byte, so
        // row `bytes[b] * ell` has `ell` bytes; `ell` is a power of two, `n128 = ell / 16` and
        // `b >> 1 <= (n_chunks - 1) / 2 < n128`, so every chunk index `c ^ (b >> 1)` stays below `n128`, and each
        // 16-byte access lies inside its row or inside `out`, whose length is asserted to be `ell`.
        unsafe {
            // b = 0: identity permutation, a straight copy from row 0.
            let row0 = base.add(bytes[0] as usize * self.ell);
            for c in 0..n128 {
                V::store(out_ptr.add(c * 16), V::load(row0.add(c * 16)));
            }

            // b ≥ 1: XOR with table row[bytes[b]], permuted.
            for (b, &byte) in bytes.iter().enumerate().take(self.n_chunks).skip(1) {
                let b_high = b >> 1;
                let b_odd = (b & 1) != 0;
                let row_b = base.add(byte as usize * self.ell);
                if b_odd {
                    for c in 0..n128 {
                        let v = V::load(row_b.add((c ^ b_high) * 16)).swap64();
                        let dst = out_ptr.add(c * 16);
                        V::store(dst, V::load(dst).xor(v));
                    }
                } else {
                    for c in 0..n128 {
                        let v = V::load(row_b.add((c ^ b_high) * 16));
                        let dst = out_ptr.add(c * 16);
                        V::store(dst, V::load(dst).xor(v));
                    }
                }
            }
        }
    }
}

/// The four inlined 128-bit primitives used by `apply_v128`'s inner loop.
#[cfg(any(target_arch = "aarch64", target_arch = "x86_64"))]
trait Vec128: Copy {
    /// # Safety
    /// `p` must be readable for 16 bytes (alignment not required).
    unsafe fn load(p: *const u8) -> Self;
    /// # Safety
    /// `p` must be writable for 16 bytes (alignment not required).
    unsafe fn store(p: *mut u8, v: Self);
    fn xor(self, other: Self) -> Self;
    /// Swap the two 64-bit halves.
    fn swap64(self) -> Self;
}

#[cfg(target_arch = "aarch64")]
#[derive(Clone, Copy)]
struct Neon(core::arch::aarch64::uint8x16_t);

#[cfg(target_arch = "aarch64")]
impl Vec128 for Neon {
    #[inline(always)]
    unsafe fn load(p: *const u8) -> Self {
        // SAFETY: NEON is part of the aarch64 baseline, and the caller guarantees 16 readable bytes at `p`.
        Self(unsafe { core::arch::aarch64::vld1q_u8(p) })
    }
    #[inline(always)]
    unsafe fn store(p: *mut u8, v: Self) {
        // SAFETY: NEON is part of the aarch64 baseline, and the caller guarantees 16 writable bytes at `p`.
        unsafe { core::arch::aarch64::vst1q_u8(p, v.0) }
    }
    #[inline(always)]
    fn xor(self, other: Self) -> Self {
        // SAFETY: NEON is part of the aarch64 baseline; registers only.
        Self(unsafe { core::arch::aarch64::veorq_u8(self.0, other.0) })
    }
    #[inline(always)]
    fn swap64(self) -> Self {
        // SAFETY: NEON is part of the aarch64 baseline; registers only.
        Self(unsafe { core::arch::aarch64::vextq_u8::<8>(self.0, self.0) })
    }
}

#[cfg(target_arch = "x86_64")]
#[derive(Clone, Copy)]
struct Sse2(core::arch::x86_64::__m128i);

#[cfg(target_arch = "x86_64")]
impl Vec128 for Sse2 {
    #[inline(always)]
    unsafe fn load(p: *const u8) -> Self {
        // SAFETY: SSE2 is part of the x86-64 baseline, and the caller guarantees 16 readable bytes at `p`;
        // the load is unaligned.
        Self(unsafe { core::arch::x86_64::_mm_loadu_si128(p as *const core::arch::x86_64::__m128i) })
    }
    #[inline(always)]
    unsafe fn store(p: *mut u8, v: Self) {
        // SAFETY: SSE2 is part of the x86-64 baseline, and the caller guarantees 16 writable bytes at `p`;
        // the store is unaligned.
        unsafe { core::arch::x86_64::_mm_storeu_si128(p as *mut core::arch::x86_64::__m128i, v.0) }
    }
    #[inline(always)]
    fn xor(self, other: Self) -> Self {
        // SAFETY: SSE2 is part of the x86-64 baseline; registers only.
        unsafe { Self(core::arch::x86_64::_mm_xor_si128(self.0, other.0)) }
    }
    #[inline(always)]
    fn swap64(self) -> Self {
        // SAFETY: SSE2 is part of the x86-64 baseline; registers only.
        unsafe { Self(core::arch::x86_64::_mm_shuffle_epi32::<0b01_00_11_10>(self.0)) }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use primitives::PrimeCharacteristicRing;
    use primitives::test_util::Rng;

    /// Naive reference: unpack `bytes` into `ell` GF(2)-valued F8 elements
    /// (one per coefficient bit), apply inv_NTT_S, then fwd_NTT_Λ.
    fn naive_apply(ntt_s: &AdditiveNttGf8, ntt_l: &AdditiveNttGf8, bytes: &[u8]) -> Vec<F8> {
        let ell = 1usize << ntt_s.k();
        assert_eq!(bytes.len(), ell / 8);
        let mut v = vec![F8::ZERO; ell];
        for (b, &byte) in bytes.iter().enumerate() {
            for t in 0..8 {
                if (byte >> t) & 1 != 0 {
                    v[8 * b + t] = F8::ONE;
                }
            }
        }
        ntt_s.inverse(&mut v);
        ntt_l.forward(&mut v);
        v
    }

    #[test]
    fn matches_naive() {
        for k in [3usize, 4, 6] {
            let ntt_s = AdditiveNttGf8::new(k, F8::ZERO);
            let ntt_l = AdditiveNttGf8::new(k, F8::from_byte(1 << k));
            let table = InvNttTableByteSingleGf8::new(&ntt_s, &ntt_l);
            let mut rng = Rng::new(100 + k as u64);
            let mut out = vec![F8::ZERO; table.ell];
            for _ in 0..32 {
                let bytes: Vec<u8> = (0..table.n_chunks).map(|_| rng.next_u8()).collect();
                table.apply(&bytes, &mut out);
                assert_eq!(out, naive_apply(&ntt_s, &ntt_l, &bytes), "k={k}, bytes={bytes:02x?}");
            }
        }
    }

    /// The dispatched SIMD `apply` must reproduce `apply_scalar`. `ell ≥ 16` at
    /// every k here, so this exercises the vector body: k=4 (n_chunks=2,
    /// n128=1) through k=6 (n_chunks=8, n128=4, the headline protocol size).
    #[test]
    fn apply_simd_matches_apply_scalar() {
        for &k in &[4usize, 5, 6] {
            let ntt_s = AdditiveNttGf8::new(k, F8::ZERO);
            let ntt_l = AdditiveNttGf8::new(k, F8::from_byte(1u8 << k));
            let table = InvNttTableByteSingleGf8::new(&ntt_s, &ntt_l);

            let mut rng = Rng::new(100 + k as u64);
            for _ in 0..32 {
                let bytes: Vec<u8> = (0..table.n_chunks).map(|_| (rng.next_u64() & 0xff) as u8).collect();
                let mut out_scalar = vec![F8::ZERO; table.ell];
                let mut out_simd = vec![F8::ZERO; table.ell];
                table.apply_scalar(&bytes, &mut out_scalar);
                table.apply(&bytes, &mut out_simd);
                assert_eq!(
                    out_scalar, out_simd,
                    "scalar/simd apply disagree at k={k}, bytes={bytes:02x?}"
                );
                #[cfg(all(target_arch = "x86_64", target_feature = "avx2"))]
                if table.ell == 64 {
                    // SAFETY: the crate is built with AVX2, and `ell` is 64.
                    unsafe { table.apply_avx2(&bytes, &mut out_simd) };
                    assert_eq!(out_scalar, out_simd, "scalar/avx2 apply disagree, bytes={bytes:02x?}");
                }
            }
        }
    }
}
