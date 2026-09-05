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

use crate::ntt::AdditiveNttGf8;
use primitives::field::F8;

#[derive(Clone, Debug)]
pub struct InvNttTableByteSingleGf8 {
    pub k: usize,
    pub ell: usize,
    pub n_chunks: usize,
    /// `data[w * ell .. (w+1) * ell]` = T_0[w], the XOR-sum of columns of `M`
    /// indexed by the set bits of `w`.
    data: Vec<F8>,
}

impl InvNttTableByteSingleGf8 {
    /// Build the table given the two NTT instances: `ntt_S` over the input
    /// domain, `ntt_L` over the output (extension) domain. Both must have the
    /// same `k`.
    pub fn new(ntt_s: &AdditiveNttGf8, ntt_l: &AdditiveNttGf8) -> Self {
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
        for t in 0..8 {
            let entry_start = (1usize << t) * ell;
            data[entry_start..entry_start + ell].copy_from_slice(&cols[t]);
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

        Self { k, ell, n_chunks, data }
    }

    /// Raw pointer to the table data (`256 × ell` bytes, row-major). Used by
    /// the URM fused inner kernel, which can't go through the safe slice API
    /// without losing the register-fused layout.
    #[inline]
    pub fn data_ptr(&self) -> *const u8 {
        self.data.as_ptr() as *const u8
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
    pub fn apply(&self, bytes: &[u8], out: &mut [F8]) {
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
    /// The whole accumulator is a single ZMM, so it never round-trips through
    /// memory between chunks the way the 128-bit arm's four does, and the
    /// `i' ⊕ 8b` permutation is one `vpermq`: an XOR of `8b` on a byte index is
    /// an XOR of `b` on a qword index, which folds the chunk swap and the
    /// half-swap the narrow arm does separately into one shuffle.
    ///
    /// # Safety
    /// Requires AVX-512F, and `self.ell` must be 64. The method validates slice
    /// lengths.
    #[cfg(all(target_arch = "x86_64", target_feature = "avx512f"))]
    #[inline]
    #[target_feature(enable = "avx512f")]
    unsafe fn apply_avx512(&self, bytes: &[u8], out: &mut [F8]) {
        use core::arch::x86_64::*;
        assert_eq!(self.ell, 64);
        assert_eq!(bytes.len(), self.n_chunks);
        assert_eq!(out.len(), self.ell);
        // SAFETY: every row offset is `byte * 64` into a `256 * 64` table, and
        // the single store covers exactly `out`.
        unsafe {
            let base = self.data.as_ptr().cast::<u8>();
            let iota = _mm512_setr_epi64(0, 1, 2, 3, 4, 5, 6, 7);
            let row = |b: usize| _mm512_loadu_si512(base.add(bytes[b] as usize * 64).cast());
            let mut acc = row(0);
            for b in 1..self.n_chunks {
                let idx = _mm512_xor_si512(iota, _mm512_set1_epi64(b as i64));
                acc = _mm512_xor_si512(acc, _mm512_permutexvar_epi64(idx, row(b)));
            }
            _mm512_storeu_si512(out.as_mut_ptr().cast(), acc);
        }
    }

    /// Scalar reference. Kept public so tests can use it as the cross-check
    /// oracle for the NEON variant.
    pub fn apply_scalar(&self, bytes: &[u8], out: &mut [F8]) {
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
    /// This is flock's round-1 inner loop and it must inline into its caller,
    /// hence `#[inline(always)]` here and on every [`Vec128`] method.
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

        unsafe {
            // b = 0: identity permutation, a straight copy from row 0.
            let row0 = base.add(bytes[0] as usize * self.ell);
            for c in 0..n128 {
                V::store(out_ptr.add(c * 16), V::load(row0.add(c * 16)));
            }

            // b ≥ 1: XOR with table row[bytes[b]], permuted.
            for b in 1..self.n_chunks {
                let b_high = b >> 1;
                let b_odd = (b & 1) != 0;
                let row_b = base.add(bytes[b] as usize * self.ell);
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
        Self(unsafe { core::arch::aarch64::vld1q_u8(p) })
    }
    #[inline(always)]
    unsafe fn store(p: *mut u8, v: Self) {
        unsafe { core::arch::aarch64::vst1q_u8(p, v.0) }
    }
    #[inline(always)]
    fn xor(self, other: Self) -> Self {
        Self(unsafe { core::arch::aarch64::veorq_u8(self.0, other.0) })
    }
    #[inline(always)]
    fn swap64(self) -> Self {
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
        Self(unsafe { core::arch::x86_64::_mm_loadu_si128(p as *const core::arch::x86_64::__m128i) })
    }
    #[inline(always)]
    unsafe fn store(p: *mut u8, v: Self) {
        unsafe { core::arch::x86_64::_mm_storeu_si128(p as *mut core::arch::x86_64::__m128i, v.0) }
    }
    #[inline(always)]
    fn xor(self, other: Self) -> Self {
        unsafe { Self(core::arch::x86_64::_mm_xor_si128(self.0, other.0)) }
    }
    #[inline(always)]
    fn swap64(self) -> Self {
        unsafe { Self(core::arch::x86_64::_mm_shuffle_epi32::<0b01_00_11_10>(self.0)) }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use primitives::test_rng::Rng;

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
            let ntt_l = AdditiveNttGf8::new(k, F8(1 << k));
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
            let ntt_l = AdditiveNttGf8::new(k, F8(1u8 << k));
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
            }
        }
    }
}
