// CREDIT: https://github.com/succinctlabs/flock (flock-core), MIT OR Apache-2.0.
//! Round-1 (univariate skip): live helpers, plus the reference oracles the optimized kernels are
//! checked against.
//!
//! The module is two disjoint halves:
//!
//! - **Live in production**: the [`build_eq`] re-export, [`SplitEq`] and [`ntt_extend_vec`].
//!   The round-1 kernel ([`super::round1`]) and the round-2 kernel
//!   ([`super::multilinear`]) are built on these.
//! - **Test-only oracles**, below the banner and all `#[cfg(test)]`: `pack_bits`,
//!   `round1_naive` and `round1_extract_c_packed`. They translate the protocol
//!   formula directly, so the optimized kernels can be diffed against something obviously
//!   correct.
//!
//! The round-1 message is `(P^{AB}, P^C)`, each a length-`2^k_skip` vector
//! of F192 values. They are evaluations on the NTT domain `Λ` of the
//! polynomial (over λ) defined by
//!
//!   P^{AB}(λ) = Σ_{x ∈ {0,1}^{m-k_skip}} eq(r_rest, x) · φ₈(â(λ, x) · b̂(λ, x))
//!   P^C(λ)   = Σ_{x ∈ {0,1}^{m-k_skip}} eq(r_rest, x) · φ₈(ĉ(λ, x))
//!
//! where â(λ, x), b̂(λ, x), ĉ(λ, x) ∈ F₂⁸ are the values at λ of the
//! univariate polynomial whose evaluations on `S = {0,…,2^k_skip − 1}` are
//! the boolean witness values `a(s, x), b(s, x), c(s, x)`. The polynomial is
//! recovered via `inv_NTT_S`; we then evaluate on `Λ = {2^k_skip, …}` via
//! `fwd_NTT_Λ`.
//!

#[cfg(test)]
use pcs::ntt::AdditiveNttGf8;
use pcs::ntt::InvNttTableByteSingleGf8;
use primitives::field::{F8, F192, phi8_192 as phi8};

// ---------------------------------------------------------------------------
// Live helpers.
// ---------------------------------------------------------------------------

pub use primitives::multilinear::eq_table as build_eq;

/// Pack a bit vector LSB-first into bytes.
#[cfg(test)]
pub fn pack_bits(bits: &[bool]) -> Vec<u8> {
    let n_bytes = bits.len().div_ceil(8);
    // Each output byte depends on 8 contiguous input bits: disjoint, so
    // process bytes in parallel.
    parallel::map_collect(n_bytes, |byte_idx| {
        let mut byte = 0u8;
        let base = byte_idx * 8;
        for j in 0..8 {
            let bit_idx = base + j;
            if bit_idx < bits.len() && bits[bit_idx] {
                byte |= 1u8 << j;
            }
        }
        byte
    })
}

/// Eq table split into a lo half (large, L2-resident) and a hi half (small,
/// kept in registers across the inner loop).
#[derive(Clone, Debug)]
pub struct SplitEq {
    pub n_lo: usize,
    pub n_hi: usize,
    pub lo: Vec<F192>,
    pub hi: Vec<F192>,
}

impl SplitEq {
    /// C++-default cap on the hi half size: keeps outer F192 muls cheap.
    pub const MAX_N_HI: usize = 7;

    pub fn new(r: &[F192]) -> Self {
        let n = r.len();
        let n_hi = n.min(Self::MAX_N_HI);
        let n_lo = n - n_hi;
        Self {
            n_lo,
            n_hi,
            lo: build_eq(&r[..n_lo]),
            hi: build_eq(&r[n_lo..]),
        }
    }
}

/// Extend a length-`ell` F192 vector from the input domain S to the extension
/// domain Λ using bit-plane decomposition: for each of the 192 bit positions
/// of F192, run the bit-input NTT (`inv_NTT_S` then `fwd_NTT_Λ` via the
/// precomputed table) on that bit-plane, scale by γ^b, and accumulate.
///
/// Ports `ntt_extend_vec` (scalar form). The NTT is F_2-linear and
/// φ_8 commutes with that linearity, which is what makes the bit-by-bit
/// decomposition equal to the direct F_8-valued NTT extension.
pub fn ntt_extend_vec(in_s: &[F192], inv_table: &InvNttTableByteSingleGf8) -> Vec<F192> {
    let ell = inv_table.ell;
    assert_eq!(in_s.len(), ell);
    assert_eq!(ell, 1usize << inv_table.k);

    let mut out = vec![F192::ZERO; ell];
    let n_chunks = inv_table.n_chunks;

    let mut input_bits = vec![0u8; n_chunks];
    let mut out_bytes = vec![F8::ZERO; ell];

    for b in 0..192 {
        // Pack bit b of each in_s[z] into z-indexed LSB-first byte form.
        input_bits.iter_mut().for_each(|x| *x = 0);
        for z in 0..ell {
            let bit = match b / 64 {
                0 => (in_s[z].c0 >> b) & 1,
                1 => (in_s[z].c1 >> (b - 64)) & 1,
                2 => (in_s[z].c2 >> (b - 128)) & 1,
                _ => unreachable!(),
            };
            if bit != 0 {
                input_bits[z / 8] |= 1u8 << (z % 8);
            }
        }

        // Bit-input NTT.
        inv_table.apply(&input_bits, &mut out_bytes);

        let basis = match b / 64 {
            0 => F192::new(1u64 << b, 0, 0),
            1 => F192::new(0, 1u64 << (b - 64), 0),
            2 => F192::new(0, 0, 1u64 << (b - 128)),
            _ => unreachable!(),
        };
        for lambda in 0..ell {
            out[lambda] += basis * phi8(out_bytes[lambda]);
        }
    }

    out
}

// ===========================================================================
// Test-only oracles. Everything below is `#[cfg(test)]`: direct translations of
// the protocol formula, kept only so the optimized kernels have something
// obviously correct to be diffed against.
// ===========================================================================

/// Compute the round-1 prover message naively (no shift-reduce, no fused
/// inner, no deferred reduction: direct algorithmic translation of the
/// protocol formula).
///
/// Returns `(p_ab, p_c)`, each a length-`2^k_skip` F192 vector of evaluations
/// on Λ.
///
/// Preconditions:
/// - `a.len() == b.len() == c.len() == 2^m`
/// - `r_rest.len() == m - k_skip`
/// - `k_skip <= m`
///
/// Index convention: for index `i ∈ 0..2^m`, the low `k_skip` bits address
/// the *skip* variables (`y_skip ∈ S`), the high `m - k_skip` bits address
/// the *rest* variables (`y_rest`).
#[cfg(test)]
pub fn round1_naive(
    a: &[bool],
    b: &[bool],
    c: &[bool],
    m: usize,
    k_skip: usize,
    r_rest: &[F192],
) -> (Vec<F192>, Vec<F192>) {
    assert!(k_skip <= m, "k_skip must be ≤ m");
    assert_eq!(a.len(), 1usize << m);
    assert_eq!(b.len(), 1usize << m);
    assert_eq!(c.len(), 1usize << m);
    assert_eq!(r_rest.len(), m - k_skip);

    let ell = 1usize << k_skip;
    let n_chunks_x = 1usize << (m - k_skip);

    // NTT for evaluating-on-Λ via inv-on-S then fwd-on-Λ.
    let ntt_s = AdditiveNttGf8::new(k_skip, F8::ZERO);
    let ntt_l = AdditiveNttGf8::new(k_skip, F8(ell as u8));

    let eq_full = build_eq(r_rest);

    let mut p_ab = vec![F192::ZERO; ell];
    let mut p_c = vec![F192::ZERO; ell];

    let mut a_col = vec![F8::ZERO; ell];
    let mut b_col = vec![F8::ZERO; ell];
    let mut c_col = vec![F8::ZERO; ell];

    for x_rest in 0..n_chunks_x {
        let base = x_rest * ell;
        for s in 0..ell {
            a_col[s] = F8(a[base + s] as u8);
            b_col[s] = F8(b[base + s] as u8);
            c_col[s] = F8(c[base + s] as u8);
        }
        // Extend the row polynomial from S to Λ.
        ntt_s.inverse(&mut a_col);
        ntt_l.forward(&mut a_col);
        ntt_s.inverse(&mut b_col);
        ntt_l.forward(&mut b_col);
        ntt_s.inverse(&mut c_col);
        ntt_l.forward(&mut c_col);

        let eq_x = eq_full[x_rest];
        for i in 0..ell {
            let ab = a_col[i] * b_col[i];
            p_ab[i] += eq_x * phi8(ab);
            p_c[i] += eq_x * phi8(c_col[i]);
        }
    }

    (p_ab, p_c)
}

/// Packed-input round-1 message in extract_c form: the scalar reference the
/// optimized kernel is cross-checked against.
#[cfg(test)]
pub fn round1_extract_c_packed(
    a_packed: &[u8],
    b_packed: &[u8],
    c_packed: &[u8],
    m: usize,
    k_skip: usize,
    r_rest: &[F192],
    inv_table: &InvNttTableByteSingleGf8,
) -> (Vec<F192>, Vec<F192>) {
    assert!(k_skip <= m);
    let total_bytes = (1usize << m) / 8;
    assert_eq!(a_packed.len(), total_bytes);
    assert_eq!(b_packed.len(), total_bytes);
    assert_eq!(c_packed.len(), total_bytes);
    assert_eq!(r_rest.len(), m - k_skip);
    assert_eq!(inv_table.k, k_skip);

    let ell = 1usize << k_skip;
    let n_chunks = ell / 8;

    let eq = SplitEq::new(r_rest);
    let lo_size = 1usize << eq.n_lo;
    let hi_size = 1usize << eq.n_hi;

    let mut res_ab = vec![F192::ZERO; ell];
    let mut res_c_s = vec![F192::ZERO; ell];

    let mut partial_ab = vec![F192::ZERO; ell];
    let mut partial_c = vec![F192::ZERO; ell];

    let mut a_col = vec![F8::ZERO; ell];
    let mut b_col = vec![F8::ZERO; ell];

    for x_hi in 0..hi_size {
        partial_ab.iter_mut().for_each(|p| *p = F192::ZERO);
        partial_c.iter_mut().for_each(|p| *p = F192::ZERO);

        for x_lo in 0..lo_size {
            let x_rest = (x_hi << eq.n_lo) | x_lo;
            let chunk_offset = x_rest * n_chunks;

            // A, B → Λ-domain via table lookup.
            inv_table.apply(&a_packed[chunk_offset..chunk_offset + n_chunks], &mut a_col);
            inv_table.apply(&b_packed[chunk_offset..chunk_offset + n_chunks], &mut b_col);

            let eq_lo = eq.lo[x_lo];

            // AB on Λ: unchanged.
            for lambda in 0..ell {
                let ab = a_col[lambda] * b_col[lambda];
                partial_ab[lambda] += eq_lo * phi8(ab);
            }

            // C on S.
            for s in 0..ell {
                let c_bit = (c_packed[chunk_offset + s / 8] >> (s % 8)) & 1;
                if c_bit != 0 {
                    partial_c[s] += eq_lo;
                }
            }
        }

        let eq_hi = eq.hi[x_hi];
        for lambda in 0..ell {
            res_ab[lambda] += eq_hi * partial_ab[lambda];
            res_c_s[lambda] += eq_hi * partial_c[lambda];
        }
    }

    let res_c_lifted = ntt_extend_vec(&res_c_s, inv_table);
    (res_ab, res_c_lifted)
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use primitives::test_rng::Rng;

    fn make_inv_table(k_skip: usize) -> InvNttTableByteSingleGf8 {
        let ntt_s = AdditiveNttGf8::new(k_skip, F8::ZERO);
        let ntt_l = AdditiveNttGf8::new(k_skip, F8(1u8 << k_skip));
        InvNttTableByteSingleGf8::new(&ntt_s, &ntt_l)
    }

    /// The strongest correctness check: extract_c must produce **identical**
    /// output to the naive round-1 message: same eq weights, same protocol,
    /// just an optimized algorithm.
    #[test]
    fn extract_c_matches_naive() {
        for &(m, k_skip) in &[(4, 3), (5, 3), (6, 3), (7, 4), (8, 3), (9, 6)] {
            let mut rng = Rng::new(100 + m as u64 * 10 + k_skip as u64);
            let a = rng.bits(1 << m);
            let b = rng.bits(1 << m);
            let c = rng.bits(1 << m);
            let r = rng.ext_vec(m - k_skip);
            let table = make_inv_table(k_skip);

            let (naive_ab, naive_c) = round1_naive(&a, &b, &c, m, k_skip, &r);
            let (opt_ab, opt_c) =
                round1_extract_c_packed(&pack_bits(&a), &pack_bits(&b), &pack_bits(&c), m, k_skip, &r, &table);

            assert_eq!(naive_ab, opt_ab, "AB mismatch at m={m}, k_skip={k_skip}");
            assert_eq!(naive_c, opt_c, "C mismatch at m={m}, k_skip={k_skip}");
        }
    }

    #[test]
    fn split_eq_basic() {
        // Building the lo and hi tables separately should produce the same
        // values as the full eq table when indexed appropriately.
        let mut rng = Rng::new(300);
        let n = 6;
        let r = rng.ext_vec(n);
        let full = build_eq(&r);
        let eq = SplitEq::new(&r);
        assert_eq!(eq.n_lo + eq.n_hi, n);
        for x in 0..(1 << n) {
            let x_lo = x & ((1 << eq.n_lo) - 1);
            let x_hi = x >> eq.n_lo;
            assert_eq!(eq.lo[x_lo] * eq.hi[x_hi], full[x]);
        }
    }
}
