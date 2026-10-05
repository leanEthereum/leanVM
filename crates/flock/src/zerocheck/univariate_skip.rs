// CREDIT: https://github.com/succinctlabs/flock (flock-core), MIT OR Apache-2.0.
//! Univariate-skip equality weights and extension-domain interpolation.
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
//! The oracles keep the constant F₈ factor `C_s = φ₈(0x1C)` in the eq-on-S weights;
//! [`super::univariate_skip_optimized`] drops it and the caller restores it before the message
//! goes on the wire.

use pcs::ntt::InvNttTableByteSingleGf8;
use primitives::field::{F8, F192, phi8_192 as phi8};

// ---------------------------------------------------------------------------
// Live helpers.
// ---------------------------------------------------------------------------

pub use primitives::multilinear::eq_table as build_eq;

/// Most high variables of a split eq table capped on its high side: few high weights keep the outer products cheap.
pub const EQ_HIGH_VARS: usize = 7;

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

#[cfg(test)]
pub(crate) mod tests {
    use super::*;
    use pcs::ntt::AdditiveNttGf8;

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
    pub(crate) fn round1_naive(
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

        for (x_rest, &weight) in eq_full.iter().enumerate().take(n_chunks_x) {
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

            let eq_x = weight;
            for i in 0..ell {
                let ab = a_col[i] * b_col[i];
                p_ab[i] += eq_x * phi8(ab);
                p_c[i] += eq_x * phi8(c_col[i]);
            }
        }

        (p_ab, p_c)
    }

    /// Pack a bit vector LSB-first into bytes.
    pub(crate) fn pack_bits(bits: &[bool]) -> Vec<u8> {
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
}
