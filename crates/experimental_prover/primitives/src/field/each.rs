//! Elementwise kernels over slices of `F128`, eight elements at a time on AVX-512 and one at a time elsewhere.
//! Every operand is a contiguous slice, so the vector forms load it straight from memory.

use super::{F64, F128};
#[cfg(all(target_arch = "x86_64", target_feature = "vpclmulqdq", target_feature = "avx512f"))]
use super::{F64x8, F128x8, Prod8};

/// `out[i] = c·x[i]`.
#[inline]
pub fn scale_each(out: &mut [F128], c: F128, x: &[F128]) {
    assert_eq!(out.len(), x.len());
    #[cfg(all(target_arch = "x86_64", target_feature = "vpclmulqdq", target_feature = "avx512f"))]
    let (out, x) = {
        let ((o8, o_r), (x8, x_r)) = (out.as_chunks_mut::<8>(), x.as_chunks::<8>());
        let c8 = F128x8::splat(c);
        for (o, x) in o8.iter_mut().zip(x8) {
            *o = (c8 * F128x8::from_array(x)).to_array();
        }
        (o_r, x_r)
    };
    for (o, &x) in out.iter_mut().zip(x) {
        *o = c * x;
    }
}

/// `out[i] = out[i]·x[i]`.
#[inline]
pub fn mul_each(out: &mut [F128], x: &[F128]) {
    assert_eq!(out.len(), x.len());
    #[cfg(all(target_arch = "x86_64", target_feature = "vpclmulqdq", target_feature = "avx512f"))]
    let (out, x) = {
        let ((o8, o_r), (x8, x_r)) = (out.as_chunks_mut::<8>(), x.as_chunks::<8>());
        for (o, x) in o8.iter_mut().zip(x8) {
            *o = (F128x8::from_array(o) * F128x8::from_array(x)).to_array();
        }
        (o_r, x_r)
    };
    for (o, &x) in out.iter_mut().zip(x) {
        *o *= x;
    }
}

/// `out[i] = out[i]·k[i]`, a base-field factor.
#[inline]
pub fn mul_base_each(out: &mut [F128], k: &[F64]) {
    assert_eq!(out.len(), k.len());
    #[cfg(all(target_arch = "x86_64", target_feature = "vpclmulqdq", target_feature = "avx512f"))]
    let (out, k) = {
        let ((o8, o_r), (k8, k_r)) = (out.as_chunks_mut::<8>(), k.as_chunks::<8>());
        for (o, k) in o8.iter_mut().zip(k8) {
            *o = F128x8::from_array(o)
                .mul_base_unreduced(F64x8::from_array(k))
                .reduce_lanes()
                .to_array();
        }
        (o_r, k_r)
    };
    for (o, &k) in out.iter_mut().zip(k) {
        *o = o.mul_base(k);
    }
}

/// `out[i] = constant + Σ coef·col[i]` over the `(coef, col)` of `terms`, each `col` as long as `out`.
#[inline]
pub fn affine_each<'a>(out: &mut [F128], constant: F128, terms: impl Iterator<Item = (F128, &'a [F64])> + Clone) {
    #[cfg(all(target_arch = "x86_64", target_feature = "vpclmulqdq", target_feature = "avx512f"))]
    let (out, start) = {
        let (o8, _) = out.as_chunks_mut::<8>();
        let c8 = F128x8::splat(constant);
        for (i, o) in o8.iter_mut().enumerate() {
            let mut acc = Prod8::ZERO;
            for (coef, col) in terms.clone() {
                let k: &[F64; 8] = col[8 * i..8 * i + 8].try_into().unwrap();
                acc ^= F128x8::splat(coef).mul_base_unreduced(F64x8::from_array(k));
            }
            *o = (acc.reduce_lanes() + c8).to_array();
        }
        let start = 8 * o8.len();
        (&mut out[start..], start)
    };
    #[cfg(not(all(target_arch = "x86_64", target_feature = "vpclmulqdq", target_feature = "avx512f")))]
    let start = 0;
    for (i, o) in out.iter_mut().enumerate() {
        let mut acc = super::F128Unreduced::ZERO;
        for (coef, col) in terms.clone() {
            acc ^= coef.mul_base_unreduced(col[start + i]);
        }
        *o = acc.reduce() + constant;
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::test_rng::Rng;

    #[test]
    fn kernels_match_the_scalar_forms() {
        let mut rng = Rng::new(0xEAC4);
        for len in [0usize, 1, 7, 8, 9, 16, 31] {
            let x: Vec<F128> = (0..len).map(|_| rng.ext()).collect();
            let y: Vec<F128> = (0..len).map(|_| rng.ext()).collect();
            let k: Vec<Vec<F64>> = (0..3)
                .map(|_| (0..len).map(|_| F64(rng.next_u64())).collect())
                .collect();
            let (c, d) = (rng.ext(), rng.ext());
            let mut out = vec![F128::ZERO; len];
            scale_each(&mut out, c, &x);
            assert_eq!(out, x.iter().map(|&x| c * x).collect::<Vec<_>>());
            mul_each(&mut out, &y);
            mul_base_each(&mut out, &k[0]);
            assert_eq!(
                out,
                (0..len)
                    .map(|i| (c * x[i] * y[i]).mul_base(k[0][i]))
                    .collect::<Vec<_>>()
            );
            let coefs = [rng.ext(), rng.ext(), rng.ext()];
            affine_each(&mut out, d, coefs.iter().zip(&k).map(|(&c, k)| (c, &k[..])));
            let want = (0..len).map(|i| d + (0..3).map(|t| coefs[t].mul_base(k[t][i])).sum::<F128>());
            assert_eq!(out, want.collect::<Vec<_>>(), "length {len}");
        }
    }
}
