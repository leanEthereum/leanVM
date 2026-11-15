//! Multiplication by `X` in the novel polynomial basis of Annex D: the `beta X` of the affine fold.
//!
//! `X_c = prod_(i: c_i = 1) What_i` and `What_i^2 = What_i + a_i What_(i+1)`, with
//! `a_i = W_(i+1)(beta_(i+1)) / W_i(beta_i)^2`. With `A_t = a_0 ... a_(t-1)` and `t` the trailing zeros of `c`,
//!
//! ```text
//!     (X h)[0] = 0,    (X h)[c] = A_t (h[c - 1] + h[c + 2^t - 1]),
//! ```
//!
//! reading zero past the end of `h`, so `X h` has one coefficient more than `h`. Each entry pulls from two, so any
//! range of it is computed from `h` alone, and an entry at or above `2^mu` only feeds entries at or above `2^mu`.

use std::sync::OnceLock;

use primitives::field::{F64, F128};

/// A coefficient: `K` or `E`, scaled by the `K` constants `A_t`.
pub(crate) trait Coef: Copy + Default + std::ops::Add<Output = Self> {
    fn scale(self, k: F64) -> Self;
}

impl Coef for F64 {
    fn scale(self, k: F64) -> Self {
        self * k
    }
}

impl Coef for F128 {
    fn scale(self, k: F64) -> Self {
        self.mul_base(k)
    }
}

/// `A_t` for every `t < 64`.
fn constants() -> &'static [F64; 64] {
    static A: OnceLock<[F64; 64]> = OnceLock::new();
    A.get_or_init(|| {
        let roots = crate::whir_induce::subspace_roots(63);
        let mut a = [F64::ONE; 64];
        for t in 1..64 {
            a[t] = a[t - 1] * roots[t] * roots[t - 1].square().inv();
        }
        a
    })
}

/// `(X h)[c]`, coefficient `i` of `h` being `h(i)`, zero past its end.
#[inline(always)]
pub(crate) fn x_coef<T: Coef>(h: impl Fn(usize) -> T, c: usize) -> T {
    match c {
        0 => T::default(),
        _ if c & 1 == 1 => h(c - 1) + h(c),
        _ => (h(c - 1) + h(c + (1 << c.trailing_zeros()) - 1)).scale(constants()[c.trailing_zeros() as usize]),
    }
}

/// `(X h)[c]`.
pub(crate) fn x_at<T: Coef>(h: &[T], c: usize) -> T {
    x_coef(|i| h.get(i).copied().unwrap_or_default(), c)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ntt::AdditiveNttF64;
    use primitives::test_rng::Rng;

    /// `X h` in evaluation form: encode `h` on a domain of `2^log_d` points, multiply each by its point, decode.
    fn by_evaluation(h: &[F64], log_d: usize) -> Vec<F64> {
        let mut data = h.to_vec();
        data.resize(1 << log_d, F64::ZERO);
        let ntt = AdditiveNttF64::standard(log_d);
        ntt.encode_interleaved_in_place(&mut data, 1, 0);
        for (q, v) in data.iter_mut().enumerate() {
            *v *= F64(q as u64);
        }
        ntt.inverse_transform(&mut data, 1);
        data
    }

    /// On `K` and `E` coefficients, with a high part.
    #[test]
    fn x_matches_multiplication_in_evaluation_form() {
        let mut rng = Rng::new(0x3);
        for mu in 0..=11 {
            for high in [0usize, 1, 3, 6] {
                let n = (1usize << mu) + high;
                if n + 1 > 2 << mu {
                    continue;
                }
                let [lo, hi]: [Vec<F64>; 2] = std::array::from_fn(|_| (0..n).map(|_| F64(rng.next_u64())).collect());
                let [want_lo, want_hi] = [&lo, &hi].map(|h| by_evaluation(h, mu + 1));
                assert!(want_lo[n + 1..].iter().all(|v| v.is_zero()), "mu={mu}, high={high}");
                let h: Vec<F128> = lo.iter().zip(&hi).map(|(lo, hi)| F128::new(lo.0, hi.0)).collect();
                for c in 0..=n {
                    assert_eq!(x_at(&lo, c), want_lo[c], "K, column {c}, mu={mu}, high={high}");
                    assert_eq!(
                        x_at(&h, c),
                        F128::new(want_lo[c].0, want_hi[c].0),
                        "E, column {c}, mu={mu}"
                    );
                }
            }
        }
    }
}
