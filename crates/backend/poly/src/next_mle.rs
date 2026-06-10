use ::utils::log2_strict_usize;
use field::{ExtensionField, Field, PrimeCharacteristicRing};
use zk_alloc::ArenaVec;

use crate::{PF, eval_eq_scaled, eval_eq_with_tail, to_big_endian_in_field};

/// Evaluates the "next" multilinear polynomial at two n-variable points (x, y).
///
/// On boolean inputs, returns 1 if y = x + 1 (big-endian binary), with the special case that
/// next_mle(2^n - 1, 2^n - 1) = 1 (wrap-around).
pub fn next_mle<F: Field>(x: &[F], y: &[F]) -> F {
    assert_eq!(x.len(), y.len());
    let n = x.len();
    let mut eq_prefix = Vec::with_capacity(n + 1);
    eq_prefix.push(F::ONE);
    for i in 0..n {
        let eq_i = x[i] * y[i] + (F::ONE - x[i]) * (F::ONE - y[i]);
        eq_prefix.push(eq_prefix[i] * eq_i);
    }
    let mut low_suffix = vec![F::ONE; n + 1];
    for i in (0..n).rev() {
        low_suffix[i] = low_suffix[i + 1] * x[i] * (F::ONE - y[i]);
    }
    let mut sum = F::ZERO;
    for arr in 0..n {
        let carry = (F::ONE - x[arr]) * y[arr];
        sum += eq_prefix[arr] * carry * low_suffix[arr + 1];
    }

    sum + x.iter().chain(y).copied().product::<F>()
}

/// Computes the dense vector `next_mle(outer_challenges, y)` for all y in {0,1}^n.
///
/// This is the "folded" version: the first argument (outer_challenges) is fixed,
/// and the result is a vector indexed by the second argument.
pub fn matrix_next_mle_folded<F: ExtensionField<PF<F>>>(outer_challenges: &[F]) -> ArenaVec<F>
where
    PF<F>: PrimeCharacteristicRing,
{
    let n = outer_challenges.len();
    let mut res = unsafe { ArenaVec::<F>::zeroed(1 << n) };
    for k in 0..n {
        let outer_challenges_prod =
            (F::ONE - outer_challenges[n - k - 1]) * outer_challenges[n - k..].iter().copied().product::<F>();
        let mut eq_mle = eval_eq_scaled(&outer_challenges[0..n - k - 1], outer_challenges_prod);
        for (mut i, v) in eq_mle.iter_mut().enumerate() {
            i <<= k + 1;
            i += 1 << k;
            res[i] += *v;
        }
    }
    res[(1 << n) - 1] += outer_challenges.iter().copied().product::<F>();

    res
}

/// Tensor-tail variant of [`next_mle`]:
/// `Σ_x tail[x] · next_mle(concat(prefix, bits(x)), y)`, where `bits(x)` is
/// big-endian over `log2(tail.len())` variables (matching `eval_eq` indexing).
/// Verifier-side: the loop over the `2^k` cube points is intentional.
pub fn next_mle_with_tail<F: Field>(prefix: &[F], tail: &[F], y: &[F]) -> F {
    let k = log2_strict_usize(tail.len());
    debug_assert_eq!(prefix.len() + k, y.len());
    let mut sum = F::ZERO;
    for (x, &t) in tail.iter().enumerate() {
        let mut point = prefix.to_vec();
        point.extend(to_big_endian_in_field::<F>(x, k));
        sum += next_mle(&point, y) * t;
    }
    sum
}

/// Tensor-tail variant of [`matrix_next_mle_folded`]: the dense vector
/// `w[y] = Σ_x tail[x] · next_mle(concat(prefix, bits(x)), y)`.
///
/// Since `next_mle` is multilinear in its first argument,
/// `w[y] = Σ_j v[j] · next_mle(j, y)` with `v = eval_eq_with_tail(prefix, tail)`,
/// and `next_mle(j, y) = 1` iff `y = j + 1`, plus the wrap-around
/// `next_mle(2^n − 1, 2^n − 1) = 1` (see [`next_mle`]). Hence `w` is the
/// shift-by-one of `v`, with `w[last] += v[last]`.
pub fn matrix_next_mle_folded_with_tail<F: ExtensionField<PF<F>>>(prefix: &[F], tail: &[F]) -> ArenaVec<F> {
    let v = eval_eq_with_tail(prefix, tail);
    let n = v.len();
    let mut res = unsafe { ArenaVec::<F>::zeroed(n) };
    res[1..].copy_from_slice(&v[..n - 1]);
    res[n - 1] += v[n - 1];
    res
}

#[cfg(test)]
mod tests {
    use field::PrimeCharacteristicRing;
    use koala_bear::KoalaBear;

    use crate::{EvaluationsList, MultilinearPoint, matrix_next_mle_folded, next_mle, to_big_endian_in_field};

    type F = KoalaBear;

    #[test]
    fn test_matrix_down_folded() {
        let n_vars = 5;
        for x in 0..1 << n_vars {
            let x_bools = to_big_endian_in_field::<F>(x, n_vars);
            let matrix = matrix_next_mle_folded(&x_bools);
            for y in 0..1 << n_vars {
                let y_bools = to_big_endian_in_field::<F>(y, n_vars);
                let expected = F::from_bool(if (x, y) == ((1 << n_vars) - 1, (1 << n_vars) - 1) {
                    true
                } else {
                    x + 1 == y
                });
                assert_eq!(matrix.evaluate(&MultilinearPoint(y_bools.clone())), expected);
                assert_eq!(next_mle(&x_bools, &y_bools), expected);
            }
        }
    }

    #[test]
    fn test_next_mle_with_tail_brute_force() {
        use koala_bear::QuinticExtensionFieldKB;
        use rand::{RngExt, SeedableRng, rngs::StdRng};

        use crate::next_mle_with_tail;
        type EF = QuinticExtensionFieldKB;

        let mut rng = StdRng::seed_from_u64(11);
        for k in [2usize, 3] {
            let n_prefix = 5 - k;
            let prefix: Vec<EF> = (0..n_prefix).map(|_| rng.random()).collect();
            let tail: Vec<EF> = (0..1 << k).map(|_| rng.random()).collect();
            let y: Vec<EF> = (0..5).map(|_| rng.random()).collect();
            let direct = next_mle_with_tail(&prefix, &tail, &y);
            let mut brute = EF::ZERO;
            for (x, &t) in tail.iter().enumerate() {
                let mut point = prefix.clone();
                point.extend(to_big_endian_in_field::<EF>(x, k));
                brute += next_mle(&point, &y) * t;
            }
            assert_eq!(direct, brute);
        }
    }

    #[test]
    fn test_matrix_next_mle_folded_with_tail_matches_sum() {
        use koala_bear::QuinticExtensionFieldKB;
        use rand::{RngExt, SeedableRng, rngs::StdRng};

        use crate::{matrix_next_mle_folded_with_tail, next_mle_with_tail};
        type EF = QuinticExtensionFieldKB;

        let mut rng = StdRng::seed_from_u64(12);
        for k in [2usize, 3] {
            let n_prefix = 5 - k;
            let prefix: Vec<EF> = (0..n_prefix).map(|_| rng.random()).collect();
            let tail: Vec<EF> = (0..1 << k).map(|_| rng.random()).collect();

            let folded = matrix_next_mle_folded_with_tail(&prefix, &tail);

            // Elementwise against the sum of per-cube-point folded matrices.
            let mut expected = EF::zero_vec(1 << 5);
            for (x, &t) in tail.iter().enumerate() {
                let mut point = prefix.clone();
                point.extend(to_big_endian_in_field::<EF>(x, k));
                for (e, &m) in expected.iter_mut().zip(matrix_next_mle_folded(&point).iter()) {
                    *e += m * t;
                }
            }
            assert_eq!(folded.as_slice(), &expected[..]);

            // Consistency with the pointwise variant: the folded vector's MLE at a
            // boolean point y equals next_mle_with_tail(prefix, tail, y).
            for y in 0..1usize << 5 {
                let y_bools = to_big_endian_in_field::<EF>(y, 5);
                assert_eq!(
                    folded.evaluate(&MultilinearPoint(y_bools.clone())),
                    next_mle_with_tail(&prefix, &tail, &y_bools)
                );
            }
        }
    }
}
