//! The product sumcheck's rounds: a round message, a bind, and the two fused.

use primitives::PrimeCharacteristicRing;

use parallel::SendPtr;
use primitives::F192;

/// Length above which the inner product / element-wise kernels fan out to the
/// pool. Below it, sequential beats dispatch overhead.
const SUMCHECK_PAR_THRESHOLD: usize = 1usize << 12;

/// One round of product-sumcheck on `(c, z)`: compute `(q(1), q(∞))` =
/// `(Σ c_hi·z_hi, Σ (c_hi+c_lo)·(z_hi+z_lo))` over the top-bit split. The
/// `len()` of `c` and `z` is even; `half = len/2`.
pub(super) fn sumcheck_round_eval_par(c: &[F192], z: &[F192]) -> (F192, F192) {
    let half = c.len() / 2;
    debug_assert_eq!(z.len(), c.len());
    let (clo, chi) = c.split_at(half);
    let (zlo, zhi) = z.split_at(half);
    if half < SUMCHECK_PAR_THRESHOLD {
        let mut e1 = F192::ZERO;
        let mut einf = F192::ZERO;
        for i in 0..half {
            e1 += chi[i] * zhi[i];
            einf += (chi[i] + clo[i]) * (zhi[i] + zlo[i]);
        }
        return (e1, einf);
    }
    parallel::map_reduce(
        half,
        || (F192::ZERO, F192::ZERO),
        |i| {
            let e1_i = chi[i] * zhi[i];
            let einf_i = (chi[i] + clo[i]) * (zhi[i] + zlo[i]);
            (e1_i, einf_i)
        },
        |a, b| (a.0 + b.0, a.1 + b.1),
    )
}

/// Bind the top remaining variable of `v` at challenge `r`: `v[i] ← v[i] +
/// r·(v[i+half] + v[i])` for `i ∈ [0, half)`, then truncate to `half`. In-place.
pub(super) fn sumcheck_bind_top_in_place_par(v: &mut Vec<F192>, r: F192) {
    let half = v.len() / 2;
    if half < SUMCHECK_PAR_THRESHOLD {
        for i in 0..half {
            v[i] = v[i] + r * (v[i + half] + v[i]);
        }
    } else {
        let (lo, hi) = v.split_at_mut(half);
        let hi = &hi[..half];
        let chunk = parallel::recommended_chunk_size(half);
        parallel::chunks_mut_zip(lo, hi, chunk, |_, lo_c, hi_c| {
            for (lo_i, &hi_i) in lo_c.iter_mut().zip(hi_c) {
                *lo_i = *lo_i + r * (hi_i + *lo_i);
            }
        });
    }
    v.truncate(half);
}

/// **Fused fold + next-round evaluation.** Binds the top variable of *both*
/// `comb` and `z` at `r` (in place, each length halves) AND returns the next
/// product-sumcheck round's message `(q(1), q(∞))` over the just-bound tables,
/// all in a single pass over the data.
///
/// Why it fuses: round `t`'s message must be sent before `r_t` is sampled, so
/// eval(t) and bind(t) can't share a pass. But binding at `r_t` produces
/// exactly the table eval(t+1) reads, and `r_t` is known by then. The bound
/// values `new[i]` and `new[i+half2]` are precisely the `lo`/`hi` halves the
/// next round's eval pairs up, so we form each product the moment both bound
/// values exist. This replaces eval + two binds (3 passes) with 1.
///
/// Operates on quarters of each array (`half2 = len/4`). For `i ∈ 0..half2`:
/// ```text
///   lo' = q0[i] + r·(q2[i] + q0[i])   (= new[i],        next round's lo)
///   hi' = q1[i] + r·(q3[i] + q1[i])   (= new[i+half2],  next round's hi)
///   q0[i] ← lo';  q1[i] ← hi'
///   e1   += hi'·zhi';   einf += (hi'+lo')·(zhi'+zlo')
/// ```
/// In-place is safe: each `i` reads its 4 quarter-entries before writing the 2
/// low-half slots, and writes across distinct `i` are disjoint. Requires
/// `comb.len() == z.len()`, a power of two ≥ 4 (so the bound length ≥ 2 has a
/// well-defined next round; the caller guarantees this by only fusing when a
/// later round exists). The returned message is bit-identical to
/// `sumcheck_round_eval_par` run on the bound tables.
pub(super) fn sumcheck_bind_both_and_eval_next(comb: &mut Vec<F192>, z: &mut Vec<F192>, r: F192) -> (F192, F192) {
    let len = comb.len();
    debug_assert_eq!(z.len(), len);
    let half = len / 2;
    let half2 = half / 2;
    debug_assert!(half2 >= 1, "fused step needs a well-defined next round");

    // q0,q1 = low half (written); q2,q3 = high half (read-only).
    let (c_lo, c_hi) = comb.split_at_mut(half);
    let (cq0, cq1) = c_lo.split_at_mut(half2);
    let (cq2, cq3) = c_hi.split_at(half2);
    let (z_lo, z_hi) = z.split_at_mut(half);
    let (zq0, zq1) = z_lo.split_at_mut(half2);
    let (zq2, zq3) = z_hi.split_at(half2);

    let (e1, einf) = if half2 < SUMCHECK_PAR_THRESHOLD {
        let mut e1 = F192::ZERO;
        let mut einf = F192::ZERO;
        for i in 0..half2 {
            let lo = cq0[i] + r * (cq2[i] + cq0[i]);
            let hi = cq1[i] + r * (cq3[i] + cq1[i]);
            let zlo = zq0[i] + r * (zq2[i] + zq0[i]);
            let zhi = zq1[i] + r * (zq3[i] + zq1[i]);
            cq0[i] = lo;
            cq1[i] = hi;
            zq0[i] = zlo;
            zq1[i] = zhi;
            e1 += hi * zhi;
            einf += (hi + lo) * (zhi + zlo);
        }
        (e1, einf)
    } else {
        // The two written quarters are indexed rather than zipped: eight-way
        // `zip` of four mutable and four shared slices has no counterpart here,
        // and index `i` of each quarter is written by exactly one task.
        let cq0_p = SendPtr(cq0.as_mut_ptr());
        let cq1_p = SendPtr(cq1.as_mut_ptr());
        let zq0_p = SendPtr(zq0.as_mut_ptr());
        let zq1_p = SendPtr(zq1.as_mut_ptr());
        parallel::map_reduce(
            half2,
            || (F192::ZERO, F192::ZERO),
            |i| {
                // SAFETY: distinct `i` touch distinct slots of four disjoint
                // quarters (`split_at_mut` above), all borrowed for the dispatch.
                let (c0, c1, z0, z1) = unsafe {
                    (
                        &mut *cq0_p.add(i),
                        &mut *cq1_p.add(i),
                        &mut *zq0_p.add(i),
                        &mut *zq1_p.add(i),
                    )
                };
                let lo = *c0 + r * (cq2[i] + *c0);
                let hi = *c1 + r * (cq3[i] + *c1);
                let zlo = *z0 + r * (zq2[i] + *z0);
                let zhi = *z1 + r * (zq3[i] + *z1);
                *c0 = lo;
                *c1 = hi;
                *z0 = zlo;
                *z1 = zhi;
                (hi * zhi, (hi + lo) * (zhi + zlo))
            },
            |a, b| (a.0 + b.0, a.1 + b.1),
        )
    };

    comb.truncate(half);
    z.truncate(half);
    (e1, einf)
}
