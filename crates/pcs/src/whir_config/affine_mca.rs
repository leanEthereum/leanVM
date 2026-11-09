//! Finite form of the affine-combiner mutual correlated agreement bound [CYWZ26, preprint], Lemma 4.1 with the
//! interpolation inequality of Lemma 4.2, for `RS[n, d]` (degree at most `d`) at agreement threshold `A` (out of `n`).
//!
//! Every hypothesis is checked in exact integer arithmetic; only the final error is a float.

/// `log2 |E|`.
const LOG_Q: f64 = super::ANALYSIS_LOG_Q;

/// Largest interpolation multiplicity `m` the search tries.
const MAX_MULTIPLICITY: u128 = 1 << 16;

/// The interpolation parameters `(m, D)` and the intermediate threshold `B` of Lemma 4.1's proof.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct AffineWitness {
    pub m: u128,
    pub big_d: u128,
    pub b: u128,
}

/// Johnson list bound (Lemma 3.11 with `a = agree/n`, `b = inter/n`): at most this many sets of size at least
/// `agree` in `[n]` with pairwise intersections at most `inter`. `None` below the Johnson radius.
pub(crate) fn johnson_list(n: u128, agree: u128, inter: u128) -> Option<u128> {
    let num = n.checked_mul(agree.checked_sub(inter)?)?;
    let den = agree.checked_mul(agree)?.checked_sub(n.checked_mul(inter)?)?;
    (den > 0).then(|| num / den)
}

/// `M = min(D, floor((mA - D - 1) / d))`, when it is at least 1.
fn interpolation_m(d: u128, a: u128, m: u128, big_d: u128) -> Option<u128> {
    let c = m.checked_mul(a)?.checked_sub(big_d)?.checked_sub(1)?;
    let big_m = big_d.min(c / d);
    (big_m >= 1).then_some(big_m)
}

/// `(sum_{j<=J} 1, sum j, sum j^2)`.
fn power_sums(j: u128) -> Option<(u128, u128, u128)> {
    let s1 = j.checked_mul(j + 1)? / 2;
    let s2 = j.checked_mul(j + 1)?.checked_mul(2 * j + 1)? / 6;
    Some((j + 1, s1, s2))
}

/// Lemma 4.2's interpolation inequality, exactly:
/// `sum_{j=0}^{M} (mA - D - dj)(D - j + 1) > n * sum_{s=0}^{min(m-1, M)} (m - s)(D - s + 1)`.
/// Every summand on the left is positive, since `j <= M <= floor((mA - D - 1)/d)` and `j <= M <= D`.
/// Returns `M` when it holds; an overflow counts as failure.
pub(crate) fn interpolation_holds(n: u128, d: u128, a: u128, m: u128, big_d: u128) -> Option<u128> {
    let big_m = interpolation_m(d, a, m, big_d)?;
    let c = m * a - big_d;
    let e = big_d + 1;
    let (s0, s1, s2) = power_sums(big_m)?;
    // sum (c - dj)(e - j) = c e S0 + d S2 - (c + d e) S1
    let unknowns = c
        .checked_mul(e)?
        .checked_mul(s0)?
        .checked_add(d.checked_mul(s2)?)?
        .checked_sub(c.checked_add(d.checked_mul(e)?)?.checked_mul(s1)?)?;
    let (t0, t1, t2) = power_sums((m - 1).min(big_m))?;
    // sum (m - s)(e - s) = m e T0 + T2 - (m + e) T1
    let equations = n.checked_mul(
        m.checked_mul(e)?
            .checked_mul(t0)?
            .checked_add(t2)?
            .checked_sub((m + e).checked_mul(t1)?)?,
    )?;
    (unknowns > equations).then_some(big_m)
}

/// The same ratio `unknowns / equations` in floating point, to steer the search (never to decide it).
fn interpolation_ratio(n: f64, d: f64, a: f64, m: f64, big_d: f64) -> f64 {
    let big_m = big_d.min(((m * a - big_d - 1.0) / d).floor());
    if big_m < 1.0 {
        return 0.0;
    }
    let (c, e) = (m * a - big_d, big_d + 1.0);
    let sums = |j: f64| (j + 1.0, j * (j + 1.0) / 2.0, j * (j + 1.0) * (2.0 * j + 1.0) / 6.0);
    let (s0, s1, s2) = sums(big_m);
    let (t0, t1, t2) = sums((m - 1.0).min(big_m));
    (c * e * s0 + d * s2 - (c + d * e) * s1) / (n * (m * e * t0 + t2 - (m + e) * t1))
}

/// For multiplicity `m`, the smallest `D` (past the point where `M` saturates at `floor((mA - D - 1)/d)`) satisfying
/// the interpolation inequality: a ternary search on the float ratio finds its peak, then a bisection on the exact
/// test finds the smallest feasible `D` below the peak.
fn smallest_big_d(n: u128, d: u128, a: u128, m: u128) -> Option<u128> {
    let lo = ((m * a).checked_sub(1)? / d).max(1);
    let hi = m * a / 2;
    if lo >= hi {
        return None;
    }
    let ratio = |big_d: u128| interpolation_ratio(n as f64, d as f64, a as f64, m as f64, big_d as f64);
    let (mut x, mut y) = (lo, hi);
    while y - x > 3 {
        let (x1, y1) = (x + (y - x) / 3, y - (y - x) / 3);
        if ratio(x1) < ratio(y1) { x = x1 + 1 } else { y = y1 }
    }
    let peak = (x..=y).find(|&big_d| interpolation_holds(n, d, a, m, big_d).is_some())?;
    let (mut x, mut y) = (lo, peak);
    while x < y {
        let mid = x + (y - x) / 2;
        if interpolation_holds(n, d, a, m, mid).is_some() {
            y = mid
        } else {
            x = mid + 1
        }
    }
    Some(x)
}

/// The interpolation parameters `(m, D)` with the smallest feasible `m` (which keeps `D`, hence `|E|` and `|N|`, small).
fn interpolation(n: u128, d: u128, a: u128) -> Option<(u128, u128)> {
    let gap = (a * a).checked_sub(n * d).filter(|&g| g > 0)?;
    // Feasibility needs about `m (A^2 - nd) > nd`: start there and double.
    let mut lo = (n * d / gap).max(1);
    let mut hi = lo;
    while smallest_big_d(n, d, a, hi).is_none() {
        lo = hi + 1;
        hi *= 2;
        if hi > MAX_MULTIPLICITY {
            return None;
        }
    }
    while lo < hi {
        let mid = lo + (hi - lo) / 2;
        if smallest_big_d(n, d, a, mid).is_some() {
            hi = mid
        } else {
            lo = mid + 1
        }
    }
    Some((hi, smallest_big_d(n, d, a, hi)?))
}

/// `log2 eps_aff` for a witness, after checking every hypothesis exactly:
/// `eps_aff = (D^2 + ell_B max(q, C(n, 2)) + 4 d^2 M^2 D^3 (n / (A - B))^2) / q^2`,
/// with `ell_B` the Johnson list at agreement `B` against degree `d + 1`.
pub(crate) fn affine_error_log2(n: u128, d: u128, a: u128, w: &AffineWitness) -> Option<f64> {
    let big_m = interpolation_holds(n, d, a, w.m, w.big_d)?;
    if !(d + 1 < w.b && w.b < a) {
        return None;
    }
    let ell_b = johnson_list(n, w.b, d + 1)?;
    let (nf, df, mf, bd) = (n as f64, d as f64, big_m as f64, w.big_d as f64);
    let q = LOG_Q.exp2();
    let pairs = nf * (nf - 1.0) / 2.0;
    let interp = 4.0 * df * df * mf * mf * bd.powi(3) * (nf / (a - w.b) as f64).powi(2);
    Some((bd * bd + ell_b as f64 * q.max(pairs) + interp).log2() - 2.0 * LOG_Q)
}

/// A witness for `(n, d, A)`: the smallest feasible `m` and its smallest `D`, then the `B = A - 2^i` minimising the
/// bound.
pub(crate) fn find_witness(n: u128, d: u128, a: u128) -> Option<(AffineWitness, f64)> {
    let (m, big_d) = interpolation(n, d, a)?;
    let mut best: Option<(AffineWitness, f64)> = None;
    for i in 0..u128::BITS {
        let Some(b) = a.checked_sub(1 << i) else { break };
        let w = AffineWitness { m, big_d, b };
        match affine_error_log2(n, d, a, &w) {
            Some(err) if best.is_none_or(|(_, e)| err < e) => best = Some((w, err)),
            Some(_) => {}
            None if b <= d + 1 || johnson_list(n, b, d + 1).is_none() => break,
            None => {}
        }
    }
    best
}

/// Errors (log2) of one fold round against degree `d` at threshold `A`: `theta` costs `ell(A - 1, d) / q`, and
/// `(gamma, alpha, beta)` costs `eps_aff + 2 ell(A - 1, d) / q`.
pub(crate) fn fold_round_errors_log2(n: u128, d: u128, a: u128, w: &AffineWitness) -> Option<(f64, f64)> {
    let ell = johnson_list(n, a - 1, d)? as f64;
    let theta = ell.log2() - LOG_Q;
    let eps_aff = affine_error_log2(n, d, a, w)?;
    let combiner = (eps_aff.exp2() + 2.0 * (theta.exp2())).log2();
    Some((theta, combiner))
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The paper's worked example: `n = 2^20`, `d = 2^18`, `A = 576717`, `m = 3`, `D = 49`, `B = 567980`.
    #[test]
    fn worked_example() {
        let (n, d, a) = (1u128 << 20, 1u128 << 18, 576_717u128);
        let w = AffineWitness {
            m: 3,
            big_d: 49,
            b: 567_980,
        };
        assert_eq!(interpolation_holds(n, d, a, w.m, w.big_d), Some(6));
        assert_eq!(johnson_list(n, w.b, d + 1), Some(6));
        assert_eq!(johnson_list(n, a - 1, d), Some(5));
        let correction = (4 * d * d * 36 * 49u128.pow(3)) as f64 * (n as f64 / (a - w.b) as f64).powi(2);
        assert!(correction.log2() - 2.0 * LOG_Q < -182.0);
        // The bound is the list term, `ell_B / q`.
        let err = affine_error_log2(n, d, a, &w).unwrap();
        assert!((err - (6f64.log2() - LOG_Q)).abs() < 1e-9);
        // The search does at least as well.
        let (_, found) = find_witness(n, d, a).unwrap();
        assert!(found <= err + 1e-9);
    }

    /// The closed forms against the sums they replace.
    #[test]
    fn closed_form_matches_the_sums() {
        let mut state = 0x9e37_79b9_7f4a_7c15u64;
        let mut next = |bound: u64| {
            state = state
                .wrapping_mul(6_364_136_223_846_793_005)
                .wrapping_add(1_442_695_040_888_963_407);
            (state >> 33) % bound
        };
        for _ in 0..2000 {
            let n = 1u128 << (8 + next(7));
            let d = 1 + next(n as u64 / 2) as u128;
            let a = d + 1 + next((n - d) as u64) as u128;
            let (m, big_d) = (1 + next(40) as u128, 1 + next(300) as u128);
            let reference = interpolation_m(d, a, m, big_d).and_then(|big_m| {
                let unknowns: u128 = (0..=big_m).map(|j| (m * a - big_d - d * j) * (big_d - j + 1)).sum();
                let equations: u128 = n
                    * (0..=(m - 1).min(big_m))
                        .map(|s| (m - s) * (big_d - s + 1))
                        .sum::<u128>();
                (unknowns > equations).then_some(big_m)
            });
            assert_eq!(
                interpolation_holds(n, d, a, m, big_d),
                reference,
                "{n} {d} {a} {m} {big_d}"
            );
        }
    }
}
