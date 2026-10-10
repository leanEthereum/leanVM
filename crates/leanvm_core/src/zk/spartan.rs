//! The outer zero-knowledge Spartan over `E`.
//!
//! It proves `sum_x eq(τ, x)·F(x) = 0` for `F = Ã·B̃ + C̃`, the row products of an [`R1cs`] over a witness the caller commits elsewhere, and ends in two linear claims the caller discharges with its own opening: one on the witness, one on the Libra mask `g(X) = g_c + sum_j (g_{j0} + g_{j1} X_j) X_j`, which the caller commits too.
//!
//! The rows form the cube `{0,1}^ℓ`, `x = sum_i x_i 2^i`, variable 0 bound first.
//!
//! Zero knowledge needs no padding:
//! - each round's `c_1` and `c_2` are those of `F` plus `α` times the mask's fresh `(g_{i0}, g_{i1})`, the eq-weighted MLE-check mask of the Binius64 whitepaper;
//! - the mask's sum `s_g` is hidden by `g_c`;
//! - the final `(a, b, c)` are hidden by the two dummy constraints ([`R1cs::push_dummies`]), whose fresh operands sit at rows of their own.
//!
//! The characteristic-2 argument rests on the Binius64 whitepaper's MLE-check theorem and is unreviewed.

use super::r1cs::R1cs;
use fiat_shamir::arith::{Arith, Native, Verifier};
use fiat_shamir::transcript::{TranscriptError, Transmitter};
use primitives::field::F192;
use primitives::multilinear::{eq_table, interp};

/// What the outer proof leaves to the caller's commitment opening.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct OuterClaims<E = F192> {
    /// `⟨witness_weight, z[1..]⟩ = witness_target`.
    pub(crate) witness_weight: Vec<E>,
    pub(crate) witness_target: E,
    /// `⟨libra_weight, libra⟩ = libra_target`: the mask at the sumcheck's point.
    pub(crate) libra_weight: Vec<E>,
    pub(crate) libra_target: E,
}

/// The Libra mask's coefficients over `log_rows` variables: `[g_c, g_00, g_01, g_10, g_11, ...]`.
pub(crate) const fn libra_len(log_rows: usize) -> usize {
    1 + 2 * log_rows
}

/// Prove `z` satisfies `r1cs`, with the Libra mask `libra` the caller committed.
///
/// # Panics
///
/// If `z` does not satisfy `r1cs`, or `libra` is not [`libra_len`] long.
pub(crate) fn prove(ps: &mut impl Transmitter, r1cs: &R1cs, z: &[F192], libra: &[F192]) -> OuterClaims {
    assert_eq!(z.first(), Some(&F192::ONE), "column 0 is the constant one");
    let products = r1cs.products(z);
    let [az, bz, cz] = &products;
    assert!(
        (az.iter().zip(bz).zip(cz)).all(|((&a, &b), &c)| a * b == c),
        "the witness satisfies the system"
    );
    prove_products(ps, r1cs, products, libra)
}

/// The prover's steps on `Az`, `Bz`, `Cz`, whatever they satisfy.
fn prove_products(ps: &mut impl Transmitter, r1cs: &R1cs, products: [Vec<F192>; 3], libra: &[F192]) -> OuterClaims {
    let log_rows = r1cs.log_rows();
    assert_eq!(libra.len(), libra_len(log_rows), "a mask of the system's size");
    let [mut az, mut bz, mut cz] = products;
    let (g_c, g) = (libra[0], libra[1..].as_chunks::<2>().0);

    let tau = ps.sample_vec(log_rows);
    // `sum_j τ_j g_j(1)`, the mask's share of the variables still free.
    let mut suffix = (tau.iter().zip(g)).fold(F192::ZERO, |acc, (&t, &[g0, g1])| acc + t * (g0 + g1));
    ps.add_scalar(g_c + suffix);
    let alpha = ps.sample();

    // `g_c + sum_{j<i} g_j(r_j) r_j`, the mask's share of the variables bound.
    let mut prefix = g_c;
    let mut r = Vec::with_capacity(log_rows);
    for (i, &[g0, g1]) in g.iter().enumerate() {
        suffix += tau[i] * (g0 + g1);
        let eq = eq_table(&tau[i + 1..]);
        let mut coeffs = [F192::ZERO; 3];
        let pairs = (az.as_chunks::<2>().0.iter().zip(bz.as_chunks::<2>().0)).zip(cz.as_chunks::<2>().0);
        for (((a, b), c), &e) in pairs.zip(&eq) {
            let (da, db) = (a[0] + a[1], b[0] + b[1]);
            coeffs[0] += e * (a[0] * b[0] + c[0]);
            coeffs[1] += e * (a[0] * db + da * b[0] + c[0] + c[1]);
            coeffs[2] += e * da * db;
        }
        coeffs[0] += alpha * (prefix + suffix);
        coeffs[1] += alpha * g0;
        coeffs[2] += alpha * g1;
        ps.add_round_poly(&coeffs, true);
        let ri = ps.sample();
        prefix += (g0 + g1 * ri) * ri;
        for table in [&mut az, &mut bz, &mut cz] {
            fold_low(table, ri);
        }
        r.push(ri);
    }

    let evals = [az[0], bz[0], cz[0]];
    ps.add_scalars(&evals);
    let gamma = ps.sample();
    let libra_weight = libra_weight(&mut Native, &r);
    let libra_target = (libra.iter().zip(&libra_weight)).fold(F192::ZERO, |acc, (&g, &w)| acc + g * w);
    claims(
        &mut Native,
        r1cs,
        &eq_table(&r),
        evals,
        gamma,
        libra_target,
        libra_weight,
    )
}

/// Verify the outer proof as far as the verifier can without the witness, returning what is left to the caller.
///
/// # Errors
///
/// Returns an error on a malformed stream: having no witness, the verifier refuses nothing else.
pub(crate) fn verify<V: Verifier>(v: &mut V, r1cs: &R1cs) -> Result<OuterClaims<V::E>, TranscriptError> {
    let log_rows = r1cs.log_rows();
    let tau = v.sample_vec(log_rows);
    let s_g = v.next_scalar()?;
    let alpha = v.sample();
    // The system's sum is zero, so the claim is the mask's alone.
    let mut s = v.mul(alpha, s_g);
    let mut r = Vec::with_capacity(log_rows);
    for &t in &tau {
        let coeffs = v.next_round_poly(3, s, Some(t))?;
        let ri = v.sample();
        s = v.poly_eval(&coeffs, ri);
        r.push(ri);
    }

    let [a, b, c] = [v.next_scalar()?, v.next_scalar()?, v.next_scalar()?];
    // `s = F(r) + α·g(r)`.
    let f = v.mul_add(a, b, c);
    let masked = v.add(s, f);
    let alpha_inv = v.inv(alpha);
    let libra_target = v.mul(masked, alpha_inv);
    let gamma = v.sample();
    let libra_weight = libra_weight(v, &r);
    let eq = v.eq_table_prefix(&r, r1cs.n_rows());
    Ok(claims(v, r1cs, &eq, [a, b, c], gamma, libra_target, libra_weight))
}

/// `[1, r_0, r_0^2, r_1, r_1^2, ...]`, so that `⟨libra, weight⟩ = g(r)`.
fn libra_weight<A: Arith>(ar: &mut A, r: &[A::E]) -> Vec<A::E> {
    let mut weight = Vec::with_capacity(libra_len(r.len()));
    weight.push(ar.one());
    for &ri in r {
        let sq = ar.square(ri);
        weight.extend([ri, sq]);
    }
    weight
}

/// The two claims, from `(a, b, c)` and `eq(r, x)` for the first `n_rows` rows `x` at least.
///
/// `t_y = sum_x eq(r, x)(A[x][y] + γ B[x][y] + γ^2 C[x][y])` gives `⟨t, z⟩ = a + γ b + γ^2 c`, and `z_0 = 1` moves `t_0` to the target.
fn claims<A: Arith>(
    ar: &mut A,
    r1cs: &R1cs,
    eq: &[A::E],
    [a, b, c]: [A::E; 3],
    gamma: A::E,
    libra_target: A::E,
    libra_weight: Vec<A::E>,
) -> OuterClaims<A::E> {
    let zero = ar.zero();
    let mut t = vec![zero; r1cs.n_cols];
    for (x, &e) in eq[..r1cs.n_rows()].iter().enumerate() {
        let eb = ar.mul(e, gamma);
        let ec = ar.mul(eb, gamma);
        for (rows, w) in [(&r1cs.a, e), (&r1cs.b, eb), (&r1cs.c, ec)] {
            for &(y, coef) in &rows[x] {
                t[y as usize] = ar.mul_const_add(w, coef, t[y as usize]);
            }
        }
    }
    let bc = ar.mul_add(c, gamma, b);
    let abc = ar.mul_add(bc, gamma, a);
    let witness_target = ar.add(abc, t[0]);
    t.remove(0);
    OuterClaims {
        witness_weight: t,
        witness_target,
        libra_weight,
        libra_target,
    }
}

/// Bind a table's lowest variable to `r`.
fn fold_low(table: &mut Vec<F192>, r: F192) {
    let half = table.len() / 2;
    for k in 0..half {
        table[k] = interp(table[2 * k], table[2 * k + 1], r);
    }
    table.truncate(half);
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::zk::r1cs::{N_DUMMIES, dummy_values};
    use fiat_shamir::transcript::{ProofTranscript, ProverState, VerifierState};
    use primitives::test_util::Rng;

    const LABEL: &[u8] = b"zk-spartan-test";
    const N_WITNESS: usize = 200;
    const N_ROWS: usize = 300;

    /// A random satisfiable system over `z = (1, w, dummies)`, its dummies pushed last.
    fn instance(rng: &mut Rng) -> (R1cs, Vec<F192>) {
        let n_cols = 1 + N_WITNESS + N_DUMMIES;
        let mut z = vec![F192::ONE];
        z.extend(rng.ext_vec(N_WITNESS));
        z.extend(dummy_values(|| rng.ext()));
        let mut r1cs = R1cs {
            n_cols,
            ..R1cs::default()
        };
        let col = |rng: &mut Rng| (rng.next_u32() as usize % (N_WITNESS + 1)) as u32;
        let row = |rng: &mut Rng, n: usize| -> Vec<(u32, F192)> { (0..n).map(|_| (col(rng), rng.ext())).collect() };
        for _ in 0..N_ROWS {
            let (a, b, mut c) = (row(rng, 3), row(rng, 2), row(rng, 2));
            let value = |row: &[(u32, F192)]| row.iter().fold(F192::ZERO, |acc, &(y, k)| acc + k * z[y as usize]);
            // A last entry on a nonzero witness column closes the row.
            let y = 1 + rng.next_u32() as usize % N_WITNESS;
            let gap = value(&a) * value(&b) + value(&c);
            c.push((y as u32, gap * z[y].inv()));
            r1cs.a.push(a);
            r1cs.b.push(b);
            r1cs.c.push(c);
        }
        r1cs.push_dummies(1 + N_WITNESS);
        assert!(r1cs.is_satisfied(&z));
        (r1cs, z)
    }

    fn libra(rng: &mut Rng, r1cs: &R1cs) -> Vec<F192> {
        rng.ext_vec(libra_len(r1cs.log_rows()))
    }

    fn dot(w: &[F192], v: &[F192]) -> F192 {
        assert_eq!(w.len(), v.len());
        w.iter().zip(v).fold(F192::ZERO, |acc, (&a, &b)| acc + a * b)
    }

    /// Whether both claims hold against the witness and the mask.
    fn holds(claims: &OuterClaims, z: &[F192], libra: &[F192]) -> bool {
        dot(&claims.witness_weight, &z[1..]) == claims.witness_target
            && dot(&claims.libra_weight, libra) == claims.libra_target
    }

    fn run(r1cs: &R1cs, z: &[F192], libra: &[F192]) -> (OuterClaims, ProofTranscript) {
        let mut ps = ProverState::from_label(LABEL);
        let claims = prove(&mut ps, r1cs, z, libra);
        (claims, ps.into_proof())
    }

    fn check(r1cs: &R1cs, proof: &ProofTranscript) -> Result<OuterClaims, TranscriptError> {
        let mut v = VerifierState::from_label(LABEL, proof);
        let claims = verify(&mut v, r1cs)?;
        v.finish()?;
        Ok(claims)
    }

    #[test]
    fn honest_claims_hold() {
        let mut rng = Rng::new(1);
        let (r1cs, z) = instance(&mut rng);
        let libra = libra(&mut rng, &r1cs);
        let (proved, proof) = run(&r1cs, &z, &libra);
        let verified = check(&r1cs, &proof).unwrap();
        assert_eq!(proved, verified);
        assert!(holds(&verified, &z, &libra));
    }

    #[test]
    fn unsatisfied_witness_fails_a_claim() {
        let mut rng = Rng::new(2);
        let (r1cs, mut z) = instance(&mut rng);
        let libra = libra(&mut rng, &r1cs);
        // Column 1 sits in some row, so that row now fails.
        z[1] += F192::ONE;
        assert!(!r1cs.is_satisfied(&z));
        let mut ps = ProverState::from_label(LABEL);
        prove_products(&mut ps, &r1cs, r1cs.products(&z), &libra);
        let claims = check(&r1cs, &ps.into_proof()).unwrap();
        assert!(!holds(&claims, &z, &libra));
    }

    #[test]
    fn tampered_proof_fails_a_claim() {
        let mut rng = Rng::new(3);
        let (r1cs, z) = instance(&mut rng);
        let libra = libra(&mut rng, &r1cs);
        let (_, proof) = run(&r1cs, &z, &libra);
        // The stream is `s_g`, then `(c_1, c_2)` per round, then `(a, b, c)`.
        let a = 1 + 2 * r1cs.log_rows();
        for (what, at) in [("s_g", 0), ("a round coefficient", 3), ("a", a)] {
            let mut tampered = proof.clone();
            tampered.stream[at] += F192::ONE;
            let refused = check(&r1cs, &tampered).map_or(true, |claims| !holds(&claims, &z, &libra));
            assert!(refused, "a tampered {what} is accepted");
        }
    }

    #[test]
    fn fresh_masks_share_no_scalar() {
        let mut rng = Rng::new(4);
        let (r1cs, z) = instance(&mut rng);
        let mut z2 = z.clone();
        z2[z.len() - N_DUMMIES..].copy_from_slice(&dummy_values(|| rng.ext()));
        assert!(r1cs.is_satisfied(&z2));
        let (_, first) = run(&r1cs, &z, &libra(&mut rng, &r1cs));
        let (_, second) = run(&r1cs, &z2, &libra(&mut rng, &r1cs));
        assert_eq!(first.stream.len(), second.stream.len());
        assert!(first.stream.iter().all(|x| !second.stream.contains(x)));
    }
}
