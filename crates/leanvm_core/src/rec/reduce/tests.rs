use super::{DenseProver, DenseTables, DenseVars, LABEL, MatrixProver, MatrixReduced, ReduceError};
use crate::class_flock::FlockId;
use crate::cpu::Claim;
use crate::rec::claims::{DenseClaim, DensePoly, MatrixClaim};
use crate::tables::TableId;
use fiat_shamir::arith::{Arith, Native};
use fiat_shamir::transcript::{Challenger, ProverState, Transmitter, VerifierState};
use flock::lincheck::MatrixForm;
use primitives::field::{F64, F192};
use primitives::multilinear::{eq_table, mle_eval};
use primitives::test_util::Rng;

fn dense_claims(rng: &mut Rng, tables: &DenseTables, vars: &DenseVars) -> Vec<DenseClaim<F192>> {
    let mut claims = Vec::new();
    for poly in DensePoly::ALL {
        let table = &tables[poly];
        for _ in 0..2 {
            let point = rng.ext_vec(vars[poly]);
            let value = mle_eval(table, &point);
            claims.push(DenseClaim::at(poly, point, None, value));
        }
    }
    let n = vars[DensePoly::Fixed];
    let low = rng.ext_vec(n - 3);
    // Claims whose points end on Boolean coordinates, the last one a kind, one of them vacuous.
    let mut term = |n_low: usize, bits: usize, top: u64, scale: F192| {
        let mut point = low[..n_low].to_vec();
        point.extend((0..n - 1 - n_low).map(|i| F192::new((bits >> i & 1) as u64, 0, 0)));
        point.push(F192::new(top, 0, 0));
        let value = mle_eval(&tables[DensePoly::Fixed], &point);
        claims.push(DenseClaim::at(DensePoly::Fixed, point, Some(scale), value));
    };
    term(n - 3, 1, 0, rng.ext());
    term(n - 4, 2, 1, rng.ext());
    term(n - 3, 0, 1, F192::ZERO);
    claims
}

#[test]
fn the_dense_reduction_reduces_to_the_polynomials() {
    let mut rng = Rng::new(17);
    let vars = DenseVars([3, 6, 7]);
    let tables = DenseTables(vars.0.map(|n| (0..1 << n).map(|_| F64(rng.next_u64())).collect()));
    let claims = dense_claims(&mut rng, &tables, &vars);
    let prove = |claims: &[DenseClaim<F192>], forge: bool| {
        let mut ps = ProverState::from_label(LABEL);
        if forge {
            // A cheating prover: honest rounds, then values that meet the final identity of the claims as stated.
            let theta = ps.sample();
            let mut p = DenseProver::new(&vars, &tables, claims, theta);
            let powers = Native.powers(theta, claims.len());
            let mut claim = (claims.iter().zip(&powers)).fold(F192::ZERO, |acc, (t, &w)| {
                acc + w * t.scale.unwrap_or(F192::ONE) * t.value
            });
            let point: Vec<F192> = (0..p.rounds())
                .map(|i| {
                    let [c0, c2] = p.message();
                    ps.add_scalars(&[c0, c2]);
                    let r = ps.sample();
                    claim = c0 + (claim + c2) * r + c2 * r * r;
                    p.bind(i, r);
                    r
                })
                .collect();
            let weights: Vec<F192> = vars
                .final_weights(&mut Native, claims, &powers, &point)
                .into_iter()
                .flatten()
                .collect();
            let mut values = p.finals();
            let rest = (values.iter().zip(&weights).skip(1)).fold(F192::ZERO, |acc, (&v, &w)| acc + v * w);
            values[0] = (claim + rest) * weights[0].inv();
            ps.add_scalars(&values);
        } else {
            DenseProver::prove(&mut ps, &vars, &tables, claims);
        }
        ps.into_proof()
    };
    let verify = |claims: &[DenseClaim<F192>], proof| {
        let mut vs = VerifierState::from_label(LABEL, proof);
        vars.verify(&mut vs, claims)
    };

    let proof = prove(&claims, false);
    let reduced = verify(&claims, &proof).expect("an honest reduction");
    for poly in DensePoly::ALL {
        let point = &reduced.point[..vars[poly]];
        assert_eq!(
            reduced.values[poly as usize],
            Some(mle_eval(&tables[poly], point)),
            "{poly:?}"
        );
    }

    // A false claim: the honest prover's reduction is refused, and a cheating prover's reduces it to a false value.
    let mut false_claims = claims;
    false_claims[7].value += F192::ONE;
    assert_eq!(verify(&false_claims, &proof).err(), Some(ReduceError::Dense));
    let forged = prove(&false_claims, true);
    let reduced = verify(&false_claims, &forged).expect("the forgery meets the final identity");
    let falsified = DensePoly::ALL.into_iter().filter(|&poly| {
        let point = &reduced.point[..vars[poly]];
        reduced.values[poly as usize] != Some(mle_eval(&tables[poly], point))
    });
    assert!(falsified.count() > 0, "a false claim reduced to true values");
}

// Claims on `poly` that each weigh one block: `(n_low, bits)` names the `2^n_low` entries at `bits << n_low`.
fn block_claims(
    rng: &mut Rng,
    tables: &DenseTables,
    vars: &DenseVars,
    poly: DensePoly,
    blocks: &[(usize, usize)],
) -> Vec<DenseClaim<F192>> {
    let n = vars[poly];
    let low = rng.ext_vec(n);
    (blocks.iter())
        .map(|&(n_low, bits)| {
            let mut point = low[..n_low].to_vec();
            point.extend((0..n - n_low).map(|i| F192::new((bits >> i & 1) as u64, 0, 0)));
            let value = mle_eval(&tables[poly], &point);
            DenseClaim::at(poly, point, Some(rng.ext()), value)
        })
        .collect()
}

#[test]
fn the_dense_reduction_reduces_claims_on_a_prefix() {
    // Weights zero past a prefix whose length is odd at several rounds, so the prover evaluates the table past it. The
    // blocks of the image and the fixed polynomial have one or two low points, so their weights stay factored for a few
    // rounds; the bytecode's has three, written out at once.
    let mut rng = Rng::new(23);
    let vars = DenseVars([3, 5, 14]);
    let tables = DenseTables(vars.0.map(|n| (0..1 << n).map(|_| F64(rng.next_u64())).collect()));
    let mut claims: Vec<DenseClaim<F192>> = (0..3)
        .map(|_| {
            let point = rng.ext_vec(3);
            let value = mle_eval(&tables[DensePoly::Bytecode], &point);
            DenseClaim::at(DensePoly::Bytecode, point, None, value)
        })
        .collect();
    claims.extend(block_claims(&mut rng, &tables, &vars, DensePoly::Image, &[(1, 2)]));
    let blocks = [(2, 0xAAA), (5, 7), (2, 0xAAA)];
    claims.extend(block_claims(&mut rng, &tables, &vars, DensePoly::Fixed, &blocks));
    claims.extend(block_claims(&mut rng, &tables, &vars, DensePoly::Fixed, &[(5, 7)]));
    let mut ps = ProverState::from_label(LABEL);
    DenseProver::prove(&mut ps, &vars, &tables, &claims);
    let proof = ps.into_proof();
    let mut vs = VerifierState::from_label(LABEL, &proof);
    let reduced = vars.verify(&mut vs, &claims).expect("an honest reduction");
    for poly in DensePoly::ALL {
        let point = &reduced.point[..vars[poly]];
        assert_eq!(
            reduced.values[poly as usize],
            Some(mle_eval(&tables[poly], point)),
            "{poly:?}"
        );
    }
}

// Each circuit's matrices at random points: lincheck claims and both carried claims, on three circuits.
//
// The lincheck claims share their points as one batch leaves them: one alpha and one skip point, the other coordinates
// prefixes of shared ones; circuit 0 has a second claim at its first's point with other slices.
fn matrix_claims(rng: &mut Rng) -> Vec<MatrixClaim<F192>> {
    let k_skip = flock::zerocheck::K_SKIP;
    let (alpha, z_skip) = (rng.ext(), rng.ext());
    let (x, r) = (rng.ext_vec(16), rng.ext_vec(16));
    let mut claims = Vec::new();
    let first = FlockId::ALL[0];
    for (i, f) in [first, first, FlockId::ALL[3], FlockId::clock(TableId::HASH)]
        .into_iter()
        .enumerate()
    {
        let circuit = f.circuit();
        let k = circuit.k_log();
        let form = MatrixForm {
            alpha,
            z_skip,
            x_inner_rest: x[..k - k_skip].to_vec(),
            r_inner_rest: r[..k - k_skip].to_vec(),
            s_hat_v: rng.ext_vec(1 << k_skip),
        };
        let value = form.evaluate(circuit);
        claims.push(MatrixClaim::fresh(f, &Claim { point: form, value }));
        if i == 0 {
            continue;
        }
        let (rows, cols) = (rng.ext_vec(k), rng.ext_vec(k));
        let (ra, rb) = circuit.row_values(&eq_table(&cols));
        let u = eq_table(&rows);
        let dot = |r: &[F192]| u.iter().zip(r).fold(F192::ZERO, |acc, (&x, &y)| acc + x * y);
        claims.extend(MatrixClaim::carried(f, k, &rows, &cols, [dot(&ra), dot(&rb)]));
    }
    claims
}

#[test]
fn the_matrix_reduction_reduces_to_the_matrices() {
    let mut rng = Rng::new(9);
    let claims = matrix_claims(&mut rng);
    let prove = |claims: &[MatrixClaim<F192>]| {
        let mut ps = ProverState::from_label(LABEL);
        MatrixProver::prove(&mut ps, claims);
        ps.into_proof()
    };
    let verify = |claims: &[MatrixClaim<F192>], proof| {
        let mut vs = VerifierState::from_label(LABEL, proof);
        MatrixReduced::verify(&mut vs, claims)
    };
    let proof = prove(&claims);
    let reduced = verify(&claims, &proof).expect("an honest reduction");
    for (f, values) in FlockId::ALL.into_iter().zip(&reduced.values) {
        let circuit = f.circuit();
        let k = circuit.k_log();
        let (ra, rb) = circuit.row_values(&eq_table(&reduced.cols[..k]));
        let u = eq_table(&reduced.rows[..k]);
        let dot = |r: &[F192]| u.iter().zip(r).fold(F192::ZERO, |acc, (&x, &y)| acc + x * y);
        assert_eq!(*values, [dot(&ra), dot(&rb)], "{f:?}");
    }
    for c in [0, 2] {
        let mut false_claims = claims.clone();
        false_claims[c].value += F192::ONE;
        assert_eq!(
            verify(&false_claims, &proof).err(),
            Some(ReduceError::Matrix),
            "claim {c}"
        );
    }
}
