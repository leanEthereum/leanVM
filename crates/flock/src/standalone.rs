//! Flock on its own, shaped for a verifier that pays for every scalar it reads.
//!
//! The statement is a batch of `2^n_log` instances of one block R1CS over GF(2), `(A_0 z) * (B_0 z) = z` per block.
//! The proof is three sumchecks and nothing else:
//!
//! 1. [`crate::zerocheck::prove_multilinear`]: `m = k_log + n_log` rounds, leaving `â`, `b̂`, `ĉ` at one point.
//! 2. [`crate::lincheck::prove_multilinear`]: `k_log` rounds over the columns, leaving the 64 bit slices of `z` and one evaluation of the matrices.
//! 3. Ring switching ([`pcs::ring_switch`]) as its own sumcheck over the packed witness, leaving one evaluation of it.
//!
//! Two plain multilinear evaluation claims come out ([`Claims`]), each for a polynomial commitment to answer ([`opening`] below):
//! the witness's, committed by the prover, and the matrices', committed once and for all.
//! The verifier never touches the circuit, so its work does not depend on what the block computes.
//!
//! The matrices are one polynomial in `2 k_log + 1` variables, [`stacked_matrix_index`]: `A_0` then `A_0 + B_0`.
//! Lincheck batches its two matrix claims with `alpha`, and `Ã_0 + alpha * B̃_0` is that polynomial with its last coordinate at `alpha`.

use fiat_shamir::transcript::{Challenger, ProverState, Receiver, Transmitter, VerifierState};
use pcs::pack::LOG_PACKING;
use pcs::ring_switch;
use primitives::field::{F64, F192};
use primitives::multilinear::{eq_table, lagrange_weights_naive, poly_eval};

use crate::lincheck::{self, LincheckCircuit, RowPoint};
use crate::zerocheck::{self, PaddingSpec};

/// `polynomial(point) = value`, the point low variable first.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Claim {
    pub point: Vec<F192>,
    pub value: F192,
}

/// What a proof leaves to the two commitments.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Claims {
    /// On the packed witness, `k_log + n_log - 6` variables.
    pub witness: Claim,
    /// On the stacked matrices, `2 k_log + 1` variables.
    pub matrix: Claim,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum VerifyError {
    Zerocheck(zerocheck::VerifyError),
    Lincheck(lincheck::VerifyError),
    MatrixSkip,
    RingSwitch,
    Transcript(fiat_shamir::transcript::Error),
}

/// Index of entry `(row, col)` of matrix `s` in the stacked table: `s = 0` is `A_0`, `s = 1` is `A_0 + B_0`.
pub fn stacked_matrix_index(k_log: usize, row: usize, col: usize, s: usize) -> usize {
    row | col << k_log | s << (2 * k_log)
}

/// The packed witness's prover-side views: `z`, `A z` and `B z` as words, and `z` in lincheck's stripe layout.
#[derive(Clone, Copy, Debug)]
pub struct Witness<'a> {
    pub z: &'a [u64],
    pub a: &'a [u64],
    pub b: &'a [u64],
    pub z_lincheck: &'a [u8],
}

/// The zerocheck's claims, whichever way its first six variables were bound.
struct RowClaims {
    /// The univariate-skip challenge, when the zerocheck skipped.
    z: Option<F192>,
    /// The multilinear coordinates: all `m` of them, or the `m - 6` past the skip.
    point: Vec<F192>,
    evals: [F192; 3],
}

impl RowClaims {
    /// Split at the block: the row point lincheck runs at, and the instance point.
    fn split(&self, k_log: usize) -> (RowPoint<'_>, &[F192]) {
        match self.z {
            None => (RowPoint::Multilinear(&self.point[..k_log]), &self.point[k_log..]),
            Some(z) => {
                let (rest, outer) = self.point.split_at(k_log - LOG_PACKING);
                (RowPoint::Skip { z, rest }, outer)
            }
        }
    }
}

/// Prove the batch. The caller has bound the statement and both commitments into `ps`.
///
/// `skip` runs the zerocheck with its univariate skip: a faster prover, for 64 scalars in place of six rounds, and a
/// matrix claim whose six low row variables then take a sumcheck of their own to become multilinear.
pub fn prove(
    circuit: &dyn LincheckCircuit,
    useful_bits: usize,
    n_log: usize,
    skip: bool,
    witness: Witness<'_>,
    ps: &mut ProverState,
) -> Claims {
    let k_log = circuit.n_cols().trailing_zeros() as usize;
    let m = k_log + n_log;
    let padding = PaddingSpec {
        k_log,
        useful_bits_per_block: useful_bits,
    };
    let zc = tracing::info_span!("Zerocheck").in_scope(|| {
        if skip {
            let bytes = crate::witness::packed_bytes;
            let zc =
                zerocheck::prove_packed_padded(bytes(witness.a), bytes(witness.b), bytes(witness.z), m, &padding, ps);
            RowClaims {
                z: Some(zc.z),
                point: zc.mlv_challenges,
                evals: [zc.a_eval, zc.b_eval, zc.c_eval],
            }
        } else {
            let zc = zerocheck::prove_multilinear(witness.a, witness.b, witness.z, m, &padding, ps);
            RowClaims {
                z: None,
                point: zc.point,
                evals: [zc.a_eval, zc.b_eval, zc.c_eval],
            }
        }
    });
    let (rows, x_outer) = zc.split(k_log);
    let lc = tracing::info_span!("Lincheck").in_scope(|| {
        lincheck::prove_multilinear(
            witness.z_lincheck,
            m,
            k_log,
            LOG_PACKING,
            useful_bits,
            circuit,
            rows,
            x_outer,
            ps,
        )
    });

    let matrix = match rows {
        RowPoint::Multilinear(x_inner) => matrix_claim(x_inner, &lc, lc.matrix_eval),
        RowPoint::Skip { z, rest } => tracing::info_span!("Matrix skip").in_scope(|| {
            // The matrices at each boolean value of the skipped row variables, one backward walk apiece.
            let (eq_rest, eq_cols) = (eq_table(rest), eq_table(&lc.r_cols));
            let at_rows: Vec<F192> = (0..1 << LOG_PACKING)
                .map(|i| {
                    let mut rows = vec![F192::ZERO; 1 << k_log];
                    for (j, &e) in eq_rest.iter().enumerate() {
                        rows[i | j << LOG_PACKING] = e;
                    }
                    ring_switch::inner_product_ext(&circuit.fold_alpha_batched(lc.alpha, &rows), &eq_cols)
                })
                .collect();
            let weights = lagrange_weights_naive(LOG_PACKING, z);
            let (rho, _, value, _) = lincheck::product_sumcheck(weights, at_rows, 0, ps);
            ps.add_scalar(value);
            let x_inner: Vec<F192> = rho.iter().chain(rest).copied().collect();
            matrix_claim(&x_inner, &lc, value)
        }),
    };

    let _span = tracing::info_span!("Ring switch").entered();
    let suffix = suffix_point(&lc.r_cols, x_outer);
    let challenges = ring_switch::sample_map_challenges(ps);
    let weights = ring_switch::dense_weights(&suffix, &challenges);
    let packed = parallel::map_collect(witness.z.len(), |i| F192::from(F64(witness.z[i])));
    let (point, _, value, _) = lincheck::product_sumcheck(weights, packed, 0, ps);
    ps.add_scalar(value);

    Claims {
        witness: Claim { point, value },
        matrix,
    }
}

/// The verifier's side of [`lincheck::product_sumcheck`]: `n` rounds from `claim`, then the value the prover says
/// its second table takes at the point. Returns the point, low variable first, the final claim and that value.
fn verify_product_rounds(
    n: usize,
    mut claim: F192,
    vs: &mut VerifierState<'_>,
) -> Result<(Vec<F192>, F192, F192), VerifyError> {
    let mut point = Vec::with_capacity(n);
    for _ in 0..n {
        let q = vs.next_round_poly(3, claim, None).map_err(VerifyError::Transcript)?;
        let r = vs.sample();
        claim = poly_eval(&q, r);
        point.push(r);
    }
    point.reverse();
    let value = vs.next_scalar().map_err(VerifyError::Transcript)?;
    Ok((point, claim, value))
}

/// Verify a proof down to its two claims: it holds if both are true of the committed polynomials.
pub fn verify(
    k_log: usize,
    pin_col: usize,
    n_log: usize,
    skip: bool,
    vs: &mut VerifierState<'_>,
) -> Result<Claims, VerifyError> {
    let m = k_log + n_log;
    let zc = if skip {
        let zc = zerocheck::verify(m, vs).map_err(VerifyError::Zerocheck)?;
        RowClaims {
            z: Some(zc.z),
            point: zc.mlv_challenges,
            evals: [zc.a_eval, zc.b_eval, zc.c_eval],
        }
    } else {
        let zc = zerocheck::verify_multilinear(m, vs).map_err(VerifyError::Zerocheck)?;
        RowClaims {
            z: None,
            point: zc.point,
            evals: [zc.a_eval, zc.b_eval, zc.c_eval],
        }
    };
    let (rows, x_outer) = zc.split(k_log);
    let [v_a, v_b, v_c] = zc.evals;
    let lc = lincheck::verify_multilinear(k_log, LOG_PACKING, pin_col, rows, v_a, v_b, v_c, vs)
        .map_err(VerifyError::Lincheck)?;

    let matrix = match rows {
        RowPoint::Multilinear(x_inner) => matrix_claim(x_inner, &lc, lc.matrix_eval),
        RowPoint::Skip { z, rest } => {
            let (rho, claim, value) = verify_product_rounds(LOG_PACKING, lc.matrix_eval, vs)?;
            if claim != lincheck::skip_weight(z, &rho) * value {
                return Err(VerifyError::MatrixSkip);
            }
            let x_inner: Vec<F192> = rho.iter().chain(rest).copied().collect();
            matrix_claim(&x_inner, &lc, value)
        }
    };

    let suffix = suffix_point(&lc.r_cols, x_outer);
    let challenges = ring_switch::sample_map_challenges(vs);
    let target = ring_switch::batched_claim(&lc.slices, &challenges);
    let (point, claim, value) = verify_product_rounds(suffix.len(), target, vs)?;
    if claim != ring_switch::eval_weights(&suffix, &point, &challenges) * value {
        return Err(VerifyError::RingSwitch);
    }

    Ok(Claims {
        witness: Claim { point, value },
        matrix,
    })
}

/// Where the slices live: the column point past the packed bits, then the instance point.
fn suffix_point(r_cols: &[F192], x_outer: &[F192]) -> Vec<F192> {
    r_cols[LOG_PACKING..].iter().chain(x_outer).copied().collect()
}

fn matrix_claim(x_inner: &[F192], lc: &lincheck::MultilinearClaim, value: F192) -> Claim {
    Claim {
        point: x_inner.iter().chain(&lc.r_cols).copied().chain([lc.alpha]).collect(),
        value,
    }
}

/// A commitment that answers one plain multilinear evaluation: WHIR, with `eq(point, .)` as its weight.
///
/// An opening is a proof of its own, its transcript seeded by the claim, so it is checked or aggregated apart from the proof that raised it.
pub mod opening {
    use super::Claim;
    use fiat_shamir::digest_words;
    use fiat_shamir::merkle::Hash;
    use fiat_shamir::transcript::{Proof, ProverState, VerifierState};
    use pcs::whir::{
        INITIAL_FOLDING_FACTOR, LOG_INV_RATE_0, ProverData, commit as whir_commit, config_for_rate,
        recursive_prover_with_basis, recursive_verifier_with_basis_succinct,
    };
    use primitives::field::F64;
    use primitives::hash::hash;
    use primitives::multilinear::{eq_eval, eq_table};

    const LABEL: &[u8] = b"whir-plain-evaluation";

    /// Commit `2^log_n` words.
    pub fn commit(poly: &[F64]) -> (Hash, ProverData) {
        let log_n = poly.len().trailing_zeros() as usize;
        assert_eq!(poly.len(), 1 << log_n);
        let (commitment, data) = whir_commit(poly, log_n, INITIAL_FOLDING_FACTOR, LOG_INV_RATE_0);
        (commitment.root, data)
    }

    /// The seed of an opening's transcript: the claim it proves.
    fn seed(root: &Hash, claim: &Claim) -> [[F64; 4]; 2] {
        let mut bytes = root.to_vec();
        for x in claim.point.iter().chain([&claim.value]) {
            for limb in [x.c0, x.c1, x.c2] {
                bytes.extend_from_slice(&limb.to_le_bytes());
            }
        }
        [digest_words(&hash(LABEL)), digest_words(&hash(&bytes))]
    }

    /// Prove `claim` about the committed `poly`.
    pub fn open(poly: &[F64], root: &Hash, data: &ProverData, claim: &Claim) -> Proof {
        let log_n = claim.point.len();
        let config = config_for_rate(log_n, LOG_INV_RATE_0).expect("WHIR configuration");
        let [iv, statement] = seed(root, claim);
        let mut ps = ProverState::new(iv, statement);
        recursive_prover_with_basis(
            &config,
            log_n,
            poly,
            eq_table(&claim.point),
            claim.value,
            &data.codeword,
            &data.merkle_tree,
            &mut ps,
        );
        ps.into_proof()
    }

    /// Check an opening of `claim` against `root`.
    pub fn verify(root: &Hash, claim: &Claim, proof: &Proof) -> bool {
        let log_n = claim.point.len();
        let Ok(config) = config_for_rate(log_n, LOG_INV_RATE_0) else {
            return false;
        };
        let [iv, statement] = seed(root, claim);
        let mut vs = VerifierState::new(iv, proof, statement);
        recursive_verifier_with_basis_succinct(
            &config,
            log_n,
            1 << INITIAL_FOLDING_FACTOR,
            claim.value,
            root,
            |x| eq_eval(&claim.point, x),
            &mut vs,
        )
        .is_ok()
            && vs.finish().is_ok()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::hash::{
        Compression, K_LOG, USEFUL_BITS, WalkLincheckCircuit, Z_CONST_POS, bilinear_walk,
        generate_witness_with_ab_packed_and_lincheck, pinned_compression,
    };
    use primitives::multilinear::mle_eval;
    use primitives::test_rng::Rng;

    const LABEL: &[u8] = b"standalone-flock-test";

    /// Prove `2^n_log` compressions, flipping witness bit `tamper` first, and return the verifier's verdict.
    fn run(n_log: usize, skip: bool, tamper: Option<usize>) -> (Vec<u64>, usize, Result<Claims, VerifyError>) {
        let mut rng = Rng::new(0x57A2 + n_log as u64);
        let blocks: Vec<Compression> = (0..1 << n_log)
            .map(|_| pinned_compression(std::array::from_fn(|_| rng.next_u32())))
            .collect();
        let (mut z, a, b, mut z_lincheck) = generate_witness_with_ab_packed_and_lincheck(&blocks, n_log);
        if let Some(bit) = tamper {
            z[bit / 64] ^= 1 << (bit % 64);
            let (inner, outer) = (bit % (1 << K_LOG), bit >> K_LOG);
            z_lincheck[(outer / 8) * (1 << K_LOG) + inner] ^= 1 << (outer % 8);
        }
        let witness = Witness {
            z: &z,
            a: &a,
            b: &b,
            z_lincheck: &z_lincheck,
        };
        let mut ps = ProverState::from_label(LABEL);
        let claims = prove(&WalkLincheckCircuit, USEFUL_BITS, n_log, skip, witness, &mut ps);
        let proof = ps.into_proof();
        let mut vs = VerifierState::from_label(LABEL, &proof);
        let verdict = verify(K_LOG, Z_CONST_POS, n_log, skip, &mut vs);
        if tamper.is_none() {
            assert_eq!(verdict.as_ref(), Ok(&claims));
            assert!(vs.finish().is_ok());
        }
        (z, proof.stream.len(), verdict)
    }

    /// Whether both claims hold: of the packed witness, and of the matrices through the circuit walk.
    fn claims_hold(z: &[u64], claims: &Claims) -> bool {
        let packed: Vec<F64> = z.iter().map(|&w| F64(w)).collect();
        let (rows, rest) = claims.matrix.point.split_at(K_LOG);
        let matrix = bilinear_walk(rest[K_LOG], &eq_table(rows), &eq_table(&rest[..K_LOG]));
        mle_eval(&packed, &claims.witness.point) == claims.witness.value && matrix == claims.matrix.value
    }

    #[test]
    fn honest_proof_leaves_true_claims() {
        let n_log = 3;
        let (m, mu) = (K_LOG + n_log, K_LOG + n_log - LOG_PACKING);
        let after_zerocheck = (2 * K_LOG + 64 + 1) + (2 * mu + 1);
        for (skip, zerocheck) in [(false, 2 * m + 2), (true, 64 + 2 * mu + 2 + 2 * LOG_PACKING + 1)] {
            let (z, scalars, verdict) = run(n_log, skip, None);
            assert!(claims_hold(&z, &verdict.unwrap()), "skip={skip}");
            assert_eq!(scalars, zerocheck + after_zerocheck, "skip={skip}");
        }
    }

    /// One flipped witness bit, wherever it sits, is rejected or leaves a false claim.
    #[test]
    fn tampered_witness_is_caught() {
        for skip in [false, true] {
            for bit in [Z_CONST_POS, 5, (3 << K_LOG) + 2000, (7 << K_LOG) + 15_999] {
                let (z, _, verdict) = run(3, skip, Some(bit));
                assert!(
                    !verdict.is_ok_and(|claims| claims_hold(&z, &claims)),
                    "skip={skip} bit {bit}"
                );
            }
        }
    }

    #[test]
    fn opening_roundtrip() {
        let mut rng = Rng::new(0x09E4);
        let log_n = 15;
        let poly: Vec<F64> = (0..1 << log_n).map(|_| F64(rng.next_u64())).collect();
        let (root, data) = opening::commit(&poly);
        let point = rng.ext_vec(log_n);
        let claim = Claim {
            value: mle_eval(&poly, &point),
            point,
        };
        let proof = opening::open(&poly, &root, &data, &claim);
        assert!(opening::verify(&root, &claim, &proof));
        let wrong = Claim {
            value: claim.value + F192::ONE,
            ..claim
        };
        assert!(!opening::verify(&root, &wrong, &proof));
    }
}
