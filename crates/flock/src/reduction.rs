//! The circuit-agnostic half of Flock: zerocheck then lincheck over batches of
//! `2^k_log`-bit blocks, one batch per circuit and every circuit under shared
//! challenges, reducing each circuit's R1CS validity to ONE claim on its packed
//! witness, packaged for ring switching. A circuit supplies only its [`Block`]:
//! the shape, and the walks behind its [`LincheckCircuit`].

use crate::lincheck::{
    self, LincheckCircuit, LincheckClaim, LincheckInput, LincheckStatement, MatrixClaim, MatrixForm, QuirkyPoint,
};
use crate::verifier::FlockError;
use crate::witness::packed_bytes;
use crate::zerocheck::multilinear::PackedWitness;
use crate::zerocheck::{self, K_SKIP, PaddingSpec, ZerocheckClaim, ZerocheckInput};
use fiat_shamir::transcript::{ProverState, VerifierState};
use pcs::pack::{LOG_PACKING, PACKING_WIDTH};
use pcs::stack_open::{RingSwitchClaim, RingSwitchOpen, RingSwitchVerify, RingSwitchVerifyClaim};
use primitives::field::F192;

// A claim's `2^K_SKIP` slices are a ring-switch claim on `q_flock` only if that
// matches the packing width; otherwise `ring_claim` fails at run time.
const _: () = assert!(
    K_SKIP == LOG_PACKING,
    "the univariate skip must match the PCS packing width"
);

/// Minimum `n_blocks_log` needed to prove `n_blocks` instances, subject to the
/// lincheck floor of `n_blocks_log ≥ 3` (`n_outer ≥ 8`).
pub const fn min_n_blocks_log(n_blocks: usize) -> usize {
    assert!(n_blocks >= 1, "n_blocks must be ≥ 1");
    let n = if n_blocks > 8 { n_blocks } else { 8 };
    n.next_power_of_two().trailing_zeros() as usize
}

/// A circuit as the reduction sees it: `2^k_log` witness bits per instance, of
/// which `[useful_bits, 2^k_log)` are zero padding the prover skips.
#[derive(Clone, Copy)]
pub struct Block<'a> {
    pub k_log: usize,
    pub useful_bits: usize,
    pub circuit: &'a dyn LincheckCircuit,
}

/// What the verifier's replay reads of a circuit short of its matrices.
///
/// The matrices are left to the claim the replay returns, so the replay needs no built circuit.
/// Whoever settles that claim against the circuit holds the circuit to this shape.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Shape {
    /// The base-two logarithm of the witness bits per instance.
    pub k_log: usize,
    /// The column of the constant wire, which lincheck pins to one.
    pub const_pin_col: usize,
}

/// The one claim on the committed witness `q_flock` left by the zerocheck +
/// lincheck reduction, for the PCS to discharge: the `2^k_skip` bit-slice
/// values of `z` at `suffix_point`, transmitted and pinned inside the reduction
/// by lincheck's terminal identity (which batches A, B, the constant-wire pin
/// and C), so the PCS only has to bind them to the commitment.
///
/// This is the clean seam between Flock's reduction and the PCS.
///
/// Its elements are values, or whatever a verifier holds them as.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SliceClaim<E = F192> {
    pub suffix_point: Vec<E>,
    pub s_hat_v: Vec<E>,
}

/// Everything [`verify_deferred`] recovers for one circuit: the z-claim for the PCS and the
/// zerocheck / lincheck claims.
#[derive(Clone, Debug)]
pub struct ReductionReplay {
    pub claim: SliceClaim,
    pub zc_claim: ZerocheckClaim,
    pub lc_claim: LincheckClaim,
}

/// One circuit's batch as the prover holds it: the packed `z`, `A·z` and `B·z` of
/// `2^n_blocks_log` instances, and `z` again in the lincheck stripe layout.
#[derive(Clone, Copy)]
pub struct Instance<'a> {
    pub block: Block<'a>,
    pub n_blocks_log: usize,
    pub z: &'a [u64],
    pub a: &'a [u64],
    pub b: &'a [u64],
    pub z_lincheck: &'a [u8],
}

/// What the zerocheck stage hands the lincheck stage: the quirky point each
/// circuit's lincheck runs at. Opaque; the two stages are split only so a caller
/// can time or profile them apart.
#[derive(Clone, Debug)]
pub struct ZerocheckStage {
    x_abs: Vec<QuirkyPoint>,
}

/// The lincheck input point carried over from the zerocheck claim: the
/// univariate-skip coordinate, then the multilinear challenges split at
/// `inner_rest_len` into the inner-rest and outer halves.
fn x_ab_of(zc: &ZerocheckClaim, inner_rest_len: usize) -> QuirkyPoint {
    QuirkyPoint {
        z_skip: zc.z,
        x_inner_rest: zc.mlv_challenges[..inner_rest_len].to_vec(),
        x_outer: zc.mlv_challenges[inner_rest_len..].to_vec(),
    }
}

/// The claim the reduction leaves for the PCS: lincheck's output point, whose
/// 64 slice values are `lc.s_hat_v`. Prover and verifier must derive it
/// identically, so they share this one derivation.
fn reduction_claim(lc: &LincheckClaim, x_outer: &[F192]) -> SliceClaim {
    let mut suffix_point = lc.r_inner_rest.clone();
    suffix_point.extend_from_slice(x_outer);
    SliceClaim {
        suffix_point,
        s_hat_v: lc.s_hat_v.clone(),
    }
}

/// **First stage (prover): the batched zerocheck.** Reduces `a·b ⊕ c = 0` over
/// every circuit's cube to evaluation claims on its `(â, b̂, ĉ)`, all three at one
/// point, the circuits sharing every challenge.
pub fn prove_zerocheck(instances: &[Instance<'_>], ps: &mut ProverState) -> ZerocheckStage {
    let _span = tracing::info_span!("Zerocheck").entered();
    // No bind_statement here: the embedding protocol binds the circuits, the
    // instance counts and the commitment root before any challenge, so the
    // statement is already fully transcript-bound.
    let inputs: Vec<ZerocheckInput<'_>> = instances
        .iter()
        .map(|i| {
            let m = i.block.k_log + i.n_blocks_log;
            // The fused generator packs 64 Boolean coordinates per word.
            let packed_len = 1usize << (m - 6);
            assert_eq!(i.z.len(), packed_len, "wrong packed witness length");
            assert_eq!(i.a.len(), packed_len, "wrong packed A·z length");
            assert_eq!(i.b.len(), packed_len, "wrong packed B·z length");
            ZerocheckInput {
                bits: PackedWitness {
                    a: packed_bytes(i.a),
                    b: packed_bytes(i.b),
                },
                c: packed_bytes(i.z), // C = I, so c == z
                m,
                padding: PaddingSpec {
                    k_log: i.block.k_log,
                    useful_bits_per_block: i.block.useful_bits,
                },
            }
        })
        .collect();
    let claims = zerocheck::prove(&inputs, ps);
    ZerocheckStage {
        x_abs: (instances.iter().zip(&claims))
            .map(|(i, zc)| x_ab_of(zc, i.block.k_log - K_SKIP))
            .collect(),
    }
}

/// **Second stage (prover): the batched lincheck.** Reduces every circuit's
/// `(â, b̂, ĉ)` claims to the `2^k_skip` bit slices of its `z` at one point, against
/// its per-block matrices, under one sumcheck.
pub fn prove_lincheck(instances: &[Instance<'_>], stage: ZerocheckStage, ps: &mut ProverState) -> Vec<SliceClaim> {
    let _span = tracing::info_span!("Lincheck").entered();
    let ZerocheckStage { x_abs } = stage;
    let inputs: Vec<LincheckInput<'_>> = (instances.iter().zip(&x_abs))
        .map(|(i, x_ab)| {
            let m = i.block.k_log + i.n_blocks_log;
            assert_eq!(i.z_lincheck.len(), (1usize << m) / 8, "wrong lincheck stripe length");
            LincheckInput {
                z_packed: i.z_lincheck,
                m,
                k_log: i.block.k_log,
                k_skip: K_SKIP,
                useful_bits: i.block.useful_bits,
                circuit: i.block.circuit,
                x_ab,
            }
        })
        .collect();
    let claims = lincheck::prove(&inputs, ps);
    (claims.iter().zip(&x_abs))
        .map(|(lc, x_ab)| reduction_claim(lc, &x_ab.x_outer))
        .collect()
}

/// The batched zerocheck then lincheck, leaving one claim on each circuit's committed witness.
pub fn prove(instances: &[Instance<'_>], ps: &mut ProverState) -> Vec<SliceClaim> {
    let stage = prove_zerocheck(instances, ps);
    prove_lincheck(instances, stage, ps)
}

impl Block<'_> {
    /// What the verifier's replay reads of the circuit short of its matrices.
    pub fn shape(&self) -> Shape {
        Shape {
            k_log: self.k_log,
            const_pin_col: self.circuit.const_pin_col(),
        }
    }
}

impl Shape {
    /// Whether a matrix form has the lengths a replay of a circuit of this shape gives.
    pub const fn fits(&self, form: &MatrixForm) -> bool {
        let rest = self.k_log - K_SKIP;
        form.s_hat_v.len() == 1 << K_SKIP && form.x_inner_rest.len() == rest && form.r_inner_rest.len() == rest
    }
}

/// **Verifier.** Replay the batched zerocheck and lincheck over circuits of
/// `2^n_blocks_log` instances each straight off the shared transcript stream,
/// recovering one evaluation claim on each circuit's committed witness, which
/// the PCS then discharges, and each circuit's claim on its matrices.
///
/// It reads only the circuits' shapes: their matrices' forms are left as claims
/// for the built circuits to settle.
///
/// # Errors
///
/// Returns the first stage that refuses the proof.
pub fn verify_deferred(
    circuits: &[(Shape, usize)],
    vs: &mut VerifierState<'_>,
) -> Result<Vec<(ReductionReplay, MatrixClaim)>, FlockError> {
    let log_ns: Vec<usize> = circuits.iter().map(|(shape, n)| shape.k_log + n).collect();
    let zc_claims = zerocheck::verify(&log_ns, vs).map_err(FlockError::Zerocheck)?;

    let x_abs: Vec<QuirkyPoint> = (circuits.iter().zip(&zc_claims))
        .map(|((shape, _), zc)| x_ab_of(zc, shape.k_log - K_SKIP))
        .collect();
    let statements: Vec<LincheckStatement<'_>> = (circuits.iter().zip(&log_ns).zip(&zc_claims).zip(&x_abs))
        .map(|((((shape, _), &m), zc), x_ab)| LincheckStatement {
            m,
            k_log: shape.k_log,
            k_skip: K_SKIP,
            const_pin_col: shape.const_pin_col,
            x_ab,
            v_a: zc.a_eval,
            v_b: zc.b_eval,
            v_c: zc.c_eval,
        })
        .collect();
    let lc_claims = lincheck::verify_deferred(&statements, vs).map_err(FlockError::Lincheck)?;

    Ok((zc_claims.into_iter().zip(lc_claims).zip(&x_abs))
        .map(|((zc_claim, (lc_claim, matrices)), x_ab)| {
            let replay = ReductionReplay {
                claim: reduction_claim(&lc_claim, &x_ab.x_outer),
                zc_claim,
                lc_claim,
            };
            (replay, matrices)
        })
        .collect())
}

/// [`verify_deferred`], each circuit's matrix claim settled against the circuit.
///
/// # Errors
///
/// Returns the first stage that refuses the proof.
pub fn verify(circuits: &[(Block<'_>, usize)], vs: &mut VerifierState<'_>) -> Result<Vec<ReductionReplay>, FlockError> {
    let shapes: Vec<(Shape, usize)> = circuits.iter().map(|(block, n)| (block.shape(), *n)).collect();
    let replays = verify_deferred(&shapes, vs)?;
    (replays.into_iter().zip(circuits))
        .map(|((replay, matrices), (block, _))| {
            matrices.check(block.circuit).map_err(FlockError::Lincheck)?;
            Ok(replay)
        })
        .collect()
}

/// One reduction claim as a tower [`RingSwitchClaim`]: the `2^k_skip` slices and
/// the suffix point they live at, which is the WHOLE multilinear tail of the
/// quirky point (`q_flock` has `2^qflock_vars` words, and the packing prefix is
/// exactly the skipped coordinates, so nothing is split off into it).
fn ring_claim(claim: &SliceClaim, qflock_vars: usize) -> RingSwitchClaim {
    assert_eq!(
        claim.suffix_point.len(),
        qflock_vars,
        "ring-switch suffix must span the q_flock cube"
    );
    assert_eq!(claim.s_hat_v.len(), PACKING_WIDTH);
    RingSwitchClaim {
        suffix_point: claim.suffix_point.clone(),
        s_hat_v: Some(claim.s_hat_v.clone()),
    }
}

/// Package the prover's reduction claim as a [`RingSwitchOpen`], so the PCS
/// discharges flock's validity in the same opening as the embedder's own point
/// claims. `q_flock` is the `2^qflock_vars`-word slice of the committed stack at
/// `offset`.
pub fn ring_switch_open(qflock_vars: usize, offset: usize, reduced: &SliceClaim) -> RingSwitchOpen {
    RingSwitchOpen {
        offset,
        qflock_vars,
        claims: vec![ring_claim(reduced, qflock_vars)],
    }
}

/// Verifier counterpart of [`ring_switch_open`]: package the recovered claim as
/// a [`RingSwitchVerify`], the same statement data. The transmitted opening
/// travels separately.
pub fn ring_switch_verify<E>(qflock_vars: usize, offset: usize, claim: &SliceClaim<E>) -> RingSwitchVerify<'_, E> {
    assert_eq!(
        claim.suffix_point.len(),
        qflock_vars,
        "ring-switch suffix must span the q_flock cube"
    );
    RingSwitchVerify {
        offset,
        qflock_vars,
        claims: vec![RingSwitchVerifyClaim {
            suffix_point: &claim.suffix_point,
            s_hat_v: claim.s_hat_v.as_slice().try_into().expect("ring-switch has 64 slices"),
        }],
    }
}
