//! The circuit-agnostic half of Flock: zerocheck then lincheck over a batch of
//! `2^k_log`-bit blocks, reducing R1CS validity to ONE claim on the packed
//! witness, packaged for ring switching. A circuit supplies only its [`Block`]:
//! the shape, and the walks behind its [`LincheckCircuit`].

use crate::lincheck::{self, LincheckCircuit, LincheckClaim, QuirkyPoint};
use crate::verifier::VerifyError;
use crate::witness::packed_bytes;
use crate::zerocheck::{self, K_SKIP, PaddingSpec, ZerocheckClaim};
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
pub fn min_n_blocks_log(n_blocks: usize) -> usize {
    assert!(n_blocks >= 1, "n_blocks must be ≥ 1");
    n_blocks.max(8).next_power_of_two().trailing_zeros() as usize
}

/// A circuit as the reduction sees it: `2^k_log` witness bits per instance, of
/// which `[useful_bits, 2^k_log)` are zero padding the prover skips.
#[derive(Clone, Copy)]
pub struct Block<'a> {
    pub k_log: usize,
    pub useful_bits: usize,
    pub circuit: &'a dyn LincheckCircuit,
}

/// The one claim on the committed witness `q_flock` left by the zerocheck +
/// lincheck reduction, for the PCS to discharge: the `2^k_skip` bit-slice
/// values of `z` at `suffix_point`, transmitted and pinned inside the reduction
/// by lincheck's terminal identity (which batches A, B, the constant-wire pin
/// and C), so the PCS only has to bind them to the commitment.
///
/// This is the clean seam between Flock's reduction and the PCS.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SliceClaim {
    pub suffix_point: Vec<F192>,
    pub s_hat_v: Vec<F192>,
}

/// Everything [`Block::verify`] recovers: the z-claim for the PCS and the
/// zerocheck / lincheck claims.
#[derive(Clone, Debug)]
pub struct ReductionReplay {
    pub claim: SliceClaim,
    pub zc_claim: ZerocheckClaim,
    pub lc_claim: LincheckClaim,
}

/// What the zerocheck stage hands the lincheck stage: the quirky point lincheck
/// runs at. Opaque; the two stages are split only so a caller can time or
/// profile them apart.
#[derive(Clone, Debug)]
pub struct ZerocheckStage {
    x_ab: QuirkyPoint,
}

/// One `FLOCK_PROVE_TRACE` line. `label` carries its own colon so the stages
/// line up.
pub(crate) fn trace_stage(label: &str, t: std::time::Instant) {
    if std::env::var_os("FLOCK_PROVE_TRACE").is_some() {
        eprintln!("[flock prove] {label:<11}{:8.2} ms", t.elapsed().as_secs_f64() * 1e3);
    }
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

impl Block<'_> {
    /// **First stage (prover): the zerocheck.** Reduces `a·b ⊕ c = 0` over the
    /// cube of `2^n_blocks_log` blocks to evaluation claims on `(â, b̂, ĉ)`, all
    /// three at one point.
    pub fn prove_zerocheck(
        &self,
        n_blocks_log: usize,
        z_packed: &[u64],
        a_packed_words: &[u64],
        b_packed_words: &[u64],
        ps: &mut ProverState,
    ) -> ZerocheckStage {
        let t_zerocheck = std::time::Instant::now();
        let m = self.k_log + n_blocks_log;

        // The fused generator packs 64 Boolean coordinates per word.
        let packed_len = 1usize << (m - 6);
        assert_eq!(z_packed.len(), packed_len, "wrong packed witness length");
        assert_eq!(a_packed_words.len(), packed_len, "wrong packed A·z length");
        assert_eq!(b_packed_words.len(), packed_len, "wrong packed B·z length");

        // No bind_statement here: the embedding protocol binds the circuit, the
        // instance count and the commitment root before any challenge, so the
        // statement is already fully transcript-bound.

        let padding = PaddingSpec {
            k_log: self.k_log,
            useful_bits_per_block: self.useful_bits,
        };
        let zc_claim = zerocheck::prove_packed_padded(
            packed_bytes(a_packed_words),
            packed_bytes(b_packed_words),
            packed_bytes(z_packed), // C = I, so c == z
            m,
            &padding,
            ps,
        );

        let x_ab = x_ab_of(&zc_claim, self.k_log - K_SKIP);
        trace_stage("zerocheck:", t_zerocheck);
        ZerocheckStage { x_ab }
    }

    /// **Second stage (prover): the lincheck.** Reduces the zerocheck's
    /// `(â, b̂, ĉ)` claims to the `2^k_skip` bit slices of `z` at one point,
    /// against the per-block matrices.
    pub fn prove_lincheck(
        &self,
        n_blocks_log: usize,
        stage: ZerocheckStage,
        z_packed_lincheck: &[u8],
        ps: &mut ProverState,
    ) -> SliceClaim {
        let t_lincheck = std::time::Instant::now();
        let m = self.k_log + n_blocks_log;
        assert_eq!(
            z_packed_lincheck.len(),
            (1usize << m) / 8,
            "wrong lincheck stripe length"
        );

        let ZerocheckStage { x_ab } = stage;
        let lc_claim = lincheck::prove_padded_capture_s_hat_v(
            z_packed_lincheck,
            m,
            self.k_log,
            K_SKIP,
            self.useful_bits,
            self.circuit,
            &x_ab,
            ps,
        );

        let claim = reduction_claim(&lc_claim, &x_ab.x_outer);
        trace_stage("lincheck:", t_lincheck);
        claim
    }

    /// **Verifier.** Replay the zerocheck and lincheck straight off the shared
    /// transcript stream, recovering the one evaluation claim on the committed
    /// witness `q_flock`. The PCS then discharges the returned claim.
    pub fn verify(&self, n_blocks_log: usize, vs: &mut VerifierState<'_>) -> Result<ReductionReplay, VerifyError> {
        let m = self.k_log + n_blocks_log;
        let zc_claim = zerocheck::verify(m, vs).map_err(VerifyError::Zerocheck)?;

        let x_ab = x_ab_of(&zc_claim, self.k_log - K_SKIP);
        let lc_claim = lincheck::verify(
            m,
            self.k_log,
            K_SKIP,
            self.circuit,
            &x_ab,
            zc_claim.a_eval,
            zc_claim.b_eval,
            zc_claim.c_eval,
            vs,
        )
        .map_err(VerifyError::Lincheck)?;

        let claim = reduction_claim(&lc_claim, &x_ab.x_outer);
        Ok(ReductionReplay {
            claim,
            zc_claim,
            lc_claim,
        })
    }
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
pub fn ring_switch_verify(qflock_vars: usize, offset: usize, claim: &SliceClaim) -> RingSwitchVerify<'_> {
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
