//! Flock's reduction (`flock::reduction::Shape::verify_deferred`) as a circuit: the zerocheck, then the
//! lincheck up to the circuit's matrices, whose bilinear form is left as a [`MatrixClaim`].
//!
//! Neither stage checks anything on its own: the zerocheck is a reduction, and lincheck's terminal identity
//! is the matrix claim's value. Every soundness check of the native replay is therefore in the claims this
//! returns, and the rows here are the transcript and the arithmetic that derives them.

use super::math::{poly_eval, times_one_plus};
use super::{MatrixClaim, SliceClaim};
use crate::rec::circuit::{Builder, Ew};
use crate::rec::transcript::Transcript;
use ::flock::reduction::Shape;
use ::flock::zerocheck::univariate_skip_optimized::{medium_challenges, small_challenges};
use ::flock::zerocheck::{K_SKIP, MIN_LOG_N};
use primitives::field::{F192, PHI_8_TABLE_192 as PHI_8_TABLE};
use primitives::multilinear::window_denominator;

/// The skip domain's size, and the round-1 message's.
const ELL: usize = 1 << K_SKIP;

/// `flock::zerocheck::ZerocheckClaim`, and the skip domain's differences at `z`, which lincheck's `C` term
/// reuses.
struct ZerocheckClaim {
    z: Ew,
    mlv_challenges: Vec<Ew>,
    a_eval: Ew,
    b_eval: Ew,
    c_eval: Ew,
    skip: Differences,
}

/// `p + nodes[k]` for an aligned window of the φ₈ table, and their prefix products
/// `prefix[i - 1] = ∏_{k<i} (p + nodes[k])` for `i` in `1..nodes.len()`.
struct Differences {
    diffs: Vec<Ew>,
    prefix: Vec<Ew>,
}

impl Differences {
    fn new(b: &mut Builder, p: Ew, nodes: &[F192]) -> Self {
        // φ₈ lands in `K`, so a node is an `E` constant with zero high limbs; the zero node costs no row.
        let diffs: Vec<Ew> = nodes
            .iter()
            .map(|&node| if node.is_zero() { p } else { b.add_const(p, node) })
            .collect();
        let mut prefix = Vec::with_capacity(nodes.len() - 1);
        prefix.push(diffs[0]);
        for i in 1..nodes.len() - 1 {
            let next = b.mul(prefix[i - 1], diffs[i]);
            prefix.push(next);
        }
        Self { diffs, prefix }
    }

    /// `∏_k (p + nodes[k])`: the window's vanishing polynomial at `p`.
    fn vanishing(&self, b: &mut Builder) -> Ew {
        let last = self.diffs.len() - 1;
        b.mul(self.prefix[last - 1], self.diffs[last])
    }

    /// `Σ_i values[i] · ∏_{k≠i} (p + nodes[k])`, the barycentric sum short of the window's denominator
    /// (`primitives::multilinear::barycentric_sum` at scale one), by Horner over the nodes: two rows a node.
    fn lagrange_sum(&self, b: &mut Builder, values: &[Ew]) -> Ew {
        assert_eq!(values.len(), self.diffs.len());
        let mut sum = values[0];
        for ((&value, &prefix), &diff) in values[1..].iter().zip(&self.prefix).zip(&self.diffs[1..]) {
            let term = b.mul(value, prefix);
            sum = b.mul_add(sum, diff, term);
        }
        sum
    }
}

/// `Σ_i L_i(z)·values[i]`, `L_i` the skip domain's Lagrange weights (`skip_lagrange_weights(K_SKIP, z)`).
pub(crate) fn skip_weighted_sum(b: &mut Builder, z: Ew, values: &[Ew]) -> Ew {
    let skip = Differences::new(b, z, &PHI_8_TABLE[..ELL]);
    let sum = skip.lagrange_sum(b, values);
    b.mul_const(sum, window_denominator(ELL))
}

/// `flock::zerocheck::verify` over `{0,1}^m`.
fn verify_zerocheck(b: &mut Builder, t: &mut Transcript, m: usize) -> ZerocheckClaim {
    assert!(m >= MIN_LOG_N, "log_n {m} is below the zerocheck's floor {MIN_LOG_N}");
    let n_mlv = m - K_SKIP;

    // The equality tail: the fixed inner coordinates, then the sampled outer ones (`equality_tail`).
    let outer = t.sample_vec(b, m - MIN_LOG_N);
    let r_rest: Vec<Ew> = small_challenges()
        .into_iter()
        .chain(medium_challenges())
        .map(|c| b.e_const(c))
        .chain(outer)
        .collect();
    debug_assert_eq!(r_rest.len(), n_mlv);

    let round1 = t.next_scalars(b, ELL);
    let z = t.sample(b);

    // `interpolate_at_z_combined`: the round-1 message on Λ, zero on S, at `z`; the weight of every node of
    // Λ carries the vanishing polynomial of S and the denominator of the window `S ∪ Λ`.
    let (s_nodes, lambda_nodes) = PHI_8_TABLE[..2 * ELL].split_at(ELL);
    let skip = Differences::new(b, z, s_nodes);
    let vanishing_on_s = skip.vanishing(b);
    let lambda = Differences::new(b, z, lambda_nodes);
    let sum = lambda.lagrange_sum(b, &round1);
    let sum = b.mul(sum, vanishing_on_s);
    let mut c_running = b.mul_const(sum, window_denominator(2 * ELL));

    let mut mlv_challenges = Vec::with_capacity(n_mlv);
    for &r_eq in &r_rest {
        let g = t.next_round_poly(b, 3, c_running, Some(r_eq));
        let chi = t.sample(b);
        mlv_challenges.push(chi);
        c_running = poly_eval(b, &g, chi);
    }

    let a_eval = t.next_scalar(b);
    let b_eval = t.next_scalar(b);
    let c_eval = b.mul_add(a_eval, b_eval, c_running);
    ZerocheckClaim {
        z,
        mlv_challenges,
        a_eval,
        b_eval,
        c_eval,
        skip,
    }
}

/// `flock::lincheck::verify_deferred` at the zerocheck's point, `k_skip = K_SKIP`.
fn verify_lincheck(
    b: &mut Builder,
    t: &mut Transcript,
    k_log: usize,
    const_pin_col: usize,
    zc: &ZerocheckClaim,
) -> MatrixClaim {
    assert!(K_SKIP <= k_log, "k_skip {K_SKIP} exceeds k_log {k_log}");
    assert!(const_pin_col < 1 << k_log, "the constant wire is outside the block");
    let inner_rest_len = k_log - K_SKIP;
    let x_inner_rest = &zc.mlv_challenges[..inner_rest_len];

    // 1. α, and the target the α-batched claims and the constant-wire pin (β = α³) set.
    let alpha = t.sample(b);
    let alpha_sq = b.square(alpha);
    let beta = b.mul(alpha_sq, alpha);
    let target = b.mul_add(alpha, zc.b_eval, zc.a_eval);
    let target = b.mul_add(alpha_sq, zc.c_eval, target);
    let mut running = b.add(target, beta);

    // 2. The product sumcheck.
    let mut r_rounds = Vec::with_capacity(inner_rest_len);
    for _ in 0..inner_rest_len {
        let q = t.next_round_poly(b, 3, running, None);
        let r = t.sample(b);
        running = poly_eval(b, &q, r);
        r_rounds.push(r);
    }

    // 3. The slices.
    let z_partial = t.next_scalars(b, ELL);
    let r_inner_rest: Vec<Ew> = r_rounds.into_iter().rev().collect();

    // 4. The terminal identity short of the bilinear form: the pin's `β·w_col[pin]`, then the `C` term
    //    `α²·eq(x_inner_rest, r_inner_rest)·⟨λ(z_skip), z_partial⟩`.
    //    Each eq factor `v·(1 + r)` is one row.
    let pin_rest = const_pin_col >> K_SKIP;
    let mut pin_term = z_partial[const_pin_col & (ELL - 1)];
    for (j, &r) in r_inner_rest.iter().enumerate() {
        pin_term = if (pin_rest >> j) & 1 == 1 {
            b.mul(pin_term, r)
        } else {
            times_one_plus(b, pin_term, r)
        };
    }
    let value = b.mul_add(beta, pin_term, running);

    // `skip_lagrange_weights(K_SKIP, z_skip)` against the slices, as one barycentric sum over S.
    let c_slices = zc.skip.lagrange_sum(b, &z_partial);
    let mut c_term = b.mul_const(c_slices, window_denominator(ELL));
    for (&x, &r) in x_inner_rest.iter().zip(&r_inner_rest) {
        let s = b.add(x, r);
        c_term = times_one_plus(b, c_term, s);
    }
    let value = b.mul_add(alpha_sq, c_term, value);

    MatrixClaim {
        alpha,
        z_skip: zc.z,
        x_inner_rest: x_inner_rest.to_vec(),
        r_inner_rest,
        s_hat_v: z_partial,
        value,
    }
}

/// `Shape::verify_deferred`: the reduction's claim on the packed witness (`ReductionReplay::claim`) and the
/// matrix claim lincheck's terminal identity leaves, which the native `MatrixClaim::check` settles against
/// the circuit.
pub fn verify_reduction(
    b: &mut Builder,
    t: &mut Transcript,
    shape: Shape,
    n_blocks_log: usize,
) -> (SliceClaim, MatrixClaim) {
    let m = shape.k_log + n_blocks_log;
    let zc = b.scope("zerocheck", |b| verify_zerocheck(b, t, m));
    let matrices = b.scope("lincheck", |b| {
        verify_lincheck(b, t, shape.k_log, shape.const_pin_col, &zc)
    });
    let x_outer = &zc.mlv_challenges[shape.k_log - K_SKIP..];
    let mut suffix_point = matrices.r_inner_rest.clone();
    suffix_point.extend_from_slice(x_outer);
    let claim = SliceClaim {
        suffix_point,
        s_hat_v: matrices.s_hat_v.clone(),
    };
    (claim, matrices)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::class_flock;
    use crate::rec::circuit::{Circuit, Limbs};
    use crate::rec::transcript::Source;
    use crate::tables::{CLASSES, Part};
    use ::flock::lincheck::{MatrixClaim as NativeMatrixClaim, MatrixForm};
    use ::flock::reduction::ReductionReplay;
    use fiat_shamir::transcript::{Proof, ProverState, RawProof, VerifierState};

    const LABEL: &[u8] = b"rec-inner-flock-test";

    fn class(name: &str) -> usize {
        let t = CLASSES.iter().position(|c| c.name == name).expect("a table");
        class_flock::flock_index(t, Part::Class)
    }

    fn xorshift(seed: u64) -> impl FnMut() -> u64 {
        let mut state = seed;
        move || {
            state ^= state << 13;
            state ^= state >> 7;
            state ^= state << 17;
            state
        }
    }

    /// The reduction of packed witness `f` over `rows`, proven natively.
    fn prove<const N: usize>(f: usize, rows: &[[u64; N]], n_blocks_log: usize) -> Proof {
        let circuit = class_flock::circuit(f);
        let (t, _) = class_flock::flock(f);
        let (z, a, bz, zl) = CLASSES[t].witness.map_or_else(
            || circuit.generate_witness(rows, n_blocks_log),
            |witness| {
                circuit.generate_witness_with(rows, &[0; N], n_blocks_log, |row, z, az, bz| witness(row, z, az, bz))
            },
        );
        let block = circuit.block();
        let mut ps = ProverState::from_label(LABEL);
        let stage = block.prove_zerocheck(n_blocks_log, &z, &a, &bz, &mut ps);
        block.prove_lincheck(n_blocks_log, stage, &zl, &mut ps);
        ps.into_proof()
    }

    fn native(f: usize, n_blocks_log: usize, proof: &Proof) -> (ReductionReplay, NativeMatrixClaim, usize) {
        let mut vs = VerifierState::from_label(LABEL, proof);
        let (replay, matrices) = class_flock::verify_reduction(f, n_blocks_log, &mut vs).expect("the replay runs");
        let read = vs.into_raw_proof().stream.len();
        (replay, matrices, read)
    }

    fn label_cv() -> Limbs {
        let d = primitives::hash::hash(LABEL);
        std::array::from_fn(|i| u64::from_le_bytes(d[8 * i..8 * i + 8].try_into().expect("eight bytes")))
    }

    /// The circuit's replay: its builder, whether the stream was read to the end, and its claims.
    fn replay(f: usize, n_blocks_log: usize, source: Source) -> (Builder, bool, SliceClaim, MatrixClaim) {
        let mut b = Builder::new();
        let cv = b.d_const(label_cv());
        let mut t = Transcript::from_state(cv, source);
        let (claim, matrices) = verify_reduction(&mut b, &mut t, class_flock::shape(f), n_blocks_log);
        let finished = t.finished();
        (b, finished, claim, matrices)
    }

    fn values(b: &Builder, ws: &[Ew]) -> Vec<F192> {
        ws.iter().map(|&w| b.e(w)).collect()
    }

    /// The circuit's matrix claim with its wires' values.
    fn native_claim(b: &Builder, mc: &MatrixClaim) -> NativeMatrixClaim {
        NativeMatrixClaim {
            form: MatrixForm {
                alpha: b.e(mc.alpha),
                z_skip: b.e(mc.z_skip),
                x_inner_rest: values(b, &mc.x_inner_rest),
                r_inner_rest: values(b, &mc.r_inner_rest),
                s_hat_v: values(b, &mc.s_hat_v),
            },
            value: b.e(mc.value),
        }
    }

    fn shape_circuit(f: usize, n_blocks_log: usize) -> Circuit {
        let (b, _, _, _) = replay(f, n_blocks_log, Source::Shape);
        b.finish().0
    }

    /// The honest replay agrees with the native one, and its matrix claim settles against the circuit.
    fn honest(f: usize, n_blocks_log: usize, proof: &Proof) {
        let (replay_native, matrices, read) = native(f, n_blocks_log, proof);
        assert_eq!(read, proof.stream.len(), "the native replay reads the whole stream");
        matrices
            .check(class_flock::circuit(f))
            .expect("the native verifier accepts");

        let raw = RawProof {
            stream: proof.stream.clone(),
            merkle: Vec::new(),
        };
        let (b, finished, claim, mc) = replay(f, n_blocks_log, Source::Proof(&raw));
        assert!(b.failures().is_empty(), "{:?}", b.failures());
        assert!(finished, "the circuit reads the whole stream");
        assert_eq!(values(&b, &claim.suffix_point), replay_native.claim.suffix_point);
        assert_eq!(values(&b, &claim.s_hat_v), replay_native.claim.s_hat_v);
        let got = native_claim(&b, &mc);
        assert_eq!(got, matrices);
        got.check(class_flock::circuit(f)).expect("the circuit's claim settles");

        let (circuit, _, failures) = b.finish();
        assert!(failures.is_empty());
        assert!(circuit == shape_circuit(f, n_blocks_log), "the circuit is the shape's");
    }

    /// A tampered stream scalar: the native verifier rejects, the circuit's matrix claim fails to settle,
    /// and settling it in the circuit is a failure.
    fn tampered(f: usize, n_blocks_log: usize, proof: &Proof, index: usize) {
        let mut proof = proof.clone();
        proof.stream[index] += F192::ONE;
        let (_, matrices, _) = native(f, n_blocks_log, &proof);
        assert!(
            matrices.check(class_flock::circuit(f)).is_err(),
            "the native verifier rejects"
        );

        let raw = RawProof {
            stream: proof.stream.clone(),
            merkle: Vec::new(),
        };
        let (mut b, finished, _, mc) = replay(f, n_blocks_log, Source::Proof(&raw));
        assert!(finished);
        let got = native_claim(&b, &mc);
        assert_eq!(
            got, matrices,
            "the circuit replays the tampered stream as the native verifier does"
        );
        let form = got.form.evaluate(class_flock::circuit(f));
        b.eq_e_const(mc.value, form);
        assert!(!b.failures().is_empty(), "the tampered proof does not settle");
    }

    /// The tampered scalars: the first of the zerocheck's round-1 message, and the last lincheck round's
    /// quadratic coefficient (the slices are the stream's last `ELL` scalars).
    fn tamper_both(f: usize, n_blocks_log: usize, proof: &Proof) {
        tampered(f, n_blocks_log, proof, 0);
        tampered(f, n_blocks_log, proof, proof.stream.len() - ELL - 1);
    }

    #[test]
    fn hash_reduction() {
        let f = class("HASH");
        let n_blocks_log = class_flock::n_blocks_log(CLASSES[class_flock::flock(f).0], 5);
        let mut next = xorshift(0xA7);
        let rows: Vec<[u64; 14]> = (0..5).map(|_| std::array::from_fn(|_| next())).collect();
        let proof = prove(f, &rows, n_blocks_log);
        honest(f, n_blocks_log, &proof);
        tamper_both(f, n_blocks_log, &proof);
    }

    #[test]
    fn small_class_reduction() {
        let f = class("LD");
        let n_blocks_log = class_flock::n_blocks_log(CLASSES[class_flock::flock(f).0], 20);
        let mut next = xorshift(0x5EED);
        let rows: Vec<[u64; 2]> = (0..20).map(|_| [next(), next()]).collect();
        let proof = prove(f, &rows, n_blocks_log);
        honest(f, n_blocks_log, &proof);
        tamper_both(f, n_blocks_log, &proof);
    }
}
