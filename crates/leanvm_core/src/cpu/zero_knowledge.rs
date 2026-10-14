//! Zero-knowledge proofs of a run: the plain proof under one-time pads, on a hiding commitment, and an outer proof.
//!
//! The transcript, after a session of its own:
//!
//! ```text
//!     clear    each table's height and the rate: the run's public shape
//!     clear    the stack's root (hiding), then the key commitment's root
//!     hidden   the final clock's free bits, the bus, the tables, flock's reductions, the opening's lane rounds
//!     clear    the rest of the opening, from its revealed claim on
//!     clear    the public evaluations the deferred claims need
//!     hidden   the outer proof's auxiliary values
//!     clear    the outer proof and the key commitment's opening
//! ```
//!
//! The verifier runs its own code over the padded transcript through a recorder.
//!
//! The outer proof shows the keys satisfy what it recorded.
//!
//! # The deferred claims
//!
//! The core leaves claims on the program's polynomials and on each circuit's matrices, as a plain proof's does.
//!
//! Their points are challenges, but some of their weights and values are hidden.
//!
//! - The prover sends what the claims need of the public polynomials: each bytecode term, the image's value, each circuit's slice weights.
//! - The verifier records each hidden claim as a linear constraint on those public values.
//! - One challenge `rho` then batches the public values into claims of the plain claims' shape, which are settled as a plain proof's.
//!
//! So the core of either kind of proof leaves the same claims, and recursion carries them out alike.

use super::deferred::{Claim, DeferredClaims, MalformedClaim, ProgramPoint};
use super::layout::{Announcement, Layout, Lookup};
use super::proof::ProofKind;
use super::witness::Witness;
use super::{CpuError, Output, Program, Proof};
use crate::bus::{self, N_TUPLE_BITS, PublicColumns, SparseColumn};
use crate::commitment::{Commitment, Committed, Rate};
use crate::constraints::ConstraintError;
use crate::tables::{CircuitId, Clock, N_CIRCUITS};
use fiat_shamir::arith::{Arith, Native, Verifier};
use fiat_shamir::{ProofTranscript, ProverState, VerifierState};
use flock::FlockError;
use flock::lincheck::{LincheckError, MatrixForm};
use pcs::merkle::Hash;
use pcs::verifier::OpeningVerifier;
use primitives::field::{F64, F192};
use std::ops::Range;
use tracing::info_span;
use zk::{KeyCommitment, Keys, OuterError, Purpose, Recorder, Seed, Value};

/// The final clock's bits a run may set: past its slot's bits and below its live bit, which is set (§sec:state).
const FREE_CLOCK_BITS: Range<usize> = Clock::SLOT_BITS as usize..Clock::LIVE_BIT as usize;

/// Prove a built witness in zero knowledge, at `rate`, every random draw from `seed`.
///
/// # Panics
///
/// Panics if the witness's bus does not balance, or if the outer proof outgrows the key commitment.
pub(super) fn prove(program: &Program, mut w: Witness, output: Output, rate: Rate, seed: &Seed) -> Proof {
    let mut ps = ProverState::new(&program.zk_session(), output.words());
    Announcement::write_shape(&w.layout.taus, rate, &mut ps);

    // The hiding stack, then the keys, both before any challenge.
    let committed = info_span!("Commit").in_scope(|| {
        Committed::new_hiding(
            &mut ps,
            &mut w.q,
            w.layout.shape,
            rate,
            &mut seed.stream(Purpose::Commitment),
        )
        .expect("the witness matches its layout")
    });
    let keys = info_span!("Commit keys").in_scope(|| Keys::commit(&mut ps, rate.log_inv_rate().into(), seed));

    // The plain proof, every scalar padded until the opening reveals its claim after its lane fold.
    ps.set_keys(keys.keys().to_vec());
    ps.set_hidden(true);
    for bit in FREE_CLOCK_BITS {
        ps.prover_message(&F192::from(F64(w.ts_final >> bit & 1)));
    }
    let (slots, rings) = program.prove_reductions(&mut ps, &mut w, output);
    info_span!("PCS open").in_scope(|| {
        committed
            .open(&mut ps, &w.q, &slots, &rings)
            .expect("opening uses the committed witness");
    });
    drop((committed, w, slots, rings));

    // The public evaluations the claims of the prover's own core need, then the challenge that batches them.
    let evaluations = info_span!("Public evaluations").in_scope(|| {
        let (_, core) = replay(program, output, ps.proof());
        PublicEvaluations::of(program, &core.claims)
    });
    evaluations.send(&mut ps);
    let _rho: F192 = ps.verifier_message();

    // The record of the whole padded transcript, then the outer proof.
    let record = info_span!("Record").in_scope(|| {
        let (mut rec, core) = replay(program, output, ps.proof());
        core.claims
            .into_plain(&mut rec)
            .expect("the prover's own claims are well formed");
        rec.finish().1
    });
    info_span!("Outer proof").in_scope(|| keys.prove_outer(&mut ps, &record));
    Proof(ps.into_proof(), ProofKind::ZeroKnowledge)
}

/// The prover's replay of its own proof so far, through the verifier's recorder: the recorder, and the core it recorded.
///
/// It feeds the prover's own proof and nobody's trust, so it runs on the prover's kernels.
///
/// # Panics
///
/// Panics if the prover's own proof is refused.
fn replay<'p>(
    program: &Program,
    output: Output,
    proof: &'p ProofTranscript,
) -> (Recorder<VerifierState<'p, Native>>, RecordedCore<Hash, F192>) {
    let mut rec = Recorder::new(VerifierState::native(&program.zk_session(), output.words(), proof));
    let core = record_proof(program, &mut rec, output).expect("the prover's own proof verifies");
    (rec, core)
}

/// Verify a zero-knowledge proof's core over a verifier reading it, returning the claims it leaves.
///
/// They have the plain claims' shape, and are settled as a plain proof's.
///
/// # Errors
///
/// Returns the first stage that refuses the proof.
pub(super) fn verify_core<V>(program: &Program, output: Output, inner: V) -> Result<(V, DeferredClaims), CpuError>
where
    V: OpeningVerifier<E = F192> + PublicColumns,
{
    let mut rec = Recorder::new(inner);
    let core = record_proof(program, &mut rec, output)?;
    let claims = core.claims.into_plain(&mut rec)?;
    let mut inner = core.keys.verify_outer(rec).map_err(CpuError::Outer)?;
    inner.check_eof()?;
    Ok((inner, claims))
}

/// The recorded core of a proof read natively: its announced shape, its layout, then the core.
fn record_proof<V: OpeningVerifier<E = F192>>(
    program: &Program,
    rec: &mut Recorder<V>,
    output: Output,
) -> Result<RecordedCore<V::Root, F192>, CpuError> {
    let (taus, rate) = Announcement::read_shape(rec.inner())?;
    let layout = Layout::announced(program.rv(), taus, ProofKind::ZeroKnowledge)?;
    let output = output.words().map(|o| rec.constant(F192::from(F64(o))));
    layout.record_core(rec, rate, &output)
}

/// What a zero-knowledge proof's verifier records of the plain core.
pub(crate) struct RecordedCore<R, E> {
    /// The key commitment, which the outer proof's opening is checked against.
    pub(crate) keys: KeyCommitment<R>,
    /// The claims the core leaves on the program's polynomials and the circuits' matrices, some of their parts hidden.
    pub(crate) claims: DeferredClaims<Value<E>>,
}

impl Layout {
    /// The plain core over a padded transcript, recorded, past the announced shape.
    ///
    /// It reads the stack's root, the key commitment's root, the final clock's hidden bits, then runs the plain core.
    ///
    /// It runs over any verifier, natively or in rows.
    ///
    /// # Errors
    ///
    /// Returns the first stage that refuses the proof.
    pub(crate) fn record_core<V: OpeningVerifier>(
        &self,
        rec: &mut Recorder<V>,
        rate: Rate,
        output: &[Value<V::E>; 4],
    ) -> Result<RecordedCore<V::Root, V::E>, CpuError> {
        let commitment = Commitment::read(rec, self.shape, rate)?;
        let keys = KeyCommitment::read(rec.inner(), rate.log_inv_rate().into())
            .map_err(|e| CpuError::Outer(OuterError::KeyOpening(e)))?;

        // The final clock: its live bit, and each free bit hidden and constrained to be a bit.
        rec.set_hidden(true);
        let mut clock = rec.constant(F192::from(F64(Clock::SEED_CLOCK)));
        for bit in FREE_CLOCK_BITS {
            let b = rec.prover_message()?;
            rec.ensure_bit(b, || CpuError::FinalClock)?;
            clock = rec.mul_const_add(b, F192::from(F64(1 << bit)), clock);
        }
        let claims = self.verify_committed(rec, &commitment, clock, output)?;
        Ok(RecordedCore { keys, claims })
    }
}

/// What the deferred claims need of the public polynomials, at their public points.
struct PublicEvaluations {
    /// The bytecode producer's terms `D_i`, one per twist weight.
    twist_terms: Vec<F192>,
    /// RAM's image at the image point.
    image: F192,
    /// Each circuit's weight on each bit slice.
    slice_weights: Vec<Vec<F192>>,
}

impl PublicEvaluations {
    /// The evaluations the prover's own claims need.
    ///
    /// # Panics
    ///
    /// Panics on a claim whose public coordinates are hidden: the prover's own claims never are.
    fn of(program: &Program, claims: &DeferredClaims<Value<F192>>) -> Self {
        let rv = program.rv();
        let point = &claims.program.point;
        let public = |xs: &[Value<F192>]| publics(xs).expect("a public point");
        let (bytecode, image_point) = (public(&point.bytecode), public(&point.image_point));
        let kbc = crate::log2_strict_usize(rv.entries().len());
        let (chi, alphas) = bytecode.split_at(kbc);
        let weights = bus::fingerprint_weights(alphas);
        let twist_terms = bus::producer_twist_terms(
            &mut Native,
            &Lookup::Bytecode.tuple(rv),
            &weights,
            chi,
            point.twist.len(),
        );
        let image = SparseColumn::new(rv.log_ram(), &[(0, rv.image())]).eval(&mut Native, &image_point);
        let slice_weights = (CircuitId::ALL.into_iter().zip(&claims.circuits))
            .map(|(f, c)| {
                // The weights depend on the slices' count, not their values.
                let form = public_form(&c.point).expect("a public form");
                let form = MatrixForm {
                    s_hat_v: vec![F192::ZERO; c.point.s_hat_v.len()],
                    ..form
                };
                form.slice_weights(f.circuit())
            })
            .collect();
        Self {
            twist_terms,
            image,
            slice_weights,
        }
    }

    /// Send them, in the order the verifier reads them.
    fn send(&self, ps: &mut ProverState) {
        ps.prover_messages(&self.twist_terms);
        ps.prover_message(&self.image);
        for weights in &self.slice_weights {
            ps.prover_messages(weights);
        }
    }
}

/// The values of elements that are all public.
fn publics<E: Copy>(xs: &[Value<E>]) -> Option<Vec<E>> {
    xs.iter().map(|&x| x.public()).collect()
}

/// A matrix form with no slices, if every coordinate but the slices is public.
fn public_form<E: Copy>(form: &MatrixForm<Value<E>>) -> Option<MatrixForm<E>> {
    Some(MatrixForm {
        alpha: form.alpha.public()?,
        z_skip: form.z_skip.public()?,
        x_inner_rest: publics(&form.x_inner_rest)?,
        r_inner_rest: publics(&form.r_inner_rest)?,
        s_hat_v: Vec::new(),
    })
}

/// A value the verifier read in the clear.
fn clear<E>(x: Value<E>) -> E {
    x.public().expect("read while hiding is off")
}

impl<E: Copy> DeferredClaims<Value<E>> {
    /// The claims of the plain shape: the hidden parts settled as constraints on public evaluations, then those batched.
    ///
    /// It reads the public evaluations, records one constraint per claim, draws `rho`, and batches:
    ///
    /// ```text
    ///     program:  twist = (1, rho, ..., rho^(L-1)),  image weight rho^L,  value sum_i rho^i D_i + rho^L image
    ///     circuit:  slices = (1, rho, ...),                                  value sum_i rho^i w_i
    /// ```
    ///
    /// A false public evaluation makes its batched claim false, except with probability `L / |E|` over `rho`.
    ///
    /// # Errors
    ///
    /// A claim of the wrong count or shape, or one whose point is hidden.
    pub(crate) fn into_plain<V: OpeningVerifier<E = E>>(
        self,
        rec: &mut Recorder<V>,
    ) -> Result<DeferredClaims<E>, CpuError> {
        if self.circuits.len() != N_CIRCUITS {
            return Err(CpuError::MalformedClaim(MalformedClaim::CircuitCount {
                expected: N_CIRCUITS,
                got: self.circuits.len(),
            }));
        }
        let malformed = CpuError::MalformedClaim(MalformedClaim::ProgramPoint);

        // The program claim: its point public, then value = image_weight image + sum_i twist_i D_i.
        let point = &self.program.point;
        let (Some(bytecode), Some(image_point)) = (publics(&point.bytecode), publics(&point.image_point)) else {
            return Err(malformed);
        };
        // A multiplicity is one word, so it has at most 64 bits; the point's own lengths are checked when it is settled.
        if point.twist.len() > 64 || bytecode.len() < N_TUPLE_BITS {
            return Err(malformed);
        }
        let terms = rec.prover_messages(point.twist.len())?;
        let image = rec.prover_message()?;
        let mut expected = rec.mul(point.image_weight, image);
        for (&mu, &d) in point.twist.iter().zip(&terms) {
            expected = rec.mul_add(mu, d, expected);
        }
        rec.ensure_eq(expected, self.program.value, || {
            CpuError::Constraint(ConstraintError::FinalMismatch)
        })?;

        // Each circuit claim: its form public but its slices, then value = sum_i s_i w_i.
        let mut forms = Vec::with_capacity(N_CIRCUITS);
        let mut weights = Vec::with_capacity(N_CIRCUITS);
        for (f, claim) in CircuitId::ALL.into_iter().zip(&self.circuits) {
            let (table, part) = (f.table().name(), f.part());
            let malformed = || CpuError::MalformedClaim(MalformedClaim::MatrixForm { table, part });
            let form = public_form(&claim.point).ok_or_else(malformed)?;
            let shape = MatrixForm {
                alpha: F192::ZERO,
                z_skip: F192::ZERO,
                x_inner_rest: vec![F192::ZERO; form.x_inner_rest.len()],
                r_inner_rest: vec![F192::ZERO; form.r_inner_rest.len()],
                s_hat_v: vec![F192::ZERO; claim.point.s_hat_v.len()],
            };
            if !f.shape().fits(&shape) {
                return Err(malformed());
            }
            let w = rec.prover_messages(claim.point.s_hat_v.len())?;
            let zero = rec.zero();
            let expected = (claim.point.s_hat_v.iter().zip(&w)).fold(zero, |acc, (&s, &w)| rec.mul_add(s, w, acc));
            rec.ensure_eq(expected, claim.value, || CpuError::Flock {
                table,
                part,
                error: FlockError::Lincheck(LincheckError::FormMismatch),
            })?;
            forms.push(form);
            weights.push(w);
        }

        // One challenge batches every public evaluation into the plain claims' shape.
        let rho = clear(rec.verifier_message());
        let v = rec.inner();
        let batched = |v: &mut V, values: &[Value<E>]| -> (Vec<E>, E) {
            let powers = v.powers(rho, values.len() + 1);
            let zero = v.zero();
            let sum = (values.iter().zip(&powers)).fold(zero, |acc, (&x, &p)| v.mul_add(clear(x), p, acc));
            (powers, sum)
        };
        let (mut twist, value) = batched(v, &terms);
        let image_weight = twist.pop().expect("one more power than terms");
        let value = v.mul_add(clear(image), image_weight, value);
        let program = Claim {
            point: ProgramPoint {
                bytecode,
                twist,
                image_weight,
                image_point,
            },
            value,
        };
        let circuits = (forms.into_iter().zip(&weights))
            .map(|(form, w)| {
                let (mut s_hat_v, value) = batched(v, w);
                s_hat_v.pop();
                Claim {
                    point: MatrixForm { s_hat_v, ..form },
                    value,
                }
            })
            .collect();
        Ok(DeferredClaims { program, circuits })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::cpu::{ProvenRun, Prover};
    use crate::rv::asm::{Addi, Asm, Reg};
    use crate::rv::{Region, RegisterFile};
    use crate::tables::TableId;
    use pcs::whir::WhirError;
    use std::panic::{AssertUnwindSafe, catch_unwind};
    use zk::Randomness;

    /// `a0 = 5; exit`, and a zero-knowledge proof of it under a test seed.
    fn proof(seed: u8) -> (Program, ProvenRun) {
        let text = Asm::new().i(Addi, Reg::A0, Reg::ZERO, 5).exit().finish();
        let program = Program::new(&text, Region::TEXT.base(), vec![], 0, 0).expect("a program");
        let run = Prover::new(Rate::MIN)
            .zero_knowledge(Randomness::Fixed([seed; 32]))
            .prove(&program, &[])
            .expect("the run exits");
        (program, run)
    }

    #[test]
    fn a_zero_knowledge_proof_verifies_and_is_a_function_of_its_seed() {
        let (program, run) = proof(7);
        assert!(run.proof.is_zero_knowledge());
        assert_eq!(program.verify(run.output, &run.proof), Ok(()));
        assert_eq!(Proof::from_bytes(&run.proof.to_bytes()), Ok(run.proof.clone()));

        // Another output is another statement.
        assert!(program.verify(Output::new([6, 0, 0, 0]), &run.proof).is_err());

        // The same body labelled plain is read under the plain session, and refused.
        let relabelled = Proof(run.proof.0.clone(), ProofKind::Plain);
        assert!(program.verify(run.output, &relabelled).is_err());

        // One seed, one proof; another seed, another valid proof.
        assert_eq!(proof(7).1.proof, run.proof);
        let other = proof(8).1.proof;
        assert_eq!(program.verify(run.output, &other), Ok(()));
    }

    #[test]
    fn every_part_of_a_zero_knowledge_proof_is_bound() {
        // Flip one bit of every 997th message byte, then of each of the last 512: the outer proof and the key opening.
        let (program, run) = proof(7);
        let n = run.proof.0.narg.len();
        for i in (0..n).step_by(997).chain(n.saturating_sub(512)..n) {
            let mut forged = run.proof.clone();
            forged.0.narg[i] ^= 1;
            let verdict = catch_unwind(AssertUnwindSafe(|| program.verify(run.output, &forged)));
            assert!(
                matches!(verdict, Ok(Err(_))),
                "byte {i} of {n}: tampered and not refused"
            );
        }
    }

    #[test]
    fn a_hidden_final_clock_cannot_carry_a_failure() {
        // The forged run of the plain test: the exit's write pulls the tuple it pushes, and its clock flags it.
        //
        // In zero knowledge the final clock is hidden, its free bits below the live bit:
        //
        //     clock = 2^40 + sum_{5 <= i < 40} b_i 2^i,   each b_i a bit
        //
        // The failure bit 41 has no place in it, so the bus cannot balance and the outer proof fails.
        let text = Asm::new().i(Addi, Reg::A0, Reg::ZERO, 42).exit().finish();
        let program = Program::new(&text, Region::TEXT.base(), vec![], 2, 0).expect("valid instruction program");
        let mut forged = program.execute(&[]).unwrap();
        let exit = forged.trace.rows[TableId::ALU]
            .iter_mut()
            .find(|r| r.index == 2)
            .unwrap();
        (exit.prev[2], exit.vd_old) = (exit.ts | 3, exit.out);
        let sink = RegisterFile::SINK as usize;
        (forged.trace.reg_ts[sink], forged.trace.reg_fin[sink]) = (F64(Clock::SEED_CLOCK), F64::ZERO);
        forged.trace.ts_final |= 1 << Clock::FAIL_BIT;
        let prover = Prover::new(Rate::MIN).zero_knowledge(Randomness::Fixed([3; 32]));
        let (proof, _) = program.prove_execution(&forged, &prover);
        // The recorded rows do not hold, so the outer proof's claims are false and the key opening refuses them.
        let refused = CpuError::Outer(OuterError::KeyOpening(WhirError::TerminalMismatch));
        assert_eq!(program.verify(forged.output.into(), &proof), Err(refused.into()));
    }
}
