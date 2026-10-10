//! Zero-knowledge proofs of a run: the plain proof under one-time pads on a hiding commitment, then an outer proof that the padded transcript passes the verifier's checks.
//!
//! After the zero-knowledge seed, the transcript is:
//!
//! ```text
//!     clear    each table's height and the rate: the run's public shape
//!     clear    the stack's root (every lane padded, one uniform lane last), then the key commitment's root
//!     hidden   the final clock's free bits, the bus, the table sumcheck, flock's reductions, the opening's lane rounds
//!     clear    the opening's claim after its lane fold, its padding's fold, the rest of the opening
//!     hidden   each product and inverse of hidden values the verifier makes
//!     clear    the outer proof, then the key commitment's opening
//! ```
//!
//! A hidden scalar travels under the next key. The verifier runs its own code over the padded transcript with the recording arithmetic of [`crate::zk::sym`], and the outer proof shows the keys satisfy what it recorded.

use super::layout::{Announcement, Layout};
use super::witness::Witness;
use super::{CpuError, Output, Program, Proof};
use crate::pcs::{self, Commitment, Committed, LOG_BATCH, Rate};
use crate::tables::Clock;
use crate::zk::keys::{self, KEY_MU, KeyStack, LANE, MAX_KEYS, MAX_OUTER_LOG_ROWS};
use crate::zk::outer::constraint_system;
use crate::zk::randomness::{Purpose, Randomness, ZkRng};
use crate::zk::spartan::{self, OuterClaims};
use crate::zk::sym::{Form, Recorder, Sym, Var};
use ::pcs::verifier::OpeningVerifier;
use ::pcs::whir::{self, Hiding, ProverData, WhirError, config_for_rate_hiding};
use fiat_shamir::arith::{Arith, Verifier};
use fiat_shamir::merkle::Hash;
use fiat_shamir::transcript::{Challenger, ProverState, RawProof, Transmitter, VerifierState};
use primitives::field::{F64, F192};
use primitives::multilinear::{eq_table, inner_product};
use std::ops::Range;
use tracing::info_span;

/// The final clock's bits a run may set: past its slot's bits and below its live bit, which is set (§sec:state).
const FREE_CLOCK_BITS: Range<usize> = Clock::SLOT_BITS as usize..Clock::LIVE_BIT as usize;

/// Prove a built witness in zero knowledge.
///
/// # Panics
///
/// Panics if the witness's bus does not balance, or if its padded transcript outgrows the key commitment.
pub(super) fn prove(program: &Program, mut w: Witness, output: Output, rate: Rate, randomness: Randomness) -> Proof {
    let rng = ZkRng::new(randomness);
    let log_inv_rate = rate.log_inv_rate().into();
    let seed = program.seed(true);
    let public = output.words().map(F64);
    let mut ps = ProverState::new(seed, public);
    Announcement::write_shape(&w.layout.taus, rate, &mut ps);

    // The stack, its last lane uniform and every lane padded, then the keys, before any challenge.
    let shape = w.layout.shape;
    let committed = info_span!("Commit").in_scope(|| {
        let lane = 1usize << (shape.mu - LOG_BATCH);
        rng.fill_k(Purpose::RandomLane, &mut w.q[shape.n_lanes * lane..]);
        let mut pads = vec![F64::ZERO; shape.committed_lanes() * pcs::padding(shape.mu, log_inv_rate)];
        rng.fill_k(Purpose::Pads, &mut pads);
        Committed::new_padded(&mut ps, &w.q, shape, rate, &pads).expect("the witness matches its layout")
    });
    let stack = KeyStack::draw(&rng);
    let key_data = info_span!("Commit keys").in_scope(|| {
        let mut pads = vec![F64::ZERO; 2 * pcs::padding(KEY_MU, log_inv_rate)];
        rng.fill_k(Purpose::KeyPads, &mut pads);
        let data = whir::commit_hiding(&stack.words, KEY_MU, LOG_BATCH, log_inv_rate, &pads);
        ps.add_root(&data.root());
        data
    });

    // The plain proof, every scalar it sends padded until its opening's lane fold ends.
    ps.set_keys(stack.keys().to_vec());
    ps.set_hidden(true);
    for bit in FREE_CLOCK_BITS {
        ps.add_scalar(F192::from(F64(w.ts_final >> bit & 1)));
    }
    let (slots, rings) = program.prove_reductions(&mut ps, &mut w, output);
    info_span!("PCS open").in_scope(|| {
        committed
            .open(&mut ps, &w.q, &slots, &rings)
            .expect("opening uses the committed witness");
    });
    drop((committed, w, slots, rings));

    // The verifier's record of the padded transcript, which the prover replays knowing the keys.
    let (record, n_keys) = info_span!("Record").in_scope(|| {
        let snapshot = ps.snapshot();
        let mut rec = Recorder::with_keys(VerifierState::new(seed, &snapshot, public), stack.keys().to_vec());
        record(program, &mut rec, output).expect("the prover's own proof verifies");
        let n_keys = rec.n_keys() as usize;
        (rec.finish_record().1, n_keys)
    });
    // The auxiliary variables' values, in the outer system's order, each under its key.
    let sent: Vec<F192> = (record.aux_order().iter())
        .map(|&j| record.aux_values[j as usize])
        .collect();
    assert!(
        n_keys + sent.len() <= MAX_KEYS,
        "the padded transcript outgrows the key commitment"
    );
    ps.set_hidden(true);
    ps.add_scalars(&sent);
    ps.set_hidden(false);
    let keys = stack.keys();
    let aux: Vec<Form> = (sent.iter().enumerate())
        .map(|(r, &value)| aux_form(value + keys[n_keys + r], n_keys + r))
        .collect();

    // The outer proof, then the key commitment's opening.
    info_span!("Outer proof").in_scope(|| {
        let r1cs = constraint_system(&record, &aux);
        assert!(
            r1cs.log_rows() <= MAX_OUTER_LOG_ROWS,
            "the outer system outgrows its mask"
        );
        let claims = spartan::prove(&mut ps, &r1cs, &stack.z(), stack.libra(r1cs.log_rows()));
        open_keys(&mut ps, &stack, &key_data, &claims, log_inv_rate);
    });
    Proof(ps.into_proof(), true)
}

/// Verify a zero-knowledge proof, and return it with every query's Merkle path written out.
///
/// # Errors
///
/// Returns the first stage that refuses the proof.
pub(super) fn verify(program: &Program, output: Output, proof: &Proof) -> Result<RawProof, CpuError> {
    let vs = VerifierState::new(program.seed(true), &proof.0, output.words().map(F64));
    let mut rec = Recorder::new(vs);
    let (key_root, rate) = record(program, &mut rec, output)?;

    // The auxiliary variables, each a hidden scalar.
    let keys = (rec.n_keys() + rec.n_aux()) as usize;
    if keys > MAX_KEYS {
        return Err(CpuError::TooManyKeys { keys, max: MAX_KEYS });
    }
    rec.set_hidden(true);
    let mut aux = Vec::with_capacity(rec.n_aux() as usize);
    for _ in 0..rec.n_aux() {
        let s = rec.next_scalar()?;
        aux.push(rec.form(s));
    }
    rec.set_hidden(false);
    let (mut vs, record) = rec.finish_record();

    let r1cs = constraint_system(&record, &aux);
    if r1cs.log_rows() > MAX_OUTER_LOG_ROWS {
        return Err(CpuError::OuterSize {
            log_rows: r1cs.log_rows(),
            max: MAX_OUTER_LOG_ROWS,
        });
    }
    let claims = spartan::verify(&mut vs, &r1cs)?;
    verify_keys(&mut vs, key_root, &claims, rate.log_inv_rate().into()).map_err(CpuError::KeyOpen)?;
    vs.finish()?;
    Ok(vs.into_raw_proof())
}

/// The plain verifier over a padded transcript, recorded: the shape, the two roots, the final clock's bits, the core, then the deferred claims. It returns the key commitment's root and the rate.
fn record<T>(program: &Program, rec: &mut Recorder<T>, output: Output) -> Result<(Hash, Rate), CpuError>
where
    T: OpeningVerifier<E = F192, K = F64, Root = Hash, Query = usize>,
{
    let (taus, rate) = Announcement::read_shape(rec.transport())?;
    let layout = Layout::announced(program.rv(), taus, true)?;
    let commitment = Commitment::read(rec, layout.shape, rate)?;
    let key_root = rec.next_root()?;

    // The final clock: its live bit, and each free bit hidden and a bit.
    rec.set_hidden(true);
    let mut clock = Sym::Pub(F192::from(F64(1 << Clock::LIVE_BIT)));
    for bit in FREE_CLOCK_BITS {
        let b = rec.next_scalar()?;
        rec.boolean(b);
        clock = rec.mul_const_add(b, F192::from(F64(1 << bit)), clock);
    }
    let output = output.words().map(|o| Sym::Pub(F192::from(F64(o))));
    let claims = layout.verify_committed(rec, &commitment, clock, &output)?;
    program.check_deferred_hidden(rec, &claims)?;
    Ok((key_root, rate))
}

/// The form of the auxiliary value sent as `sent` under key `key`.
fn aux_form(sent: F192, key: usize) -> Form {
    Form {
        constant: sent,
        terms: vec![(Var::Key(u32::try_from(key).expect("a key index fits a u32")), F192::ONE)],
    }
}

/// Open the key commitment at the outer proof's claims, batched by one challenge.
fn open_keys(ps: &mut ProverState, stack: &KeyStack, data: &ProverData, claims: &OuterClaims, log_inv_rate: usize) {
    let cfg = config_for_rate_hiding(KEY_MU, log_inv_rate).expect("the key commitment's size is configured");
    let lambda = ps.sample();
    let (mut weight, target) = keys::opening_claim(claims, lambda);
    weight.resize(2 * LANE, F192::ZERO);
    let hiding = Hiding { hidden_claim: false };
    whir::open_hiding(&cfg, KEY_MU, &stack.words, weight, target, data, hiding, ps);
}

/// Verify the key commitment's opening at the outer proof's claims.
fn verify_keys(vs: &mut VerifierState, root: Hash, claims: &OuterClaims, log_inv_rate: usize) -> Result<(), WhirError> {
    let cfg = config_for_rate_hiding(KEY_MU, log_inv_rate)?;
    let lambda = Challenger::sample(vs);
    let (weight, target) = keys::opening_claim(claims, lambda);
    let hiding = Hiding { hidden_claim: false };
    // The weight lives on lane 0, the stack's first `LANE` words: its low variables index the word, the rest are zero.
    let weight_at = |_: &mut VerifierState, x: &[F192]| {
        let low = LANE.trailing_zeros() as usize;
        let lane_0 = x[low..].iter().fold(F192::ONE, |acc, &xi| acc * (F192::ONE + xi));
        lane_0 * inner_product(&weight, &eq_table(&x[..low]))
    };
    whir::verify_hiding(vs, &cfg, KEY_MU, 2, target, root, hiding, weight_at)
}

#[cfg(test)]
mod tests {
    use crate::cpu::{Program, Proof, ProvenRun, Prover};
    use crate::pcs::Rate;
    use crate::rv::Region;
    use crate::rv::asm::{Addi, Asm, Reg};
    use crate::zk::randomness::Randomness;
    use primitives::field::F192;
    use std::panic::AssertUnwindSafe;

    fn proof(seed: u8) -> (Program, ProvenRun) {
        let text = Asm::new().i(Addi, Reg::A0, Reg::ZERO, 5).exit().finish();
        let program = Program::new(&text, Region::TEXT.base(), vec![], 0, 0).expect("a program");
        let run = Prover::new(Rate::MIN)
            .zk(Randomness::Seed([seed; 32]))
            .prove(&program, &[])
            .expect("the run exits");
        (program, run)
    }

    #[test]
    fn a_zero_knowledge_proof_verifies_and_is_a_function_of_its_seed() {
        let (program, run) = proof(7);
        assert!(run.proof.is_zk());
        program.verify(run.output, &run.proof).unwrap();
        assert_eq!(Proof::from_bytes(&run.proof.to_bytes()), Ok(run.proof.clone()));

        // A zero-knowledge proof read as a plain one is refused.
        assert!(program.verify(run.output, &Proof(run.proof.0.clone(), false)).is_err());

        // One seed, one proof; another seed reveals other scalars past the public shape.
        assert_eq!(proof(7).1.proof, run.proof);
        let other = proof(8).1.proof;
        program.verify(run.output, &other).unwrap();
        let shared = (run.proof.0.stream.iter().zip(&other.0.stream))
            .skip(crate::tables::N_TABLES + 1)
            .filter(|(a, b)| a == b)
            .count();
        assert!(shared < 8, "{shared} scalars shared past the announcement");
    }

    #[test]
    fn every_part_of_a_zero_knowledge_proof_is_bound() {
        let (program, run) = proof(7);
        let n = run.proof.0.stream.len();
        // Every 17th scalar, then the whole tail: the outer proof and the key opening.
        for i in (0..n).step_by(17).chain(n.saturating_sub(64)..n) {
            let mut forged = run.proof.clone();
            forged.0.stream[i] += F192::ONE;
            let verdict = std::panic::catch_unwind(AssertUnwindSafe(|| program.verify(run.output, &forged)));
            assert!(
                matches!(verdict, Ok(Err(_))),
                "scalar {i} of {n}: tampered and not refused"
            );
        }
    }
}
