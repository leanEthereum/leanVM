use super::flock::Reduction;
use super::recursion::RecRows;
use super::ring::RingShare;
use super::whir::Opening;
use super::{ProofShape, RecShape, Rows};
use crate::class_flock::FlockId;
use crate::constraints::ConstraintError;
use crate::cpu::{CpuError, DeferredClaims, Output, Program, ProvenRun, Prover, UNGROUND_LOG_BYTECODE};
use crate::leaf::BusError;
use crate::pcs::{Rate, RingSwitch, SliceClaim, StackClaim};
use crate::rec::RecError;
use crate::rec::circuit::{Assignment, Builder, Circuit, Ew, Finished, Kw, Limbs, Unsatisfied};
use crate::rec::fixed::FixedColumns;
use crate::rec::table::HashFlock;
use crate::rec::transcript::{ProofSource, Transcript};
use crate::rv::Region;
use crate::rv::asm::*;
use crate::tables::{Fill, N_TABLES, PerTable, TableId};
use crate::witness::StackShape;
use ::flock::reduction::{self, Instance, ReductionReplay, Shape};
use ::flock::zerocheck::K_SKIP;
use ::pcs::pack::PACKING_WIDTH;
use ::pcs::stack_open::RingFamily;
use ::pcs::whir::inner_product_base_ext;
use fiat_shamir::transcript::{ProofTranscript, ProverState, RawProof, TranscriptError, VerifierState};
use primitives::field::{F64, F192};
use primitives::test_util::Rng;
use std::sync::OnceLock;

// A program with a loop, so that every framework block is read.
fn small_program() -> Program {
    let text = Asm::new()
        .li(Reg::T0, 0x0123_4567_89ab_cdef)
        .li(Reg::T1, 9)
        .r(Xor, Reg::A0, Reg::T0, Reg::T1)
        .label("loop")
        .i(Addi, Reg::T1, Reg::T1, -1)
        .branch(Bne, Reg::T1, Reg::ZERO, "loop")
        .exit()
        .finish();
    Program::new(&text, Region::TEXT.base(), vec![3, 5], 2, 0).expect("a valid program")
}

// One honest proof of the small program, as the native verifier read it.
struct Fixture {
    program: Program,
    raw: RawProof,
    output: Output,
    taus: PerTable<usize>,
    native: DeferredClaims,
}

// Proven once, shared by every test.
fn fixture() -> &'static Fixture {
    static FIXTURE: OnceLock<Fixture> = OnceLock::new();
    FIXTURE.get_or_init(|| {
        let program = small_program();
        let ProvenRun { proof, output, .. } = Prover::new(Rate::MIN).prove(&program, &[]).expect("the run halts");
        let native = program.verify_core(output, &proof).expect("an honest proof");
        let raw = program.verify_to_raw(output, &proof).expect("an honest proof");
        let taus = PerTable::from_fn(|t: TableId| usize::try_from(proof.0.stream[t.index()].c0).expect("a height"));
        Fixture {
            program,
            raw,
            output,
            taus,
            native,
        }
    })
}

impl Fixture {
    // The core's rows over `source`: the builder, holding the wires' values, and the claims the core leaves.
    fn build(&self, source: ProofSource<'_>) -> (Builder, DeferredClaims<Ew>) {
        let shape = ProofShape::new(&self.program, self.taus, Rate::MIN).expect("an honest shape");
        let mut b = Builder::new();
        let output = self.output.words().map(|o| b.free_k(o));
        let core = shape.verify_core(&mut b, output, source);
        (b, core.claims)
    }

    // The checks a forged proof fails, in the order the rows meet them.
    fn failures(&self, raw: &RawProof) -> Vec<String> {
        let failures = self.build(ProofSource::Proof(raw)).0.finish().failures;
        failures.iter().map(Unsatisfied::to_string).collect()
    }
}

fn values(b: &Builder, claims: &DeferredClaims<Ew>) -> DeferredClaims {
    claims.map(|w| b.e(w))
}

#[test]
fn the_core_leaves_the_native_deferred_claims() {
    let f = fixture();
    let (b, claims) = f.build(ProofSource::Proof(&f.raw));
    let got = values(&b, &claims);
    assert_eq!(got.program, f.native.program, "the program claim");
    for (i, (got, native)) in got.circuits.iter().zip(&f.native.circuits).enumerate() {
        assert_eq!(got, native, "circuit {i}'s matrix claim");
    }
    assert_eq!(got, f.native);
    f.program.check_deferred(&got).expect("the rows' claims settle");
    let Finished { circuit, failures, .. } = b.finish();
    assert!(failures.is_empty(), "{failures:?}");
    assert!(
        circuit == f.build(ProofSource::Shape).0.finish().circuit,
        "the shape builds another circuit"
    );
}

#[test]
fn a_tampered_proof_fails_where_the_native_verifier_does() {
    let f = fixture();
    let first = |raw: &RawProof| f.failures(raw).into_iter().next().unwrap_or_default();

    // The GKR's root, read right after the announcement and the commitment's two halves.
    let mut forged = f.raw.clone();
    forged.stream[N_TABLES + 4].c1 ^= 1;
    assert!(first(&forged).starts_with("bus and tables"), "{}", first(&forged));

    // A sibling and a leaf word of the first and the last opening.
    for opening in [0, f.raw.merkle.len() - 1] {
        let mut forged = f.raw.clone();
        forged.merkle[opening].path[1][0] ^= 1;
        assert!(
            first(&forged).starts_with("opening / whir / rows"),
            "{}",
            first(&forged)
        );
        let mut forged = f.raw.clone();
        let last = forged.merkle[opening].leaf_data.len() - 1;
        forged.merkle[opening].leaf_data[last].0 ^= 1;
        assert!(
            first(&forged).starts_with("opening / whir / rows"),
            "{}",
            first(&forged)
        );
    }
}

#[test]
fn a_forged_announcement_is_refused_first() {
    let f = fixture();
    let clock = N_TABLES + 1;
    let ts = f.raw.stream[clock];
    let forge = |edit: &dyn Fn(&mut RawProof)| {
        let mut forged = f.raw.clone();
        edit(&mut forged);
        f.failures(&forged).into_iter().next().unwrap_or_default()
    };
    for t in 0..N_TABLES {
        let failure = forge(&|p| p.stream[t].c0 += 1);
        assert!(failure.starts_with("announcement"), "height {t}: {failure}");
    }
    let edits: [(&str, F192); 7] = [
        ("the rate", F192::new(2, 0, 0)),
        ("a slot bit", F192::new(ts.c0 | 1, 0, 0)),
        ("no live bit", F192::new(ts.c0 & !(1 << 40), 0, 0)),
        ("a failure bit", F192::new(ts.c0 | 1 << 41, 0, 0)),
        ("the top bit", F192::new(ts.c0 | 1 << 63, 0, 0)),
        ("the second limb", F192::new(ts.c0, 1, 0)),
        ("the third limb", F192::new(ts.c0, 0, 1)),
    ];
    for (i, (what, value)) in edits.into_iter().enumerate() {
        let at = if i == 0 { N_TABLES } else { clock };
        let failure = forge(&|p| p.stream[at] = value);
        assert!(failure.starts_with("announcement"), "{what}: {failure}");
    }
    // A live clock at slot zero passes the announcement, and the bus refuses the wrong one.
    let failure = forge(&|p| p.stream[clock] = F192::new(ts.c0 + 32, 0, 0));
    assert!(failure.starts_with("bus and tables"), "a later clock: {failure}");
}

// A program past the unground bytecode: its rows check the bus's proof of work, which a smaller program's never meet.
#[test]
fn a_large_programs_rows_check_its_grinding() {
    // The exit, then nops nothing runs, enough for one bit of grinding.
    let mut a = Asm::new();
    a.li(Reg::A0, 7).exit();
    for _ in 0..1 << UNGROUND_LOG_BYTECODE {
        a.i(Addi, Reg::ZERO, Reg::ZERO, 0);
    }
    let program = Program::new(&a.finish(), Region::TEXT.base(), vec![], 0, 0).expect("a valid program");
    let ProvenRun { proof, output, .. } = Prover::new(Rate::MIN).prove(&program, &[]).expect("the run halts");
    let f = Fixture {
        native: program.verify_core(output, &proof).expect("an honest proof"),
        raw: program.verify_to_raw(output, &proof).expect("an honest proof"),
        taus: PerTable::from_fn(|t: TableId| usize::try_from(proof.0.stream[t.index()].c0).expect("a height")),
        program,
        output,
    };

    // The rows leave the native claims, and the shape builds the same circuit.
    let (b, claims) = f.build(ProofSource::Proof(&f.raw));
    assert_eq!(values(&b, &claims), f.native);
    let Finished { circuit, failures, .. } = b.finish();
    assert!(failures.is_empty(), "{failures:?}");
    assert!(circuit == f.build(ProofSource::Shape).0.finish().circuit);

    // The nonce follows the announcement and the root: one the native verifier refuses for missing the work fails at the bus.
    let missed = CpuError::Bus(BusError::Transcript(TranscriptError::PowFailed { bits: 1 }));
    let forged = (1..64)
        .map(|step| {
            let mut forged = proof.clone();
            forged.0.stream[N_TABLES + 4].c0 += step;
            forged
        })
        .find(|forged| f.program.verify_core(f.output, forged).err() == Some(missed.clone()))
        .expect("half the nonces miss one bit of work");
    let mut forged_raw = f.raw.clone();
    forged_raw.stream = forged.0.stream;
    let failure = f.failures(&forged_raw).into_iter().next().unwrap_or_default();
    assert!(failure.starts_with("bus and tables"), "{failure}");
}

// The direction bit of a Merkle node is the hash row's mux selector: a non-Boolean one is refused by the outer verifier.
#[test]
fn a_non_boolean_merkle_selector_is_refused() {
    let mut b = Builder::new();
    let acc = b.free_d([1, 2, 3, 4]);
    let bit = b.free_k(1);
    let parent = b.node(acc, bit, [5, 6, 7, 8]);
    b.expose_d(parent);
    let Finished {
        circuit,
        assignment: mut a,
        failures,
    } = b.finish();
    assert!(failures.is_empty(), "{failures:?}");
    let iv = [F64(7); 4];
    let statement = a.statement().to_vec();
    let prove = |a: &Assignment| circuit.prove(a, iv, Rate::MIN).expect("the circuit fits");
    let verify = |proof: &ProofTranscript| circuit.verify_to_raw(&statement, iv, Rate::MIN, proof).map(|_| ());
    assert_eq!(verify(&prove(&a)), Ok(()));
    a.values[bit.0 as usize][0] = 2;
    assert_eq!(
        verify(&prove(&a)),
        Err(RecError::Constraint(ConstraintError::FinalMismatch))
    );
}

const LABEL: &[u8] = b"rec-verifier-test";

fn label_cv() -> Limbs {
    fiat_shamir::digest_words(&primitives::hash::hash(LABEL)).map(|w| w.0)
}

// A rows transcript from the test label over `source`, and what `f` builds on it.
fn replay<T>(source: ProofSource<'_>, f: impl FnOnce(&mut Rows<'_, '_>) -> T) -> (Builder, T, bool) {
    let mut b = Builder::new();
    let cv = b.d_const(label_cv());
    let mut t = Transcript::from_state(cv, source);
    let out = f(&mut Rows::new(&mut b, &mut t));
    let finished = t.finished();
    (b, out, finished)
}

fn raw(proof: &ProofTranscript) -> RawProof {
    RawProof {
        stream: proof.stream.clone(),
        merkle: Vec::new(),
    }
}

// Packed witness `f`'s batch over `rows`, as the prover holds it.
fn batch<const N: usize>(f: FlockId, rows: &[[u64; N]]) -> Instance<'static> {
    let (circuit, spec) = (f.circuit(), f.table().spec());
    let n_blocks_log = spec.n_blocks_log(rows.len());
    let witness = match spec.circuit.as_ref().map(|c| c.fill) {
        Some(Fill::Instance(instance)) => {
            circuit.generate_witness_with(rows, &[0; N], n_blocks_log, |row, z, az, bz| instance(row, z, az, bz))
        }
        _ => circuit.generate_witness(rows, n_blocks_log),
    };
    Instance {
        block: circuit.block(),
        n_blocks_log,
        witness,
    }
}

// The reduction in rows agrees with the native replay, and a tampered scalar fails both, where the native verifier fails.
fn check_reductions(batches: &[Instance<'static>]) {
    let proof = {
        let mut ps = ProverState::from_label(LABEL);
        reduction::prove(batches, &mut ps);
        ps.into_proof()
    };
    let circuits: Vec<(Shape, usize)> = (batches.iter())
        .map(|batch| (batch.block.shape(), batch.n_blocks_log))
        .collect();
    let native = |proof: &ProofTranscript| {
        let mut vs = VerifierState::from_label(LABEL, proof);
        reduction::verify(&circuits, &mut vs)
    };
    let rows = |proof: &RawProof| replay(ProofSource::Proof(proof), |r| Reduction::replay(r, &circuits));

    let replays = native(&proof).expect("an honest batch");
    let (b, reductions, finished) = rows(&raw(&proof));
    assert!(finished, "the rows read the whole stream");
    for (f, ((batch, reduction), replay)) in batches.iter().zip(&reductions).zip(&replays).enumerate() {
        let point: Vec<F192> = reduction.slice.suffix_point.iter().map(|&w| b.e(w)).collect();
        assert_eq!(point, replay.claim.suffix_point, "circuit {f}'s point");
        assert_eq!(reduction.matrix.point.map(|w| b.e(w)), replay.matrices.form);
        assert_eq!(b.e(reduction.matrix.value), replay.matrices.value);
        assert_eq!(
            replay.matrices.form.evaluate(batch.block.circuit),
            replay.matrices.value
        );
    }
    let Finished { circuit, failures, .. } = b.finish();
    assert!(failures.is_empty(), "{failures:?}");
    let shaped: Circuit = replay(ProofSource::Shape, |r| Reduction::replay(r, &circuits))
        .0
        .finish()
        .circuit;
    assert!(circuit == shaped, "the shape builds another circuit");

    // The first scalar of the zerocheck's first round, the last circuit's `c` claim, the last lincheck round's top
    // coefficient, the first circuit's first slice and its form's value.
    let n = batches.len();
    let tail = n * (PACKING_WIDTH + 1);
    let n_rounds = (circuits.iter())
        .map(|(shape, _)| shape.k_log - K_SKIP)
        .max()
        .unwrap_or(0);
    let lincheck_start = proof.stream.len() - tail - 2 * n_rounds;
    let len = proof.stream.len();
    let tampers = [
        (0, "zerocheck"),
        (lincheck_start - 1, "zerocheck"),
        (len - tail - 1, "lincheck"),
        (len - tail, "lincheck"),
        (len - tail + PACKING_WIDTH, "lincheck"),
    ];
    for (index, stage) in tampers {
        let mut forged = proof.clone();
        forged.stream[index] += F192::ONE;
        assert!(native(&forged).is_err(), "the native verifier refuses scalar {index}");
        let failures = rows(&raw(&forged)).0.finish().failures;
        assert!(
            failures.first().is_some_and(|f| f.scope()[0] == stage),
            "scalar {index}: {failures:?}"
        );
    }

    // A value moved between two circuits' forms keeps the batch's identity: the core accepts, and the claims do not settle.
    if n > 1 {
        let lifts: Vec<F192> = {
            // A circuit's lincheck rounds bind its inner coordinates top first: its round challenges are its
            // column point reversed, a prefix of the longest circuit's.
            let rounds = |replay: &ReductionReplay| replay.matrices.form.r_inner_rest.len();
            let longest = replays.iter().max_by_key(|r| rounds(r)).expect("a batch");
            let r_rounds: Vec<F192> = longest.matrices.form.r_inner_rest.iter().rev().copied().collect();
            let alpha_4 = replays[0].matrices.form.alpha.square().square();
            let weights = primitives::field::powers(alpha_4, n);
            (replays.iter().zip(weights))
                .map(|(replay, w)| r_rounds[rounds(replay)..].iter().fold(w, |acc, &r| acc * r))
                .collect()
        };
        let delta = F192::new(7, 0, 0);
        let mut forged = proof;
        forged.stream[len - tail + PACKING_WIDTH] += delta * lifts[1];
        forged.stream[len - tail + 2 * PACKING_WIDTH + 1] += delta * lifts[0];
        let moved = native(&forged).expect("the batch's identity holds");
        let (b, reductions, _) = rows(&raw(&forged));
        for (f, (reduction, replay)) in reductions.iter().zip(&moved).enumerate() {
            let matrices = &replay.matrices;
            assert_eq!(b.e(reduction.matrix.value), matrices.value);
            let settles = matrices.form.evaluate(batches[f].block.circuit) == matrices.value;
            assert_eq!(settles, f > 1, "circuit {f}'s moved claim");
        }
        let failures = b.finish().failures;
        assert!(failures.is_empty(), "{failures:?}");
    }
}

fn hash_batch(seed: u64) -> Instance<'static> {
    let mut rng = Rng::new(seed);
    let rows: Vec<[u64; 14]> = (0..5).map(|_| std::array::from_fn(|_| rng.next_u64())).collect();
    batch(HashFlock::FLOCK, &rows)
}

fn ld_batch(seed: u64, n: usize) -> Instance<'static> {
    let mut rng = Rng::new(seed);
    let rows: Vec<[u64; 2]> = (0..n).map(|_| [rng.next_u64(), rng.next_u64()]).collect();
    batch(FlockId::class(TableId::LD).unwrap(), &rows)
}

#[test]
fn the_hash_reduction_in_rows_is_the_native_one() {
    check_reductions(&[hash_batch(0xA7)]);
}

// Two block sizes, and two batches of one circuit at different heights, so the claims sit at prefixes of one another.
#[test]
fn a_mixed_batch_in_rows_is_the_native_one() {
    check_reductions(&[ld_batch(0x5EED, 20), hash_batch(0xA7), ld_batch(0xB0B, 300)]);
}

// Fewer lanes than a leaf holds, and not whole blocks of them, so the level-0 image has a zero prefix.
const N_LANES: usize = 37;

// The 64 bit slices of the packed words `q` at `point`.
fn slices(q: &[F64], point: &[F192]) -> Vec<F192> {
    let eq = primitives::multilinear::eq_table(point);
    (0..PACKING_WIDTH)
        .map(|i| (q.iter().zip(&eq)).fold(F192::ZERO, |acc, (w, &e)| if w.0 >> i & 1 == 1 { acc + e } else { acc }))
        .collect()
}

// The regions with every claim's elements as free wires holding their values.
fn ring_wires(r: &mut Rows<'_, '_>, rings: &[RingSwitch]) -> Vec<RingSwitch<Ew>> {
    (rings.iter())
        .map(|ring| RingSwitch {
            offset: ring.offset,
            qflock_vars: ring.qflock_vars,
            claims: (ring.claims.iter())
                .map(|claim| SliceClaim {
                    suffix_point: claim.suffix_point.iter().map(|&v| r.b.free_e(v)).collect(),
                    s_hat_v: claim.s_hat_v.iter().map(|&v| r.b.free_e(v)).collect(),
                })
                .collect(),
        })
        .collect()
}

// Point and strided claims and two ring-switched regions on a stack of `N_LANES` lanes, their values read from `q`.
fn opening_claims(mu: usize, q: &[F64], rng: &mut Rng) -> (Vec<StackClaim>, Vec<RingSwitch>) {
    let lane = 1usize << (mu - crate::pcs::LOG_BATCH);
    let eq = primitives::multilinear::eq_table;
    let mut slots = Vec::new();
    for (offset, vars) in [(0, mu - 6), (2 * lane, mu - 5), (8, 3), (5, 0)] {
        let low_point = rng.ext_vec(vars);
        let value = inner_product_base_ext(&q[offset..offset + (1 << vars)], &eq(&low_point));
        slots.push(StackClaim::Point {
            offset,
            low_point,
            value,
        });
    }
    for (offset, slot, stride_log) in [(4 * lane, 5, 3), (6 * lane, 0, 0)] {
        let point = rng.ext_vec(mu - 6 - stride_log);
        let value = (eq(&point).iter().enumerate()).fold(F192::ZERO, |acc, (j, e)| {
            acc + e.mul_base(q[offset + slot + (j << stride_log)])
        });
        slots.push(StackClaim::Strided {
            offset,
            slot,
            stride_log,
            point,
            value,
        });
    }
    let rings = [(4 * lane, mu - 4, 2), (16 * lane, mu - 5, 1)]
        .into_iter()
        .map(|(offset, qflock_vars, n_claims)| RingSwitch {
            offset,
            qflock_vars,
            claims: (0..n_claims)
                .map(|_| {
                    let suffix_point = rng.ext_vec(qflock_vars);
                    let s_hat_v = slices(&q[offset..offset + (1 << qflock_vars)], &suffix_point);
                    SliceClaim { suffix_point, s_hat_v }
                })
                .collect(),
        })
        .collect();
    (slots, rings)
}

// The opening's rows over `source`, its claims free wires holding the given values.
fn opening_rows(
    shape: StackShape,
    log_inv_rate: usize,
    slots: &[StackClaim],
    rings: &[RingSwitch],
    source: ProofSource<'_>,
) -> (Circuit, Vec<Unsatisfied>, bool) {
    let (b, (), finished) = replay(source, |r| {
        let root = r.t.next_root(r.b);
        let wire = |r: &mut Rows<'_, '_>, v: &F192| r.b.free_e(*v);
        let slot_wires: Vec<StackClaim<Ew>> = (slots.iter())
            .map(|claim| match claim {
                StackClaim::Point {
                    offset,
                    low_point,
                    value,
                } => StackClaim::Point {
                    offset: *offset,
                    low_point: low_point.iter().map(|v| wire(r, v)).collect(),
                    value: wire(r, value),
                },
                StackClaim::Strided {
                    offset,
                    slot,
                    stride_log,
                    point,
                    value,
                } => StackClaim::Strided {
                    offset: *offset,
                    slot: *slot,
                    stride_log: *stride_log,
                    point: point.iter().map(|v| wire(r, v)).collect(),
                    value: wire(r, value),
                },
            })
            .collect();
        let ring_wires = ring_wires(r, rings);
        let opening = Opening {
            slots: &slot_wires,
            rings: &ring_wires,
            shape,
            log_inv_rate,
        };
        opening.verify(r, root);
    });
    let done = b.finish();
    (done.circuit, done.failures, finished)
}

// Commit and open natively, verify natively, then replay the opening in rows, honest and with each claim tampered.
fn check_opening(mu: usize, log_inv_rate: usize, seed: u64) {
    let what = format!("mu {mu}, log_inv_rate {log_inv_rate}");
    let mut rng = Rng::new(seed);
    let shape = StackShape { mu, n_lanes: N_LANES };
    let q: Vec<F64> = (0..shape.committed_len()).map(|_| F64(rng.next_u64())).collect();
    let (slots, rings) = opening_claims(mu, &q, &mut rng);

    let mut ps = ProverState::from_label(LABEL);
    let committed = crate::pcs::commit(&mut ps, &q, shape, log_inv_rate);
    crate::pcs::open(&mut ps, &committed, &q, &slots, &rings);
    let proof = ps.into_proof();
    let mut vs = VerifierState::from_label(LABEL, &proof);
    let root = crate::pcs::read_commitment(&mut vs).expect("a root");
    crate::pcs::verify(&mut vs, &slots, &rings, shape, log_inv_rate, &root).expect("the native verifier accepts");
    vs.finish().expect("the native verifier reads the whole proof");
    let raw = vs.into_raw_proof();

    let rows = |slots: &[StackClaim], rings: &[RingSwitch], source: ProofSource<'_>| {
        opening_rows(shape, log_inv_rate, slots, rings, source)
    };
    let (circuit, failures, finished) = rows(&slots, &rings, ProofSource::Proof(&raw));
    assert!(failures.is_empty(), "{what}: {failures:?}");
    assert!(finished, "{what}: the rows left part of the proof unread");
    assert!(
        circuit == rows(&slots, &rings, ProofSource::Shape).0,
        "{what}: the shape builds another circuit"
    );

    let terminal = |failures: &[Unsatisfied]| failures.iter().any(|f| f.scope().iter().any(|s| s == "terminal"));
    for i in 0..slots.len() {
        let mut forged = slots.clone();
        match &mut forged[i] {
            StackClaim::Point { value, .. } | StackClaim::Strided { value, .. } => *value += F192::ONE,
        }
        let (_, failures, _) = rows(&forged, &rings, ProofSource::Proof(&raw));
        assert!(
            terminal(&failures),
            "{what}: a wrong value of point claim {i} passes: {failures:?}"
        );
    }
    for ring in 0..rings.len() {
        for claim in 0..rings[ring].claims.len() {
            let mut forged = rings.clone();
            forged[ring].claims[claim].s_hat_v[7] += F192::ONE;
            let (_, failures, _) = rows(&slots, &forged, ProofSource::Proof(&raw));
            assert!(
                terminal(&failures),
                "{what}: a wrong slice of ring {ring} claim {claim} passes: {failures:?}"
            );
        }
    }
    let mut forged = raw;
    let mid = forged.stream.len() / 2;
    forged.stream[mid].c1 ^= 1;
    assert!(
        !rows(&slots, &rings, ProofSource::Proof(&forged)).1.is_empty(),
        "{what}: a forged scalar passes"
    );
}

#[test]
fn the_smallest_opening_in_rows_is_the_native_one() {
    check_opening(crate::pcs::MIN_MU, 1, 1);
    check_opening(crate::pcs::MIN_MU, 2, 2);
}

#[test]
fn a_larger_opening_in_rows_is_the_native_one() {
    check_opening(20, 1, 3);
    check_opening(20, 2, 4);
}

// The family's share in rows is what the native verifier adds to the target and to the weight.
//
// Two more regions take claims at prefixes of the first claim's point, two at one length, on the same wires, as flock's circuits of one block size do.
#[test]
fn the_ring_family_in_rows_is_the_native_one() {
    let mut rng = Rng::new(9);
    let mu = 16;
    let q: Vec<F64> = (0..1 << mu).map(|_| F64(rng.next_u64())).collect();
    let (_, mut rings) = opening_claims(mu, &q, &mut rng);
    let lead = rings[0].claims[0].suffix_point.clone();
    let top = 1usize << mu;
    for (offset, vars, lengths) in [
        (top - (1 << (mu - 5)), mu - 5, &[mu - 5][..]),
        (top - (1 << (mu - 5)) - (1 << (mu - 6)), mu - 6, &[mu - 6, mu - 6][..]),
    ] {
        let claims = (lengths.iter())
            .map(|&len| {
                let suffix_point = lead[..len].to_vec();
                let s_hat_v = slices(&q[offset..offset + (1 << vars)], &suffix_point);
                SliceClaim { suffix_point, s_hat_v }
            })
            .collect();
        rings.push(RingSwitch {
            offset,
            qflock_vars: vars,
            claims,
        });
    }
    let gamma_rs = rng.ext();
    let map: [F192; 6] = std::array::from_fn(|_| rng.ext());
    let x = rng.ext_vec(mu);
    let family = RingFamily::new(gamma_rs, map);
    let target = family.target(
        rings
            .iter()
            .flat_map(|ring| ring.claims.iter().map(|c| c.s_hat_v.as_slice())),
    );
    let weight = family.weight(&rings, &x);

    let (b, (target_wire, weight_wire), _) = replay(ProofSource::Shape, |r| {
        // Claims at prefixes of the lead point hold its wires, so the rows see them as one point.
        let lead_wires: Vec<Ew> = lead.iter().map(|&v| r.b.free_e(v)).collect();
        let wires: Vec<RingSwitch<Ew>> = (rings.iter())
            .map(|ring| RingSwitch {
                offset: ring.offset,
                qflock_vars: ring.qflock_vars,
                claims: (ring.claims.iter())
                    .map(|claim| SliceClaim {
                        suffix_point: if lead.starts_with(&claim.suffix_point) {
                            lead_wires[..claim.suffix_point.len()].to_vec()
                        } else {
                            claim.suffix_point.iter().map(|&v| r.b.free_e(v)).collect()
                        },
                        s_hat_v: claim.s_hat_v.iter().map(|&v| r.b.free_e(v)).collect(),
                    })
                    .collect(),
            })
            .collect();
        let gamma = r.b.free_e(gamma_rs);
        let map: Vec<Ew> = map.iter().map(|&m| r.b.free_e(m)).collect();
        let x: Vec<Ew> = x.iter().map(|&v| r.b.free_e(v)).collect();
        let family = RingShare::new(r, &wires, gamma, &map);
        (family.target(r), family.weight_at(r, &x))
    });
    assert_eq!(b.e(target_wire), target);
    assert_eq!(b.e(weight_wire), weight);
}

// A recursion proof of a small circuit, as rows of another.
fn recursion_rows(
    circuit: &Circuit,
    statement: &[Limbs],
    columns: &FixedColumns,
    source: ProofSource<'_>,
) -> (Builder, RecRows) {
    let shape = RecShape::new(circuit.heights(), Rate::MIN).expect("a layout");
    let mut b = Builder::new();
    let iv = b.d_const(label_cv());
    let limbs: Vec<[Kw; 4]> = statement.iter().map(|w| w.map(|l| b.free_k(l))).collect();
    let rows = shape.verify(&mut b, iv, &limbs, columns, source);
    (b, rows)
}

// The rows hold on an honest proof, leave a hash matrix claim that settles and true fixed hints, and are the shape's rows.
#[test]
fn a_recursion_proof_in_rows_is_its_verifier() {
    let mut b = Builder::new();
    let x = b.free_e(F192::new(3, 5, 7));
    let y = b.e_const(F192::new(11, 13, 17));
    let mut acc = b.d_const([1, 2, 3, 4]);
    let observe = b.k_const(fiat_shamir::DS_OBSERVE.0);
    let mut e = x;
    for _ in 0..40 {
        e = b.mul_add(e, y, x);
        acc = b.compress(acc, e, observe).0;
    }
    let w = b.free_k(0xfeed);
    b.split(w);
    b.expose_d(acc);
    b.expose_e(e);
    let Finished {
        circuit,
        assignment: a,
        failures,
    } = b.finish();
    assert!(failures.is_empty(), "{failures:?}");
    let iv = label_cv().map(F64);
    let proof = circuit.prove(&a, iv, Rate::MIN).expect("the circuit fits");
    let raw = circuit
        .verify_to_raw(a.statement(), iv, Rate::MIN, &proof)
        .expect("an honest proof");
    let taus = circuit.heights();
    let columns = FixedColumns::of(&circuit, &taus);

    let (b, rows) = recursion_rows(&circuit, a.statement(), &columns, ProofSource::Proof(&raw));
    let form = rows.matrix.point.map(|w| b.e(w));
    let hash = HashFlock::FLOCK.circuit();
    assert_eq!(
        form.evaluate(hash),
        b.e(rows.matrix.value),
        "the hash rows' matrix claim settles"
    );
    for hint in &rows.hints {
        let point: Vec<F192> = hint.point.iter().map(|&w| b.e(w)).collect();
        let column = columns.get(hint.column);
        assert_eq!(b.e(hint.value), primitives::multilinear::mle_eval(column, &point));
    }
    let Finished {
        circuit: proven,
        failures,
        ..
    } = b.finish();
    assert!(failures.is_empty(), "{failures:?}");
    let zeros = FixedColumns::zeros(&taus);
    let (shaped, _) = recursion_rows(&circuit, a.statement(), &zeros, ProofSource::Shape);
    assert!(proven == shaped.finish().circuit, "the shape builds another circuit");

    // A tampered scalar, and a statement word the proof is not of.
    let mut forged = raw.clone();
    forged.stream[7].c1 ^= 1;
    let (b, _) = recursion_rows(&circuit, a.statement(), &columns, ProofSource::Proof(&forged));
    assert!(!b.finish().failures.is_empty(), "a forged scalar passes");
    let mut statement = a.statement().to_vec();
    statement[1][2] ^= 1;
    let (b, _) = recursion_rows(&circuit, &statement, &columns, ProofSource::Proof(&raw));
    assert!(!b.finish().failures.is_empty(), "another statement passes");
}
