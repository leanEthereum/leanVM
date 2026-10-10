use super::recursion::RecRows;
use super::{ProofShape, RecShape, Rows, infallible};
use crate::class_flock::FlockId;
use crate::constraints::ConstraintError;
use crate::cpu::{CpuError, DeferredClaims, Output, Program, ProvenRun, Prover, UNGROUND_LOG_BYTECODE};
use crate::leaf::BusError;
use crate::pcs::{Commitment, Committed, Rate, RingSwitch, SliceClaim, StackClaim};
use crate::rec::RecError;
use crate::rec::circuit::{Assignment, Builder, Circuit, Ew, Finished, Kw, Limbs, Unsatisfied};
use crate::rec::fixed::FixedColumns;
use crate::rec::table::HashFlock;
use crate::rec::transcript::{ProofSource, Transcript};
use crate::rv::Region;
use crate::rv::asm::*;
use crate::tables::{Fill, N_TABLES, PerTable, TableId};
use crate::witness::StackShape;
use fiat_shamir::{Encoding, FromNarg, ProofTranscript, ProverState, SessionId, TranscriptError, VerifierState};
use flock::FlockError;
use flock::Witness;
use flock::reduction::{self, Block, Instance, ReductionReplay, Shape};
use flock::zerocheck::K_SKIP;
use pcs::merkle::{Hash, hash_leaf, hash_pair};
use pcs::whir::{WhirError, inner_product_base_ext, strata};
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

// One honest proof of the small program.
struct Fixture {
    program: Program,
    proof: ProofTranscript,
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
        let taus = heights(&proof.0);
        Fixture {
            program,
            proof: proof.0,
            output,
            taus,
            native,
        }
    })
}

// The table heights a proof announces, its first messages.
fn heights(proof: &ProofTranscript) -> PerTable<usize> {
    PerTable::from_fn(|t: TableId| usize::try_from(scalar(proof, t.index()).c0).expect("a height"))
}

// Message `i` of a proof whose first `i + 1` messages are field elements.
fn scalar(proof: &ProofTranscript, i: usize) -> F192 {
    F192::from_narg(&mut &proof.narg[24 * i..]).expect("a message")
}

// Replace message `i` of a proof whose first `i + 1` messages are field elements.
fn set_scalar(proof: &mut ProofTranscript, i: usize, x: F192) {
    proof.narg[24 * i..24 * i + 24].copy_from_slice(&x.encode());
}

// Where each hint's bytes start and end, past its 4-byte length.
fn hints(proof: &ProofTranscript) -> Vec<std::ops::Range<usize>> {
    let mut ranges = Vec::new();
    let mut at = 0;
    while at < proof.hints.len() {
        let len = u32::from_le_bytes(proof.hints[at..at + 4].try_into().unwrap()) as usize;
        ranges.push(at + 4..at + 4 + len);
        at += 4 + len;
    }
    ranges
}

// The byte where the bus's first message starts: past the announcement, then the commitment's root.
const BUS_START: usize = 24 * (N_TABLES + 2) + 32;

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
    fn failures(&self, proof: &ProofTranscript) -> Vec<String> {
        let failures = self.build(ProofSource::Proof(proof)).0.finish().failures;
        failures.iter().map(Unsatisfied::to_string).collect()
    }
}

fn values(b: &Builder, claims: &DeferredClaims<Ew>) -> DeferredClaims {
    claims.map(|w| b.e(w))
}

#[test]
fn the_core_leaves_the_native_deferred_claims() {
    let f = fixture();
    let (b, claims) = f.build(ProofSource::Proof(&f.proof));
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
    let first = |proof: &ProofTranscript| f.failures(proof).into_iter().next().unwrap_or_default();

    // The GKR's root, the bus's first message: one bit of its second limb.
    let mut forged = f.proof.clone();
    forged.narg[BUS_START + 8] ^= 1;
    assert!(first(&forged).starts_with("bus and tables"), "{}", first(&forged));

    // A row word and a sibling of the first and the last opening: each hint is rows, then siblings.
    let ranges = hints(&f.proof);
    for range in [&ranges[0], &ranges[ranges.len() - 1]] {
        for byte in [range.start, range.end - 1] {
            let mut forged = f.proof.clone();
            forged.hints[byte] ^= 1;
            assert!(
                first(&forged).starts_with("opening / whir / rows"),
                "{}",
                first(&forged)
            );
        }
    }
}

// The level-0 batch: the largest group's first query feeds the shared subtree's bottom level, and the first query of
// the next group reaches a node inside it. A wrong sibling right under either node breaks the tie to the subtree.
#[test]
fn a_wrong_sibling_under_the_shared_subtree_is_refused() {
    // Fixture: a tree of 2^6 one-block leaves, and 21 queries in their strata.
    let (depth, count) = (6, 21);
    let leaves: Vec<Hash> = (0..1u64 << depth)
        .map(|i| hash_leaf(&(0..8).flat_map(|j| (8 * i + j).to_le_bytes()).collect::<Vec<u8>>()))
        .collect();
    let mut levels = vec![leaves];
    while levels.last().unwrap().len() > 1 {
        let level = levels.last().unwrap();
        levels.push(level.chunks(2).map(|pair| hash_pair(&pair[0], &pair[1])).collect());
    }
    let root = levels.last().unwrap()[0];
    let strata = strata(count, depth);
    let mut rng = Rng::new(9);
    let queries: Vec<usize> = (strata.iter())
        .map(|s| {
            let low = depth - s.bits;
            (rng.next_u64() as usize & ((1 << low) - 1)) | s.index << low
        })
        .collect();

    // Each query's honest full path, and the rows hashing them.
    let path = |q: usize| -> Vec<Hash> { (0..depth).map(|l| levels[l][(q >> l) ^ 1]).collect() };
    let failures = |forge: Option<usize>| {
        let mut b = Builder::new();
        let instance = [b.k_const(0)];
        let mut t = Transcript::new(&mut b, &SessionId::new(LABEL), &instance, ProofSource::Shape);
        for (i, &q) in queries.iter().enumerate() {
            let mut path = path(q);
            if forge == Some(i) {
                path[depth - strata[i].bits - 1][0] ^= 1;
            }
            t.queue_opening((0..8).map(|j| 8 * q as u64 + j).collect(), &path);
        }
        let bits: Vec<Vec<Kw>> = (queries.iter())
            .map(|&q| (0..depth).map(|l| b.k_const((q >> l) as u64 & 1)).collect())
            .collect();
        let root = b.d_const(primitives::hash::digest_words(&root));
        super::authenticate_queued(&mut Rows::new(&mut b, &mut t), root, &bits, 8, 8);
        b.finish().failures
    };
    assert!(failures(None).is_empty(), "the honest paths tie to the root");

    // The largest group's first query, and the first query of a group with fixed bits inside the subtree.
    let inner = strata.iter().position(|s| s.bits < strata[0].bits && s.bits > 0);
    let inner = inner.expect("the batch has a second group with fixed bits");
    for q in [0, inner] {
        assert!(!failures(Some(q)).is_empty(), "query {q}");
    }
}

#[test]
fn a_forged_announcement_is_refused_first() {
    let f = fixture();
    let clock = N_TABLES + 1;
    let ts = scalar(&f.proof, clock);
    let forge = |edit: &dyn Fn(&mut ProofTranscript)| {
        let mut forged = f.proof.clone();
        edit(&mut forged);
        f.failures(&forged).into_iter().next().unwrap_or_default()
    };
    for t in 0..N_TABLES {
        let failure = forge(&|p| set_scalar(p, t, F192::new(scalar(p, t).c0 + 1, 0, 0)));
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
        let failure = forge(&|p| set_scalar(p, at, value));
        assert!(failure.starts_with("announcement"), "{what}: {failure}");
    }
    // A live clock at slot zero passes the announcement, and the bus refuses the wrong one.
    let failure = forge(&|p| set_scalar(p, clock, F192::new(ts.c0 + 32, 0, 0)));
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
        taus: heights(&proof.0),
        proof: proof.0.clone(),
        program,
        output,
    };

    // The rows leave the native claims, and the shape builds the same circuit.
    let (b, claims) = f.build(ProofSource::Proof(&f.proof));
    assert_eq!(values(&b, &claims), f.native);
    let Finished { circuit, failures, .. } = b.finish();
    assert!(failures.is_empty(), "{failures:?}");
    assert!(circuit == f.build(ProofSource::Shape).0.finish().circuit);

    // The nonce is the bus's first message: one the native verifier refuses for missing the work fails at the bus.
    let missed = CpuError::Bus(BusError::Transcript(TranscriptError::PowFailed { bits: 1 }));
    let forged = (1..64)
        .map(|step| {
            let mut forged = proof.clone();
            forged.0.narg[BUS_START] ^= step;
            forged
        })
        .find(|forged| f.program.verify_core(f.output, forged).err() == Some(missed.clone()))
        .expect("half the nonces miss one bit of work");
    let failure = f.failures(&forged.0).into_iter().next().unwrap_or_default();
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
    let session = SessionId::new(b"selector-test");
    let statement = a.statement().to_vec();
    let prove = |a: &Assignment| circuit.prove(a, &session, Rate::MIN).expect("the circuit fits");
    let verify = |proof: &ProofTranscript| circuit.verify(&statement, &session, Rate::MIN, proof);
    assert_eq!(verify(&prove(&a)), Ok(()));
    a.values[bit.0 as usize][0] = 2;
    assert_eq!(
        verify(&prove(&a)),
        Err(RecError::Constraint(ConstraintError::FinalMismatch))
    );
}

const LABEL: &[u8] = b"rec-verifier-test";

// A rows transcript from the test label over `source`, and what `f` builds on it.
fn replay<T>(source: ProofSource<'_>, f: impl FnOnce(&mut Rows<'_, '_>) -> T) -> (Builder, T, bool) {
    let mut b = Builder::new();
    let instance = [b.k_const(0)];
    let mut t = Transcript::new(&mut b, &SessionId::new(LABEL), &instance, source);
    let out = f(&mut Rows::new(&mut b, &mut t));
    let finished = t.finished();
    (b, out, finished)
}

// Packed witness `f`'s batch over `rows`, as the prover holds it.
struct Batch {
    block: Block<'static>,
    n_blocks_log: usize,
    witness: Witness,
}

fn batch<const N: usize>(f: FlockId, rows: &[[u64; N]]) -> Batch {
    let (circuit, spec) = (f.circuit(), f.table().spec());
    let n_blocks_log = spec.n_blocks_log(rows.len());
    let witness = match spec.circuit.as_ref().map(|c| c.fill) {
        Some(Fill::Instance(instance)) => {
            circuit.witness_by_instance(rows, &[0; N], n_blocks_log, |row, z, az, bz| instance(row, z, az, bz))
        }
        _ => circuit.witness_by_walk(rows, &[0; N], n_blocks_log, |row, words| words.copy_from_slice(row)),
    };
    Batch {
        block: circuit.block(),
        n_blocks_log,
        witness,
    }
}

// The reduction's matrix claims settle, its rows read the whole proof and are the shape's, and a tampered scalar fails both verifiers at one stage.
fn check_reductions(batches: &[Batch]) {
    let proof = {
        let instances: Vec<Instance<'_>> = (batches.iter())
            .map(|batch| Instance::of(batch.block, batch.n_blocks_log, &batch.witness))
            .collect();
        let mut ps = ProverState::new(&SessionId::new(LABEL), &0u64);
        reduction::prove(&instances, &mut ps);
        ps.into_proof()
    };
    let circuits: Vec<(Shape, usize)> = (batches.iter())
        .map(|batch| (batch.block.shape(), batch.n_blocks_log))
        .collect();
    let native = |proof: &ProofTranscript| {
        let mut vs = VerifierState::new(&SessionId::new(LABEL), &0u64, proof);
        reduction::verify(&circuits, &mut vs)
    };
    let rows = |source: ProofSource<'_>| replay(source, |r| infallible(reduction::verify(&circuits, r)));

    let replays = native(&proof).expect("an honest batch");
    for (batch, replay) in batches.iter().zip(&replays) {
        assert_eq!(
            replay.matrices.form.evaluate(batch.block.circuit),
            replay.matrices.value
        );
    }
    let (b, _, finished) = rows(ProofSource::Proof(&proof));
    assert!(finished, "the rows read the whole proof");
    let Finished { circuit, failures, .. } = b.finish();
    assert!(failures.is_empty(), "{failures:?}");
    assert!(
        circuit == rows(ProofSource::Shape).0.finish().circuit,
        "the shape builds another circuit"
    );

    // The first scalar of the zerocheck's first round, the last circuit's `c` claim, the last lincheck round's top
    // coefficient, the first circuit's first slice and its form's value.
    let n = batches.len();
    let tail = n * (F64::DEGREE + 1);
    let n_rounds = (circuits.iter())
        .map(|(shape, _)| shape.k_log - K_SKIP)
        .max()
        .unwrap_or(0);
    let lincheck_start = proof.narg.len() / 24 - tail - 2 * n_rounds;
    let len = proof.narg.len() / 24;
    let tampers = [
        (0, "zerocheck"),
        (lincheck_start - 1, "zerocheck"),
        (len - tail - 1, "lincheck"),
        (len - tail, "lincheck"),
        (len - tail + F64::DEGREE, "lincheck"),
    ];
    for (index, stage) in tampers {
        let mut forged = proof.clone();
        forged.narg[24 * index] ^= 1;
        let refused = match native(&forged) {
            Err(FlockError::Zerocheck(_)) => "zerocheck",
            Err(FlockError::Lincheck(_)) => "lincheck",
            Ok(_) => "",
        };
        assert_eq!(refused, stage, "the native verifier refuses scalar {index}");
        let failures = rows(ProofSource::Proof(&forged)).0.finish().failures;
        assert!(
            failures.first().is_some_and(|f| f.scope()[0] == stage),
            "scalar {index}: {failures:?}"
        );
    }

    // A value moved between two circuits' forms keeps the batch's identity: the reduction accepts, and the claims do not settle.
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
        let (a, b) = (len - tail + F64::DEGREE, len - tail + 2 * F64::DEGREE + 1);
        let (moved_a, moved_b) = (
            scalar(&forged, a) + delta * lifts[1],
            scalar(&forged, b) + delta * lifts[0],
        );
        set_scalar(&mut forged, a, moved_a);
        set_scalar(&mut forged, b, moved_b);
        let moved = native(&forged).expect("the batch's identity holds");
        for (f, replay) in moved.iter().enumerate() {
            let matrices = &replay.matrices;
            let settles = matrices.form.evaluate(batches[f].block.circuit) == matrices.value;
            assert_eq!(settles, f > 1, "circuit {f}'s moved claim");
        }
    }
}

fn hash_batch(seed: u64) -> Batch {
    let mut rng = Rng::new(seed);
    let rows: Vec<[u64; 14]> = (0..5).map(|_| std::array::from_fn(|_| rng.next_u64())).collect();
    batch(HashFlock::FLOCK, &rows)
}

fn ld_batch(seed: u64, n: usize) -> Batch {
    let mut rng = Rng::new(seed);
    let rows: Vec<[u64; 2]> = (0..n).map(|_| [rng.next_u64(), rng.next_u64()]).collect();
    batch(FlockId::class(TableId::LD).unwrap(), &rows)
}

#[test]
fn the_hash_reduction_holds_in_both_verifiers() {
    check_reductions(&[hash_batch(0xA7)]);
}

// Two block sizes, and two batches of one circuit at different heights, so the claims sit at prefixes of one another.
#[test]
fn a_mixed_batch_holds_in_both_verifiers() {
    check_reductions(&[ld_batch(0x5EED, 20), hash_batch(0xA7), ld_batch(0xB0B, 300)]);
}

// Fewer lanes than a leaf holds, and not whole blocks of them, so the level-0 image has a zero prefix.
const N_LANES: usize = 37;

// The 64 bit slices of the packed words `q` at `point`.
fn slices(q: &[F64], point: &[F192]) -> Vec<F192> {
    let eq = primitives::multilinear::eq_table(point);
    (0..F64::DEGREE)
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
    rate: Rate,
    slots: &[StackClaim],
    rings: &[RingSwitch],
    source: ProofSource<'_>,
) -> (Circuit, Vec<Unsatisfied>, bool) {
    let (b, (), finished) = replay(source, |r| {
        let commitment = infallible(Commitment::read(r, shape, rate));
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
        infallible(commitment.verify(r, &slot_wires, &ring_wires));
    });
    let done = b.finish();
    (done.circuit, done.failures, finished)
}

// Commit and open, then verify natively and in rows: an honest opening holds in both, and a tampered claim fails both at the terminal check.
fn check_opening(mu: usize, log_inv_rate: u8, seed: u64) {
    let what = format!("mu {mu}, log_inv_rate {log_inv_rate}");
    let rate = Rate::new(log_inv_rate).expect("a supported rate");
    let mut rng = Rng::new(seed);
    let shape = StackShape { mu, n_lanes: N_LANES };
    let q: Vec<F64> = (0..shape.committed_len()).map(|_| F64(rng.next_u64())).collect();
    let (slots, rings) = opening_claims(mu, &q, &mut rng);

    let mut ps = ProverState::new(&SessionId::new(LABEL), &0u64);
    let committed = Committed::new(&mut ps, &q, shape, rate).expect("a supported witness");
    committed
        .open(&mut ps, &q, &slots, &rings)
        .expect("the committed witness");
    let proof = ps.into_proof();
    let native = |slots: &[StackClaim], rings: &[RingSwitch], proof: &ProofTranscript| {
        let mut vs = VerifierState::new(&SessionId::new(LABEL), &0u64, proof);
        let commitment = Commitment::read(&mut vs, shape, rate).expect("a root");
        commitment.verify(&mut vs, slots, rings)?;
        vs.check_eof().expect("the native verifier reads the whole proof");
        Ok::<_, WhirError>(())
    };
    native(&slots, &rings, &proof).expect("the native verifier accepts");

    let rows = |slots: &[StackClaim], rings: &[RingSwitch], source: ProofSource<'_>| {
        opening_rows(shape, rate, slots, rings, source)
    };
    let (circuit, failures, finished) = rows(&slots, &rings, ProofSource::Proof(&proof));
    assert!(failures.is_empty(), "{what}: {failures:?}");
    assert!(finished, "{what}: the rows left part of the proof unread");
    assert!(
        circuit == rows(&slots, &rings, ProofSource::Shape).0,
        "{what}: the shape builds another circuit"
    );

    let terminal = |failures: &[Unsatisfied]| failures.iter().any(|f| f.scope().iter().any(|s| s == "terminal"));
    let refused = |slots: &[StackClaim], rings: &[RingSwitch]| {
        native(slots, rings, &proof).err() == Some(WhirError::TerminalMismatch)
            && terminal(&rows(slots, rings, ProofSource::Proof(&proof)).1)
    };
    for i in 0..slots.len() {
        let mut forged = slots.clone();
        match &mut forged[i] {
            StackClaim::Point { value, .. } | StackClaim::Strided { value, .. } => *value += F192::ONE,
        }
        assert!(
            refused(&forged, &rings),
            "{what}: a wrong value of point claim {i} passes"
        );
    }
    for ring in 0..rings.len() {
        for claim in 0..rings[ring].claims.len() {
            let mut forged = rings.clone();
            forged[ring].claims[claim].s_hat_v[7] += F192::ONE;
            assert!(
                refused(&slots, &forged),
                "{what}: a wrong slice of ring {ring} claim {claim} passes"
            );
        }
    }
    let mut forged = proof.clone();
    let mid = forged.narg.len() / 2;
    forged.narg[mid] ^= 1;
    assert!(
        !rows(&slots, &rings, ProofSource::Proof(&forged)).1.is_empty(),
        "{what}: a forged scalar passes"
    );
}

#[test]
fn the_smallest_opening_holds_in_both_verifiers() {
    check_opening(crate::pcs::MIN_MU, 1, 1);
    check_opening(crate::pcs::MIN_MU, 2, 2);
}

#[test]
fn a_larger_opening_holds_in_both_verifiers() {
    check_opening(20, 1, 3);
    check_opening(20, 2, 4);
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
    let limbs: Vec<[Kw; 4]> = statement.iter().map(|w| w.map(|l| b.free_k(l))).collect();
    let rows = shape.verify(&mut b, &SessionId::new(LABEL), &limbs, columns, source);
    (b, rows)
}

// The rows hold on an honest proof, leave a hash matrix claim that settles and true fixed hints, and are the shape's rows.
#[test]
fn a_recursion_proof_in_rows_is_its_verifier() {
    let mut b = Builder::new();
    let x = b.free_e(F192::new(3, 5, 7));
    let y = b.e_const(F192::new(11, 13, 17));
    let mut acc = b.d_const([1, 2, 3, 4]);
    let observe = b.k_const(1);
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
    let session = SessionId::new(LABEL);
    let proof = circuit.prove(&a, &session, Rate::MIN).expect("the circuit fits");
    circuit
        .verify(a.statement(), &session, Rate::MIN, &proof)
        .expect("an honest proof");
    let taus = circuit.heights();
    let columns = FixedColumns::of(&circuit, &taus);

    let (b, rows) = recursion_rows(&circuit, a.statement(), &columns, ProofSource::Proof(&proof));
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
    let mut forged = proof.clone();
    forged.narg[24 * 7 + 8] ^= 1;
    let (b, _) = recursion_rows(&circuit, a.statement(), &columns, ProofSource::Proof(&forged));
    assert!(!b.finish().failures.is_empty(), "a forged scalar passes");
    let mut statement = a.statement().to_vec();
    statement[1][2] ^= 1;
    let (b, _) = recursion_rows(&circuit, &statement, &columns, ProofSource::Proof(&proof));
    assert!(!b.finish().failures.is_empty(), "another statement passes");
}
