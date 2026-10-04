use super::flock::Reduction;
use super::recursion::RecRows;
use super::ring::RingShare;
use super::whir::Opening;
use super::{ProofShape, RecShape, Rows};
use crate::class_flock;
use crate::cpu::{DeferredClaims, Program};
use crate::pcs::{Rate, RingSwitchClaim, RingSwitchOpen, SlotClaim};
use crate::rec::RecError;
use crate::rec::circuit::{Assignment, Builder, Circuit, Ew, Finished, Kw, Limbs};
use crate::rec::fixed::FixedColumns;
use crate::rec::table::HashFlock;
use crate::rec::transcript::{ProofSource, Transcript};
use crate::rv::asm::*;
use crate::tables::{ClassSpec, N_TABLES, Part};
use crate::witness::StackShape;
use ::flock::lincheck::MatrixForm;
use ::pcs::pack::PACKING_WIDTH;
use ::pcs::ring_switch::fold_1b_rows;
use ::pcs::stack_open::{RingFamily, RingSwitchVerify, RingSwitchVerifyClaim};
use ::pcs::whir::inner_product_base_ext;
use fiat_shamir::transcript::{Proof, ProverState, RawProof, VerifierState};
use primitives::field::{F64, F192};
use primitives::test_rng::Rng;

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
    Program::new(&text, crate::rv::Region::TEXT.base(), vec![3, 5], 2, 0).expect("a valid program")
}

// One honest proof of the small program, as the native verifier read it.
struct Fixture {
    program: Program,
    raw: RawProof,
    output: [u64; 4],
    taus: [usize; N_TABLES],
    native: DeferredClaims,
}

fn fixture() -> Fixture {
    let program = small_program();
    let (proof, output, _) = program.prove(&[], Rate::MIN).expect("the run halts");
    let native = program.verify_core(&output, &proof).expect("an honest proof");
    let raw = program.verify_to_raw(&output, &proof).expect("an honest proof");
    let taus = std::array::from_fn(|i| usize::try_from(proof.stream[i].c0).expect("a height"));
    Fixture {
        program,
        raw,
        output,
        taus,
        native,
    }
}

impl Fixture {
    // The core's rows over `source`: the builder, holding the wires' values, and the claims the core leaves.
    fn build(&self, source: ProofSource<'_>) -> (Builder, DeferredClaims<Ew>) {
        let shape = ProofShape::new(&self.program, self.taus, Rate::MIN).expect("an honest shape");
        let mut b = Builder::new();
        let output = self.output.map(|o| b.free_k(o));
        let core = shape.verify_core(&mut b, output, source);
        (b, core.claims)
    }

    // The checks a forged proof fails, in the order the rows meet them.
    fn failures(&self, raw: &RawProof) -> Vec<String> {
        self.build(ProofSource::Proof(raw)).0.finish().failures
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
    let verify = |proof: &Proof| circuit.verify(&statement, iv, Rate::MIN, proof);
    assert_eq!(verify(&prove(&a)), Ok(()));
    a.values[bit.0 as usize][0] = 2;
    assert_eq!(
        verify(&prove(&a)),
        Err(RecError::Constraint(crate::constraints::ConstraintError::FinalMismatch))
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

fn raw(proof: &Proof) -> RawProof {
    RawProof {
        stream: proof.stream.clone(),
        merkle: Vec::new(),
    }
}

// The reduction of packed witness `f` over `rows`, proven natively.
fn prove_reduction<const N: usize>(f: usize, rows: &[[u64; N]], n_blocks_log: usize) -> Proof {
    let circuit = class_flock::circuit(f);
    let (t, _) = class_flock::flock(f);
    let (z, a, bz, zl) = ClassSpec::ALL[t].witness.map_or_else(
        || circuit.generate_witness(rows, n_blocks_log),
        |witness| circuit.generate_witness_with(rows, &[0; N], n_blocks_log, |row, z, az, bz| witness(row, z, az, bz)),
    );
    let block = circuit.block();
    let mut ps = ProverState::from_label(LABEL);
    let stage = block.prove_zerocheck(n_blocks_log, &z, &a, &bz, &mut ps);
    block.prove_lincheck(n_blocks_log, stage, &zl, &mut ps);
    ps.into_proof()
}

// The reduction in rows agrees with the native replay, and a tampered scalar leaves a claim that does not settle.
fn check_reduction(f: usize, n_blocks_log: usize, proof: &Proof) {
    let shape = class_flock::shape(f);
    let native = |proof: &Proof| {
        let mut vs = VerifierState::from_label(LABEL, proof);
        class_flock::verify_reduction(f, n_blocks_log, &mut vs).expect("the replay runs")
    };
    let rows = |proof: &RawProof| replay(ProofSource::Proof(proof), |r| Reduction::replay(r, shape, n_blocks_log));

    let (replay_native, matrices) = native(proof);
    let (b, reduction, finished) = rows(&raw(proof));
    assert!(finished, "the rows read the whole stream");
    assert_eq!(
        reduction.slice.suffix_point.iter().map(|&w| b.e(w)).collect::<Vec<_>>(),
        replay_native.claim.suffix_point
    );
    assert_eq!(reduction.matrix.point.map(|w| b.e(w)), matrices.form);
    assert_eq!(b.e(reduction.matrix.value), matrices.value);
    let Finished { circuit, failures, .. } = b.finish();
    assert!(failures.is_empty(), "{failures:?}");
    let shaped: Circuit = replay(ProofSource::Shape, |r| Reduction::replay(r, shape, n_blocks_log))
        .0
        .finish()
        .circuit;
    assert!(circuit == shaped, "the shape builds another circuit");

    // The first scalar of the zerocheck's first round, and the last lincheck round's top coefficient.
    for index in [0, proof.stream.len() - PACKING_WIDTH - 1] {
        let mut forged = proof.clone();
        forged.stream[index] += F192::ONE;
        let (_, matrices) = native(&forged);
        let (b, reduction, _) = rows(&raw(&forged));
        let form: MatrixForm = reduction.matrix.point.map(|w| b.e(w));
        assert_eq!(
            form, matrices.form,
            "the rows replay the forged stream as the native verifier does"
        );
        assert_eq!(b.e(reduction.matrix.value), matrices.value);
        assert_ne!(
            form.evaluate(class_flock::circuit(f)),
            matrices.value,
            "the forged claim does not settle"
        );
    }
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

fn flock_index(name: &str, part: Part) -> usize {
    let t = ClassSpec::ALL.iter().position(|c| c.name == name).expect("a table");
    class_flock::flock_index(t, part)
}

#[test]
fn the_hash_reduction_in_rows_is_the_native_one() {
    let f = flock_index("HASH", Part::Class);
    let n_blocks_log = class_flock::n_blocks_log(ClassSpec::ALL[class_flock::flock(f).0], 5);
    let mut next = xorshift(0xA7);
    let rows: Vec<[u64; 14]> = (0..5).map(|_| std::array::from_fn(|_| next())).collect();
    check_reduction(f, n_blocks_log, &prove_reduction(f, &rows, n_blocks_log));
}

#[test]
fn a_small_reduction_in_rows_is_the_native_one() {
    let f = flock_index("LD", Part::Class);
    let n_blocks_log = class_flock::n_blocks_log(ClassSpec::ALL[class_flock::flock(f).0], 20);
    let mut next = xorshift(0x5EED);
    let rows: Vec<[u64; 2]> = (0..20).map(|_| [next(), next()]).collect();
    check_reduction(f, n_blocks_log, &prove_reduction(f, &rows, n_blocks_log));
}

// Fewer lanes than a leaf holds, and not whole blocks of them, so the level-0 image has a zero prefix.
const N_LANES: usize = 37;

// A region's claims, each a suffix point and its slices.
#[derive(Clone)]
struct Ring {
    offset: usize,
    qflock_vars: usize,
    claims: Vec<(Vec<F192>, Vec<F192>)>,
}

impl Ring {
    fn verify(&self) -> RingSwitchVerify<'_> {
        RingSwitchVerify {
            offset: self.offset,
            qflock_vars: self.qflock_vars,
            claims: (self.claims.iter())
                .map(|(suffix_point, s_hat_v)| RingSwitchVerifyClaim {
                    suffix_point,
                    s_hat_v: s_hat_v.as_slice().try_into().expect("64 slices"),
                })
                .collect(),
        }
    }
}

// Point and strided claims and two ring-switched regions on a stack of `N_LANES` lanes, their values read from `q`.
fn opening_claims(mu: usize, q: &[F64], rng: &mut Rng) -> (Vec<SlotClaim>, Vec<Ring>) {
    let lane = 1usize << (mu - crate::pcs::LOG_BATCH);
    let eq = primitives::multilinear::eq_table;
    let mut slots = Vec::new();
    for (offset, vars) in [(0, mu - 6), (2 * lane, mu - 5), (8, 3), (5, 0)] {
        let low_point = rng.ext_vec(vars);
        let value = inner_product_base_ext(&q[offset..offset + (1 << vars)], &eq(&low_point));
        slots.push(SlotClaim::Point {
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
        slots.push(SlotClaim::Strided {
            offset,
            slot,
            stride_log,
            point,
            value,
        });
    }
    let rings = [(4 * lane, mu - 4, 2), (16 * lane, mu - 5, 1)]
        .into_iter()
        .map(|(offset, qflock_vars, n_claims)| Ring {
            offset,
            qflock_vars,
            claims: (0..n_claims)
                .map(|_| {
                    let suffix_point = rng.ext_vec(qflock_vars);
                    let s_hat_v = fold_1b_rows(&q[offset..offset + (1 << qflock_vars)], &eq(&suffix_point));
                    (suffix_point, s_hat_v)
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
    slots: &[SlotClaim],
    rings: &[Ring],
    source: ProofSource<'_>,
) -> (Circuit, Vec<String>, bool) {
    let (b, (), finished) = replay(source, |r| {
        let root = r.t.next_root(r.b);
        let wire = |r: &mut Rows<'_, '_>, v: &F192| r.b.free_e(*v);
        let slot_wires: Vec<SlotClaim<Ew>> = (slots.iter())
            .map(|claim| match claim {
                SlotClaim::Point {
                    offset,
                    low_point,
                    value,
                } => SlotClaim::Point {
                    offset: *offset,
                    low_point: low_point.iter().map(|v| wire(r, v)).collect(),
                    value: wire(r, value),
                },
                SlotClaim::Strided {
                    offset,
                    slot,
                    stride_log,
                    point,
                    value,
                } => SlotClaim::Strided {
                    offset: *offset,
                    slot: *slot,
                    stride_log: *stride_log,
                    point: point.iter().map(|v| wire(r, v)).collect(),
                    value: wire(r, value),
                },
            })
            .collect();
        let claim_wires: Vec<Vec<(Vec<Ew>, Vec<Ew>)>> = (rings.iter())
            .map(|ring| {
                (ring.claims.iter())
                    .map(|(point, slices)| {
                        let point = point.iter().map(|v| wire(r, v)).collect();
                        (point, slices.iter().map(|v| wire(r, v)).collect())
                    })
                    .collect()
            })
            .collect();
        let ring_wires: Vec<RingSwitchVerify<'_, Ew>> = (rings.iter().zip(&claim_wires))
            .map(|(ring, claims)| RingSwitchVerify {
                offset: ring.offset,
                qflock_vars: ring.qflock_vars,
                claims: (claims.iter())
                    .map(|(suffix_point, s_hat_v)| RingSwitchVerifyClaim {
                        suffix_point,
                        s_hat_v: s_hat_v.as_slice().try_into().expect("64 slices"),
                    })
                    .collect(),
            })
            .collect();
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
    let opens: Vec<RingSwitchOpen> = (rings.iter())
        .map(|ring| RingSwitchOpen {
            offset: ring.offset,
            qflock_vars: ring.qflock_vars,
            claims: (ring.claims.iter())
                .map(|(suffix_point, s_hat_v)| RingSwitchClaim {
                    suffix_point: suffix_point.clone(),
                    s_hat_v: Some(s_hat_v.clone()),
                })
                .collect(),
        })
        .collect();
    crate::pcs::open(&mut ps, &committed, &q, &slots, &opens);
    let proof = ps.into_proof();
    let verifies: Vec<RingSwitchVerify<'_>> = rings.iter().map(Ring::verify).collect();
    let mut vs = VerifierState::from_label(LABEL, &proof);
    let root = crate::pcs::read_commitment(&mut vs).expect("a root");
    crate::pcs::verify(&mut vs, &slots, &verifies, shape, log_inv_rate, &root).expect("the native verifier accepts");
    vs.finish().expect("the native verifier reads the whole proof");
    let raw = vs.into_raw_proof();

    let rows = |slots: &[SlotClaim], rings: &[Ring], source: ProofSource<'_>| {
        opening_rows(shape, log_inv_rate, slots, rings, source)
    };
    let (circuit, failures, finished) = rows(&slots, &rings, ProofSource::Proof(&raw));
    assert!(failures.is_empty(), "{what}: {failures:?}");
    assert!(finished, "{what}: the rows left part of the proof unread");
    assert!(
        circuit == rows(&slots, &rings, ProofSource::Shape).0,
        "{what}: the shape builds another circuit"
    );

    let terminal = |failures: &[String]| failures.iter().any(|f| f.contains("terminal"));
    for i in 0..slots.len() {
        let mut forged = slots.clone();
        match &mut forged[i] {
            SlotClaim::Point { value, .. } | SlotClaim::Strided { value, .. } => *value += F192::ONE,
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
            forged[ring].claims[claim].1[7] += F192::ONE;
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
#[test]
fn the_ring_family_in_rows_is_the_native_one() {
    let mut rng = Rng::new(9);
    let mu = 16;
    let q: Vec<F64> = (0..1 << mu).map(|_| F64(rng.next_u64())).collect();
    let (_, rings) = opening_claims(mu, &q, &mut rng);
    let verifies: Vec<RingSwitchVerify<'_>> = rings.iter().map(Ring::verify).collect();
    let gamma_rs = rng.ext();
    let map: [F192; 6] = std::array::from_fn(|_| rng.ext());
    let x = rng.ext_vec(mu);
    let slices = verifies
        .iter()
        .flat_map(|ring| ring.claims.iter().map(|c| c.s_hat_v.as_slice()));
    let family = RingFamily::new(gamma_rs, map);
    let target = family.target(slices);
    let weight = family.weight(&verifies, &x);

    let (b, (target_wire, weight_wire), _) = replay(ProofSource::Shape, |r| {
        let claims: Vec<Vec<(Vec<Ew>, Vec<Ew>)>> = (rings.iter())
            .map(|ring| {
                (ring.claims.iter())
                    .map(|(p, s)| {
                        (
                            p.iter().map(|&v| r.b.free_e(v)).collect(),
                            s.iter().map(|&v| r.b.free_e(v)).collect(),
                        )
                    })
                    .collect()
            })
            .collect();
        let wires: Vec<RingSwitchVerify<'_, Ew>> = (rings.iter().zip(&claims))
            .map(|(ring, claims)| RingSwitchVerify {
                offset: ring.offset,
                qflock_vars: ring.qflock_vars,
                claims: (claims.iter())
                    .map(|(p, s)| RingSwitchVerifyClaim {
                        suffix_point: p,
                        s_hat_v: s.as_slice().try_into().expect("64 slices"),
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
    let hash = class_flock::circuit(HashFlock::index());
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
