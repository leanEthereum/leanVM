//! The stable prover and the experimental one, in every CPU tier this machine runs, give the same proof of the same
//! statement, byte for byte: three leaves (leanXMSS signatures and blobs, leanSPHINCS signatures, both schemes and
//! blobs, with enough signatures of each that experimental runs both signature loops as parallel segments), a recursion
//! node over them, at the four rates, and a second-level node over that node, a leaf and a raw signature; the same
//! refusal of a forged signature the native pre-check misses; and every compiler test program, or the same refusal.
//! Both trees' thread pools live in this one process, and libtest may run the two tests at once: both pools can then be
//! busy together, and either can take dispatches from both tests, which its dispatch lock serializes. Both executors
//! run the compiler's programs alike, and the experimental prover's proofs are the same bytes at every thread count.
//! `IDENTICAL_PROOFS_THREADS` sets both pools' thread count.

use aggregation::{AggregateClaims, AggregateError, AggregateProof, OutputClaims, signers_cache};
use experimental_dispatch::{__tiers_here, __with_tier, ExperimentalProver};
use isa::{Program, Prover};
use stable_lean_vm_core::StableProver;
use verifier::E;

/// The thread count this test binary proves at, the default if unset; each run of it by
/// [`experimental_proofs_are_identical_at_every_thread_count`] sets it.
const THREADS: &str = "IDENTICAL_PROOFS_THREADS";

/// Starts both trees' pools at [`THREADS`] threads, before any test uses either.
fn init() {
    let threads = std::env::var(THREADS).map_or(0, |t| t.parse().unwrap());
    StableProver::set_num_threads(threads);
    ExperimentalProver::set_num_threads(threads);
    StableProver::init();
    ExperimentalProver::init();
}

/// The proofs `P` gives, the three leaves', the node's and the second-level node's, then why it refuses a
/// forged signature.
fn proofs<P: Prover>() -> ([Vec<u8>; 5], Option<AggregateError>) {
    init();
    let aggregate = |children: &[(AggregateClaims, AggregateProof)], xmss, sphincs, blobs, rate| {
        aggregation::aggregate::<P>(children, xmss, sphincs, blobs, OutputClaims::All, rate).map(|(c, p, _)| (c, p))
    };
    let symbols: Vec<u128> = (0..2 * lean_da::BLOB_SYMBOLS as u128)
        .map(|i| i.wrapping_mul(0x9e37_79b9_7f4a_7c15))
        .collect();
    let blobs = lean_da::BlobMatrix::build(symbols.as_chunks().0).unwrap();
    let (xmss, sphincs) = (
        signers_cache::get_signers::<P>(23),
        signers_cache::get_lean_sphincs_signers::<P>(20),
    );
    let left = aggregate(&[], xmss[..3].to_vec(), vec![], Some(&blobs), 1).unwrap();
    let right = aggregate(&[], vec![], sphincs[..1].to_vec(), None, 2).unwrap();
    let mixed = aggregate(&[], xmss[3..22].to_vec(), sphincs[1..].to_vec(), Some(&blobs), 3).unwrap();
    let children = [left.clone(), right.clone(), mixed.clone()];
    let node = aggregate(&children, vec![], vec![], None, 4).unwrap();
    // The node's carried deferred claim is at a non-zero point, unlike a leaf's.
    let children = [node.clone(), right.clone()];
    let top = aggregate(&children, xmss[22..].to_vec(), vec![], None, 1).unwrap();
    // A leanXMSS signature with its top layer's last path node changed: the native pre-check passes, the guest fails.
    let (pk, message, signature) = &xmss[0];
    let mut bytes = signature.to_bytes();
    bytes[lean_xmss::SIG_SIZE - 1] ^= 1;
    let forged = vec![(*pk, *message, lean_xmss::LeanXmssSignature::from_bytes(&bytes))];
    let refusal = aggregate(&[], forged, vec![], None, 1).err();
    (
        [left, right, mixed, node, top].map(|(_, proof)| proof.to_bytes()),
        refusal,
    )
}

#[test]
fn stable_and_experimental_proofs_are_identical() {
    let (stable, stable_refusal) = proofs::<StableProver>();
    assert_eq!(stable_refusal, Some(AggregateError::ProvingFailed));
    for tier in __tiers_here() {
        let (experimental, experimental_refusal) = __with_tier(tier, proofs::<ExperimentalProver>);
        for (name, (e, s)) in ["left leaf", "right leaf", "mixed leaf", "node", "second-level node"]
            .iter()
            .zip(experimental.iter().zip(&stable))
        {
            let at = vm_proof(e)
                .zip(vm_proof(s))
                .and_then(|(e, s)| first_divergence(&e, &s, None));
            assert!(
                e == s,
                "{tier:?}: the {name}'s proofs differ ({} and {} bytes): {}",
                e.len(),
                s.len(),
                at.unwrap_or_else(|| "in the deferred point".into())
            );
        }
        assert_eq!(experimental_refusal, stable_refusal, "{tier:?}");
    }
}

/// `program`'s proof at rate `2^-log_inv_rate` on `public_input`, or why there is none.
fn prove<P: Prover>(
    program: &Program,
    public_input: [E; 2],
    witness: &[(String, Vec<Vec<E>>)],
    log_inv_rate: usize,
) -> Result<verifier::Proof, String> {
    init();
    P::prove(program, witness, public_input, log_inv_rate).map(|(proof, _)| proof)
}

/// Every compiler test program, compiled, with its annotated inputs (`# public_input:`, `# witness name:`).
fn compiler_programs() -> Vec<(std::path::PathBuf, Program, [E; 2], Witness)> {
    let dir = concat!(env!("CARGO_MANIFEST_DIR"), "/../crates/zkdsl_compiler/tests/programs");
    let mut paths: Vec<_> = std::fs::read_dir(dir)
        .unwrap()
        .map(|entry| entry.unwrap().path())
        .collect();
    paths.retain(|path| path.extension().is_some_and(|ext| ext == "py"));
    paths.sort();
    assert!(!paths.is_empty());
    let constants = |values: &str| -> Vec<E> {
        values
            .split(',')
            .map(|v| zkdsl_compiler::parse_const(v).unwrap())
            .collect()
    };
    paths
        .into_iter()
        .map(|path| {
            let src = std::fs::read_to_string(&path).unwrap();
            let program = Program::from(zkdsl_compiler::compile(&zkdsl_compiler::parse(&src).unwrap()));
            let annotation = |tag: &'static str| src.lines().filter_map(move |line| line.trim().strip_prefix(tag));
            let public_input = annotation("# public_input:")
                .next()
                .map_or([E::new(0, 0); 2], |v| constants(v).try_into().unwrap());
            // Each line is the next entry of its stream.
            let mut witness: Witness = Vec::new();
            for (name, values) in annotation("# witness ").map(|rest| rest.split_once(':').unwrap()) {
                match witness.iter_mut().find(|(stream, _)| stream == name.trim()) {
                    Some((_, entries)) => entries.push(constants(values)),
                    None => witness.push((name.trim().to_string(), vec![constants(values)])),
                }
            }
            (path, program, public_input, witness)
        })
        .collect()
}

/// A program's witness streams, each with its entries.
type Witness = Vec<(String, Vec<Vec<E>>)>;

/// The compiler suite runs on experimental alone; this runs its programs, with their annotated inputs (`# public_input:`,
/// `# witness name:`) and with a wrong public input, through experimental's interpreter and hints too, at every rate.
#[test]
fn compiler_programs_prove_identically() {
    for (path, program, public_input, witness) in compiler_programs() {
        let wrong = [public_input[0] + E::new(1, 0), public_input[1]];
        let runs = (1..=4).map(|rate| (public_input, rate)).chain([(wrong, 1)]);
        for (input, rate) in runs {
            let annotated = input == public_input;
            let stable = prove::<StableProver>(&program, input, &witness, rate);
            for tier in __tiers_here() {
                let experimental = __with_tier(tier, || prove::<ExperimentalProver>(&program, input, &witness, rate));
                let at = match (&experimental, &stable) {
                    (Ok(e), Ok(s)) => {
                        let summary = verifier::replay_unchecked(program.bytecode(), &statement(input), e).ok();
                        first_divergence(e, s, summary.as_ref())
                    }
                    _ => None,
                };
                assert!(
                    experimental == stable,
                    "{tier:?}: {} at rate {rate}: the provers disagree{}",
                    path.display(),
                    at.map_or(String::new(), |at| format!(", first {at}"))
                );
            }
            assert!(!annotated || stable.is_ok(), "{}: {:?}", path.display(), stable.err());
        }
    }
}

/// Both executors run a program to the same memory image, cycle count and used memory, or both fault alike: at the
/// same instruction, for the same reason.
fn assert_executions_agree(name: &str, program: &Program, public_input: [E; 2], witness: &[(String, Vec<Vec<E>>)]) {
    use experimental_lean_vm_core::cpu as experimental;
    use stable_lean_vm_core::cpu as stable;
    let stable_witness: Vec<_> = witness
        .iter()
        .map(|(n, es)| {
            (
                n.clone(),
                es.iter()
                    .map(|e| e.iter().map(|&x| stable::from_scalar(x)).collect())
                    .collect(),
            )
        })
        .collect();
    let experimental_witness: Vec<_> = witness
        .iter()
        .map(|(n, es)| {
            let entries = es
                .iter()
                .map(|e| e.iter().map(|&x| experimental::from_scalar(x)).collect());
            (n.clone(), entries.collect())
        })
        .collect();
    let s = stable::execute(program, &stable_witness, public_input.map(stable::from_scalar));
    let e = experimental::execute(
        program,
        &experimental_witness,
        public_input.map(experimental::from_scalar),
    );
    match (s, e) {
        (Ok(s), Ok(e)) => {
            assert_eq!(
                (s.cycles, s.mem_used, s.mem.len()),
                (e.cycles, e.mem_used, e.mem.len()),
                "{name}"
            );
            let differs = (0..s.mem.len())
                .find(|&i| stable::to_scalar(&s.mem.word(i)) != experimental::to_scalar(&e.mem.word(i)));
            assert_eq!(differs, None, "{name}: the memory images differ");
        }
        (Err(s), Err(e)) => {
            // The faults' payloads are each tree's own field types: compare their kinds.
            let kind = |debug: String| debug.split([' ', '{', '(']).next().unwrap().to_string();
            assert_eq!(
                (s.pc, s.site, kind(format!("{:?}", s.fault))),
                (e.pc, e.site, kind(format!("{:?}", e.fault))),
                "{name}: the executors fault differently"
            );
        }
        (s, e) => panic!("{name}: only one executor faults: {:?} {:?}", s.err(), e.err()),
    }
}

/// The two trees' executors agree on every compiler test program, and on loops that pop a stream and call a hashing
/// frame each iteration, which experimental runs as parallel segments.
#[test]
fn stable_and_experimental_executions_agree() {
    init();
    for (path, program, public_input, witness) in compiler_programs() {
        assert_executions_agree(&path.display().to_string(), &program, public_input, &witness);
    }
    for heap in [1usize, 3, 16] {
        let src = format!(
            r#"def f(v):
    h = StackBuf(13)
    keccak([v, v], [v, v], h)
    return h[0]

def main():
    for i in mul_range(1, GEN ** 60):
        w = StackBuf(1)
        hint_witness(w[0:1], "s")
        hb = HeapBuf({heap})
        hb[1] = w[0]
        x = f(hb[1])
        assert x == x
    return
"#
        );
        let program = Program::from(zkdsl_compiler::compile(&zkdsl_compiler::parse(&src).unwrap()));
        let witness = vec![("s".to_string(), (0..60).map(|k| vec![E::new(k + 3, 0)]).collect())];
        let merged = experimental_lean_vm_core::cpu::__segmented_loops().1;
        assert_executions_agree(
            &format!("loop with {heap} heap cells"),
            &program,
            [E::new(0, 0); 2],
            &witness,
        );
        // One thread runs no loop as segments.
        assert!(
            std::env::var(THREADS).is_ok_and(|t| t == "1")
                || experimental_lean_vm_core::cpu::__segmented_loops().1 > merged,
            "the loop with {heap} heap cells ran as merged segments"
        );
    }
}

/// A `DEREF` in pc or fp mode covers its third cell, which its row reads in every mode, as the Lean executor does:
/// with `o3` past every other cell, both executors announce a memory that holds it, and both provers prove the run.
#[test]
fn deref_covers_its_third_cell_in_every_mode() {
    use isa::{CompiledProgram, DerefMode, Op};
    for mode in [DerefMode::Pc, DerefMode::Fp] {
        let prog = vec![
            Op::Set {
                o: 2,
                k: E::new(isa::g_pow(5), 0),
            },
            Op::Deref {
                o1: 2,
                o2: 0,
                o3: 1000,
                mode,
            },
            Op::Set { o: 3, k: E::new(0, 0) },
            Op::Xor { a: 0, b: 0, c: 0 },
        ];
        let program = Program::from(CompiledProgram {
            prog,
            hints: Default::default(),
            main_frame: 8,
            fn_ranges: Vec::new(),
            src_lines: Vec::new(),
        });
        let public_input = [E::new(7, 0), E::new(11, 0)];
        let name = format!("DEREF in {mode:?} mode");
        init();
        assert_executions_agree(&name, &program, public_input, &[]);
        let stable_public_input = public_input.map(stable_lean_vm_core::cpu::from_scalar);
        let execution = stable_lean_vm_core::cpu::execute(&program, &[], stable_public_input).unwrap();
        assert_eq!(execution.mem.len(), 1024, "{name}");
        let stable = prove::<StableProver>(&program, public_input, &[], 1).unwrap();
        verifier::verify_execution(program.bytecode(), &statement(public_input), &stable).unwrap();
        for tier in __tiers_here() {
            let experimental = __with_tier(tier, || prove::<ExperimentalProver>(&program, public_input, &[], 1));
            assert!(
                experimental.as_ref() == Ok(&stable),
                "{tier:?}: {name}: the provers disagree"
            );
        }
    }
}

/// The experimental prover's proofs of two leaves (leanXMSS signatures and blobs; leanXMSS and leanSPHINCS signatures,
/// at another rate) and a node over them are the same bytes at every thread count. One pool per process: each count
/// runs in a child process of this binary.
#[test]
fn experimental_proofs_are_identical_at_every_thread_count() {
    proofs_are_identical_at_every_thread_count::<ExperimentalProver>(
        "experimental_proofs_are_identical_at_every_thread_count",
    );
}

/// [`experimental_proofs_are_identical_at_every_thread_count`] for the stable prover.
#[test]
fn stable_proofs_are_identical_at_every_thread_count() {
    proofs_are_identical_at_every_thread_count::<StableProver>("stable_proofs_are_identical_at_every_thread_count");
}

fn proofs_are_identical_at_every_thread_count<P: Prover>(name: &str) {
    if std::env::var(THREADS).is_ok() {
        init();
        let aggregate = |children: &[(AggregateClaims, AggregateProof)], xmss, sphincs, blobs, rate| {
            aggregation::aggregate::<P>(children, xmss, sphincs, blobs, OutputClaims::All, rate)
                .map(|(c, p, _)| (c, p))
                .unwrap()
        };
        let symbols: Vec<u128> = (0..2 * lean_da::BLOB_SYMBOLS as u128)
            .map(|i| i.wrapping_mul(0x9e37_79b9_7f4a_7c15))
            .collect();
        let blobs = lean_da::BlobMatrix::build(symbols.as_chunks().0).unwrap();
        let (xmss, sphincs) = (
            signers_cache::get_signers::<P>(5),
            signers_cache::get_lean_sphincs_signers::<P>(2),
        );
        let left = aggregate(&[], xmss[..3].to_vec(), vec![], Some(&blobs), 1);
        let right = aggregate(&[], xmss[3..].to_vec(), sphincs, None, 2);
        let node = aggregate(&[left.clone(), right.clone()], vec![], vec![], None, 1);
        // FNV-1a of every proof's bytes.
        let digest = [left, right, node]
            .iter()
            .flat_map(|(_, p)| p.to_bytes())
            .fold(0xcbf2_9ce4_8422_2325u64, |h, b| {
                (h ^ u64::from(b)).wrapping_mul(0x100_0000_01b3)
            });
        println!("{THREADS} {digest:016x}");
        return;
    }
    let digest = |threads: usize| {
        let out = std::process::Command::new(std::env::current_exe().unwrap())
            .args(["--exact", name, "--nocapture", "--test-threads=1"])
            .env(THREADS, threads.to_string())
            .output()
            .unwrap();
        let stdout = String::from_utf8_lossy(&out.stdout);
        // libtest prints the test's name on the same line.
        let printed = stdout
            .split(&format!("{THREADS} "))
            .nth(1)
            .and_then(|rest| rest.split_whitespace().next());
        printed
            .unwrap_or_else(|| panic!("{threads} threads: {stdout} {}", String::from_utf8_lossy(&out.stderr)))
            .to_string()
    };
    let one = digest(1);
    for threads in [2, 3, 4, 8, 13, 0] {
        assert_eq!(digest(threads), one, "{threads} threads and 1 give different proofs");
    }
}

/// The statement's 32 bytes, as the verifier takes them.
fn statement(public_input: [E; 2]) -> [u8; 32] {
    verifier::Digest::from_halves(public_input[0], public_input[1]).0
}

/// The VM proof inside an aggregate proof's bytes: past the deferred point, a count and two limbs an element.
fn vm_proof(bytes: &[u8]) -> Option<verifier::Proof> {
    let n = u64::from_le_bytes(bytes.get(..8)?.try_into().ok()?) as usize;
    verifier::Proof::from_bytes(bytes.get(8 + 16 * n..)?)
}

/// Where two proofs first differ, for a test that finds the provers disagree: the first stream scalar, with the stage
/// `summary` (one proof's, read unchecked) places it in, or the first Merkle opening.
fn first_divergence(a: &verifier::Proof, b: &verifier::Proof, summary: Option<&verifier::Summary>) -> Option<String> {
    if let Some(i) = (0..a.stream.len().min(b.stream.len())).find(|&i| a.stream[i] != b.stream[i]) {
        let stage = summary.map_or("", |s| {
            if i < s.values_at_r.start {
                " (the sizes, the commitment or the index side)"
            } else if s.values_at_r.contains(&i) {
                " (the memory term at r)"
            } else if i < s.bit_slices.start {
                " (the row side or the column values)"
            } else if s.bit_slices.contains(&i) {
                " (the pointer columns' bit-slices)"
            } else if i < s.keccak_scalars.start {
                " (before the Keccak reduction)"
            } else if s.keccak_scalars.contains(&i) {
                " (the Keccak reduction)"
            } else {
                " (the opening)"
            }
        });
        return Some(format!(
            "stream scalar {i} of {} and {}{stage}: {:?} and {:?}",
            a.stream.len(),
            b.stream.len(),
            a.stream[i],
            b.stream[i]
        ));
    }
    if a.stream.len() != b.stream.len() {
        return Some(format!("stream lengths {} and {}", a.stream.len(), b.stream.len()));
    }
    let phases = a.merkle_openings.iter().zip(&b.merkle_openings);
    if let Some((phase, (x, y))) = phases.enumerate().find(|(_, (x, y))| x != y) {
        let path = (0..x.len().min(y.len())).find(|&k| x[k] != y[k]);
        return Some(format!("Merkle phase {phase}, path {path:?}"));
    }
    (a.merkle_openings.len() != b.merkle_openings.len()).then(|| "the number of Merkle phases".into())
}

/// The two trees' row sides send the same round polynomials and end at the same values on the same tables: tables of
/// different heights (finished early, one of a single row, one with no executed row), padding rows, shift groups,
/// words that are not one-hot, gated and `eq`-weighed base blocks with products.
mod row_side {
    use experimental_lean_vm_core::link as xl;
    use experimental_primitives::field::{F64 as XK, F128 as XF};
    use stable_lean_vm_core::form::Form;
    use stable_lean_vm_core::link as sl;
    use stable_primitives::field::{F64 as SK, F128 as SF};

    /// SplitMix64.
    struct Rng(u64);

    impl Rng {
        fn next(&mut self) -> u64 {
            self.0 = self.0.wrapping_add(0x9e37_79b9_7f4a_7c15);
            let mut z = self.0;
            z = (z ^ (z >> 30)).wrapping_mul(0xbf58_476d_1ce4_e5b9);
            z = (z ^ (z >> 27)).wrapping_mul(0x94d0_49bb_1331_11eb);
            z ^ (z >> 31)
        }

        fn ext(&mut self) -> SF {
            SF::new(self.next(), self.next())
        }

        fn ext_vec(&mut self, n: usize) -> Vec<SF> {
            (0..n).map(|_| self.ext()).collect()
        }
    }

    fn x(v: SF) -> XF {
        XF { c0: v.c0, c1: v.c1 }
    }

    fn xs(v: &[SF]) -> Vec<XF> {
        v.iter().map(|&v| x(v)).collect()
    }

    fn sf(v: XF) -> SF {
        SF::new(v.c0, v.c1)
    }

    /// `JUMP`'s identities in experimental's column order, weighed by `pows`, with `constant` and some linear terms
    /// added: experimental's form and the same polynomial as a stable form.
    fn jump_form(rng: &mut Rng, constant: SF) -> (experimental_lean_vm_core::form::Form, Form) {
        let pows = rng.ext_vec(4);
        let mut ours = experimental_lean_vm_core::tables::tables()[4].constraint(&xs(&pows));
        ours.constant = x(constant);
        ours.coeffs[11] += x(rng.ext());
        ours.coeffs[12] += x(rng.ext());
        let mut form = Form::new(ours.coeffs.len());
        form.constant = constant;
        form.coeffs = ours.coeffs.iter().map(|&c| sf(c)).collect();
        // `(V_COND, W)`, `(V_COND, B)`, `(B, V_PC)`, `(B, PC)·g`, `(B, V_FP)`, `(B, FP)`.
        let g = stable_primitives::field::g_pow(1);
        form.prods = vec![
            (2, 7, pows[0]),
            (2, 8, pows[1]),
            (3, 8, pows[2]),
            (0, 8, pows[2].mul_base(g)),
            (4, 8, pows[3]),
            (1, 8, pows[3]),
        ];
        (ours, form)
    }

    struct Raw {
        log_rows: usize,
        rows: usize,
        explicit: usize,
        tau: Vec<SF>,
        omega: Vec<SF>,
        aux: Vec<Vec<SF>>,
        aux_tail: Vec<SF>,
        words: Vec<Vec<u64>>,
        /// Per pointer column: on `ω`, on `act`, the shift groups, the certificate per chunk.
        coefs: Vec<(sl::row::Coef, sl::row::Coef, Vec<sl::row::ShiftGroup>, Vec<SF>)>,
        k_columns: Vec<Vec<u64>>,
        blocks: Vec<(
            sl::base::Weight,
            Option<usize>,
            experimental_lean_vm_core::form::Form,
            Form,
        )>,
    }

    fn random_table(
        rng: &mut Rng,
        width: usize,
        max_shift: usize,
        (log_rows, rows, explicit): (usize, usize, usize),
    ) -> Raw {
        let chunks = sl::pointer::Chunks::new(width);
        let mask = (1usize << width) - 1;
        let mut words = Vec::new();
        let mut coefs = Vec::new();
        for c in 0..3 {
            let mut sigma = rng.next() as usize & mask;
            words.push(
                (0..1usize << log_rows)
                    .map(|u| {
                        if u >= explicit {
                            return 0;
                        }
                        if rng.next().is_multiple_of(3) {
                            sigma = (sigma + rng.next() as usize % 5) & mask;
                        }
                        if rng.next().is_multiple_of(7) {
                            sigma = (sigma | ((1 << chunks.widths[0]) - 2)) & mask;
                        }
                        let word = chunks.encode(sigma);
                        if rng.next().is_multiple_of(11) {
                            word ^ 1 << (rng.next() % 64)
                        } else {
                            word
                        }
                    })
                    .collect(),
            );
            let coef = |rng: &mut Rng, a: usize| sl::row::Coef {
                constant: rng.ext(),
                aux: (a < 2).then(|| (a, rng.ext())),
            };
            let shifts = match c {
                0 => vec![sl::row::ShiftGroup {
                    coef: coef(rng, 2),
                    weights: vec![(1, rng.ext())],
                }],
                1 => (0..2)
                    .map(|g| sl::row::ShiftGroup {
                        coef: coef(rng, 2 * g),
                        weights: (0..3)
                            .map(|_| (1 + rng.next() as usize % max_shift, rng.ext()))
                            .collect(),
                    })
                    .collect(),
                _ => Vec::new(),
            };
            let (omega, act) = match c {
                0 => (sl::row::Coef::ZERO, coef(rng, 0)),
                _ => (coef(rng, c), coef(rng, c - 1)),
            };
            coefs.push((omega, act, shifts, rng.ext_vec(chunks.d())));
        }
        let tau = rng.ext_vec(log_rows);
        let theta = rng.ext();
        let omega = stable_primitives::multilinear::eq_table(&tau)[..rows]
            .iter()
            .map(|&e| theta * e)
            .collect();
        let k_columns = (0..14)
            .map(|_| {
                (0..1usize << log_rows)
                    .map(|u| if u < explicit { rng.next() } else { 0 })
                    .collect()
            })
            .collect();
        let blocks = vec![
            (sl::base::Weight::Omega, None, rng.ext()),
            (sl::base::Weight::Omega, Some(7), rng.ext()),
            (sl::base::Weight::Eq, None, SF::ZERO),
        ]
        .into_iter()
        .map(|(w, g, constant)| {
            let (ours, form) = jump_form(rng, constant);
            (w, g, ours, form)
        })
        .collect();
        Raw {
            log_rows,
            rows,
            explicit,
            tau,
            omega,
            aux: (0..2).map(|_| rng.ext_vec(explicit)).collect(),
            aux_tail: rng.ext_vec(2),
            words,
            coefs,
            k_columns,
            blocks,
        }
    }

    fn stable_table<'a>(t: &'a Raw, k_columns: &'a [Vec<SK>], q: &mut usize) -> sl::row::RowTable<'a> {
        let blocks = (t.blocks.iter())
            .map(|(weight, gate, _, form)| sl::base::Block {
                weight: *weight,
                gate: *gate,
                form: form.clone(),
            })
            .collect();
        sl::row::RowTable {
            log_rows: t.log_rows,
            rows: t.rows,
            explicit: t.explicit,
            omega: t.omega.clone(),
            aux: t.aux.clone(),
            aux_tail: t.aux_tail.clone(),
            columns: (t.words.iter().zip(&t.coefs))
                .map(|(words, (omega, act, shifts, cert))| {
                    *q += 1;
                    sl::row::RowColumn {
                        words,
                        omega: *omega,
                        act: *act,
                        shifts: shifts.clone(),
                        cert: cert.clone(),
                        q: *q - 1,
                    }
                })
                .collect(),
            base: sl::base::Base::new(
                blocks,
                &k_columns.iter().map(Vec::as_slice).collect::<Vec<_>>(),
                &[SK::ZERO; 14],
                t.explicit,
                Some(stable_primitives::multilinear::eq_table(&t.tau)),
            ),
        }
    }

    fn experimental_table<'a>(
        t: &'a Raw,
        k_columns: &'a [Vec<XK>],
        chunks: &xl::pointer::Chunks,
        q: &mut usize,
    ) -> xl::row::RowTable<'a> {
        let coef = |c: sl::row::Coef| xl::row::Coef {
            constant: x(c.constant),
            aux: c.aux.map(|(a, s)| (a, x(s))),
        };
        let base = || {
            let blocks = (t.blocks.iter())
                .map(|(weight, gate, form, _)| xl::base::Block {
                    weight: match weight {
                        sl::base::Weight::Omega => xl::base::Weight::Omega,
                        sl::base::Weight::Eq => xl::base::Weight::Eq,
                    },
                    gate: *gate,
                    form: form.clone(),
                })
                .collect();
            xl::base::Base::new(
                blocks,
                k_columns.iter().map(Vec::as_slice).collect(),
                &[XK::ZERO; 14],
                Some(experimental_primitives::multilinear::eq_table(&xs(&t.tau))),
            )
        };
        let omega = xs(&t.omega);
        let base_first = base().omega_round(&omega, t.tau.first().map(|&v| x(v)));
        xl::row::RowTable {
            log_rows: t.log_rows,
            rows: t.rows,
            explicit: t.explicit,
            omega,
            tau: xs(&t.tau),
            aux: t.aux.iter().map(|a| xs(a)).collect(),
            aux_tail: xs(&t.aux_tail),
            columns: (t.words.iter().zip(&t.coefs))
                .map(|(words, (omega, act, shifts, cert))| {
                    *q += 1;
                    xl::row::RowColumn {
                        words,
                        index: chunks.decode_all(words),
                        omega: coef(*omega),
                        act: coef(*act),
                        shifts: (shifts.iter())
                            .map(|g| xl::row::ShiftGroup {
                                coef: coef(g.coef),
                                weights: g.weights.iter().map(|&(s, mu)| (s, x(mu))).collect(),
                            })
                            .collect(),
                        cert: xs(cert),
                        q: *q - 1,
                    }
                })
                .collect(),
            base: base(),
            base_first,
        }
    }

    /// Both row sides over the same random tables, each round's challenge drawn from the same stream: every round
    /// polynomial, the points, the claim and the tables' ends agree.
    pub fn compare(seed: u64, width: usize, max_shift: usize, shapes: &[(usize, usize, usize)]) {
        let mut rng = Rng(seed);
        let raw: Vec<Raw> = shapes
            .iter()
            .map(|&s| random_table(&mut rng, width, max_shift, s))
            .collect();
        let s_k: Vec<Vec<Vec<SK>>> = raw
            .iter()
            .map(|t| t.k_columns.iter().map(|c| c.iter().map(|&v| SK(v)).collect()).collect())
            .collect();
        let x_k: Vec<Vec<Vec<XK>>> = raw
            .iter()
            .map(|t| t.k_columns.iter().map(|c| c.iter().map(|&v| XK(v)).collect()).collect())
            .collect();
        let r = rng.ext_vec(width);
        let q_vars = (3 * raw.len()).next_power_of_two().trailing_zeros() as usize;
        let seed = rng.next();

        let s_chunks = sl::pointer::Chunks::new(width);
        let s_points = sl::row::RowPoints::new(&s_chunks, &r, max_shift);
        let mut q = 0;
        let tables = (raw.iter().zip(&s_k))
            .map(|(t, k)| stable_table(t, k, &mut q))
            .collect();
        let (mut polys, mut challenges) = (Vec::new(), Rng(seed));
        // The claim is the first round's sum, which the stable side only checks in debug builds.
        let mut claim = None;
        let end = sl::row::prove(&s_chunks, &s_points, tables, q_vars, SF::ZERO, &mut |poly| {
            claim.get_or_insert(poly[1..].iter().copied().sum::<SF>());
            polys.push(poly.iter().map(|v| (v.c0, v.c1)).collect::<Vec<_>>());
            challenges.ext()
        });
        let claim = claim.expect("a round");

        let x_chunks = xl::pointer::Chunks::new(width);
        let x_points = xl::row::RowPoints::new(&x_chunks, &xs(&r), max_shift);
        let mut q = 0;
        let tables = (raw.iter().zip(&x_k))
            .map(|(t, k)| experimental_table(t, k, &x_chunks, &mut q))
            .collect();
        let (mut x_polys, mut challenges) = (Vec::new(), Rng(seed));
        let x_end = xl::row::prove(&x_chunks, &x_points, tables, q_vars, x(claim), &mut |poly| {
            x_polys.push(poly.iter().map(|v| (v.c0, v.c1)).collect::<Vec<_>>());
            x(challenges.ext())
        });
        for (round, (a, b)) in polys.iter().zip(&x_polys).enumerate() {
            assert_eq!(a, b, "round {round}");
        }
        assert_eq!(polys.len(), x_polys.len());
        assert_eq!(xs(&end.point), x_end.point);
        assert_eq!(xs(&end.column_point), x_end.column_point);
        assert_eq!(x(end.claim), x_end.claim);
        for (a, b) in end.tables.iter().zip(&x_end.tables) {
            assert_eq!(
                (x(a.omega), x(a.act), xs(&a.aux), x(a.corner), x(a.base)),
                (b.omega, b.act, b.aux.clone(), b.corner, b.base)
            );
            for (a, b) in a.columns.iter().zip(&b.columns) {
                assert_eq!((xs(&a.slices), xs(&a.values)), (b.slices.clone(), b.values.clone()));
            }
        }
    }

    #[test]
    fn row_sides_send_the_same_round_polynomials() {
        super::init();
        compare(1, 7, 12, &[(3, 5, 6), (2, 4, 4)]);
        compare(2, 13, 3, &[(5, 19, 25), (6, 64, 64), (2, 1, 3), (0, 1, 1), (4, 0, 2)]);
        compare(
            3,
            22,
            12,
            &[(10, 1000, 1000), (12, 3000, 3002), (7, 100, 100), (3, 7, 8)],
        );
        compare(4, 24, 12, &[(9, 300, 320), (3, 7, 8)]);
        compare(5, 1, 1, &[(3, 6, 6), (1, 2, 2)]);
    }
}

/// Edge shapes: tables with no row or one row, the smallest programs, and the widest pointer. Each prover in each tier
/// gives the same verifying proof, or the same refusal.
mod edge {
    use super::*;

    fn src_program(src: &str) -> Program {
        Program::from(zkdsl_compiler::compile(&zkdsl_compiler::parse(src).unwrap()))
    }

    /// Proves `program` with stable and in every tier, checks the proofs are the same bytes and verify, and returns
    /// the stable run's table heights, or the shared refusal.
    fn check(
        name: &str,
        program: &Program,
        witness: &[(String, Vec<Vec<E>>)],
        rate: usize,
    ) -> Result<[usize; 6], String> {
        init();
        let input = [E::new(0, 0); 2];
        let stable = StableProver::prove(program, witness, input, rate);
        for tier in __tiers_here() {
            let experimental = __with_tier(tier, || ExperimentalProver::prove(program, witness, input, rate));
            match (&stable, &experimental) {
                (Ok((s, _)), Ok((e, _))) => assert!(s == e, "{tier:?}: {name} at rate {rate}: the proofs differ"),
                (Err(s), Err(e)) => assert_eq!(s, e, "{tier:?}: {name}: the refusals differ"),
                _ => panic!(
                    "{tier:?}: {name}: one prover refuses: {:?} {:?}",
                    stable.as_ref().err(),
                    experimental.as_ref().err()
                ),
            }
        }
        let (proof, stats) = stable?;
        verifier::verify_execution(program.bytecode(), &statement(input), &proof)
            .unwrap_or_else(|e| panic!("{name} at rate {rate}: {e:?}"));
        println!(
            "{name} rate {rate}: heights {:?} memory {} cycles {}",
            stats.table_heights, stats.memory_used, stats.cycles
        );
        Ok(stats.table_heights)
    }

    fn stream(name: &str, values: &[u64]) -> (String, Vec<Vec<E>>) {
        (name.to_string(), vec![values.iter().map(|&v| E::new(v, 0)).collect()])
    }

    #[test]
    fn tiny_and_single_row_programs_prove_identically() {
        println!("tiers here: {:?}", __tiers_here());
        let empty = src_program("def main():\n    return\n");
        for rate in 1..=4 {
            let h = check("empty main", &empty, &[], rate).unwrap();
            assert_eq!([h[0], h[1], h[3], h[5]], [0; 4], "no XOR, MUL, DEREF or KECCAK row");
        }
        // A rate no verifier takes.
        for rate in [0, 5] {
            assert!(check("empty main", &empty, &[], rate).is_err(), "rate {rate}");
        }
        // One XOR and one MUL, each asserting a hinted result.
        let arith = src_program(
            "def main():\n    w = StackBuf(4)\n    hint_witness(w[0:4], \"s\")\n    w[2] = w[0] * w[1]\n    w[3] = w[0] + w[1]\n    return\n",
        );
        let h = check("one XOR, one MUL", &arith, &[stream("s", &[3, 5, 15, 6])], 1).unwrap();
        println!("one XOR, one MUL: {h:?}");
        // A wrong product: both refuse alike.
        assert!(check("a wrong MUL", &arith, &[stream("s", &[3, 5, 14, 6])], 1).is_err());
        // One KECCAK.
        let keccak = src_program(
            "def main():\n    w = StackBuf(1)\n    hint_witness(w[0:1], \"s\")\n    v = w[0]\n    h = StackBuf(13)\n    keccak([v, v], [v, v], h)\n    return\n",
        );
        for rate in [1, 4] {
            let h = check("one KECCAK", &keccak, &[stream("s", &[9])], rate).unwrap();
            assert_eq!(h[5], 1, "one KECCAK row");
        }
        // Raw programs of a single instruction kind, and a one-instruction program.
        use isa::{CompiledProgram, Op};
        let raw = |prog: Vec<Op>| {
            Program::from(CompiledProgram {
                prog,
                hints: Default::default(),
                main_frame: 8,
                fn_ranges: Vec::new(),
                src_lines: Vec::new(),
            })
        };
        for (name, prog) in [
            ("one XOR", vec![Op::Xor { a: 0, b: 0, c: 0 }]),
            (
                "one SET then XOR",
                vec![Op::Set { o: 2, k: E::new(1, 0) }, Op::Xor { a: 0, b: 0, c: 0 }],
            ),
            ("one MUL", vec![Op::Mul { a: 0, b: 0, c: 0 }]),
        ] {
            let r = check(name, &raw(prog), &[], 1);
            println!("{name}: {r:?}");
        }
    }

    /// A memory of `2^24` cells takes the widest pointer a word holds; one of `2^25` takes a wider one, which both
    /// refuse alike.
    #[test]
    #[ignore]
    fn widest_pointer_proves_and_a_wider_one_is_refused() {
        let wide = |cells: usize| {
            src_program(&format!(
                "def main():\n    w = StackBuf(1)\n    hint_witness(w[0:1], \"s\")\n    buf = HeapBuf({cells})\n    buf[GEN ** {}] = w[0]\n    return\n",
                cells - 1
            ))
        };
        let h = check("2^24 cells", &wide((1 << 23) + 5), &[stream("s", &[7])], 1).unwrap();
        println!("2^24 cells: {h:?}");
        let refusal = check("2^25 cells", &wide((1 << 24) + 5), &[stream("s", &[7])], 1).unwrap_err();
        println!("2^25 cells: {refusal}");
    }
}
