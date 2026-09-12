//! Native range checks with a public low-memory prefix and a relocated private frame.

use std::collections::HashMap;

use lean_vm::cpu::{DerefMode, MIN_LOG_MEM, Op, Program, hints::RHint, prove, verify};
use pcs::ntt::AdditiveNttF64;
use primitives::field::{F64, F192, g_pow};

const PROBE_PREFIX: usize = 1 << MIN_LOG_MEM;
const MASK_WORDS: usize = 1280;
const FRAME: u32 = (PROBE_PREFIX + MASK_WORDS) as u32;

fn program(count_prefix: usize) -> Program {
    assert!(matches!(count_prefix, 0 | 128));
    let bound = F192::from(g_pow(PROBE_PREFIX - 1));
    let mut code = vec![
        Op::Set {
            o: FRAME + 16,
            k: F192::from(g_pow(3)),
        },
        Op::Set {
            o: FRAME + 17,
            k: F192::from(g_pow(FRAME as usize)),
        },
        Op::Jump {
            oc: FRAME + 16,
            od: FRAME + 16,
            of: FRAME + 17,
        },
        Op::Set { o: 2, k: bound },
        Op::Deref {
            o1: 0,
            o2: 0,
            o3: 3,
            mode: DerefMode::Cell,
        },
        Op::Mul { a: 0, b: 1, c: 2 },
        Op::Deref {
            o1: 1,
            o2: 0,
            o3: 4,
            mode: DerefMode::Cell,
        },
        Op::Set { o: 40, k: F192::ZERO },
        Op::Xor { a: 40, b: 40, c: 41 },
        Op::Blake2s {
            ins: [40; 4],
            cv: 40,
            out: 42,
            md: 40,
        },
        Op::Set { o: 2, k: bound },
        Op::Set { o: 2, k: bound },
        Op::Set {
            o: 20,
            k: F192::from(g_pow(31)),
        },
        Op::Set { o: 21, k: F192::ONE },
        Op::Jump { oc: 20, od: 20, of: 21 },
        Op::Set { o: 0, k: F192::ZERO },
    ];
    let compression = code[9];
    code.splice(10..10, [compression; 7]);
    let extra_derefs = (2 + count_prefix).next_power_of_two() - 2;
    code.splice(
        17..17,
        (0..count_prefix)
            .map(|index| Op::Deref {
                o1: 64 + index as u32,
                o2: 0,
                o3: 200 + index.min(2) as u32,
                mode: DerefMode::Cell,
            })
            .chain(std::iter::repeat_n(
                Op::Deref {
                    o1: 192,
                    o2: 0,
                    o3: 202,
                    mode: DerefMode::Cell,
                },
                extra_derefs - count_prefix,
            )),
    );
    let code_size = code.len().next_power_of_two();
    code[19 + extra_derefs] = Op::Set {
        o: 20,
        k: F192::from(g_pow(code_size - 1)),
    };
    code.resize(code_size, Op::Set { o: 0, k: F192::ZERO });
    let mut hints = HashMap::from([
        (
            0,
            vec![
                RHint::WitnessStack {
                    name: "masks".into(),
                    base: PROBE_PREFIX as u32,
                    len: MASK_WORDS as u32,
                },
                RHint::Alloc {
                    ptr: FRAME + 17,
                    size: if count_prefix == 0 { 44 } else { 203 },
                },
            ],
        ),
        (
            3,
            vec![RHint::WitnessStack {
                name: "exponent".into(),
                base: 0,
                len: 1,
            }],
        ),
    ]);
    if count_prefix != 0 {
        hints.insert(
            17,
            vec![
                RHint::WitnessStack {
                    name: "count_pointers".into(),
                    base: 64,
                    len: count_prefix as u32,
                },
                RHint::WitnessStack {
                    name: "public_values".into(),
                    base: 200,
                    len: 3,
                },
                RHint::WitnessStack {
                    name: "dummy_pointer".into(),
                    base: 192,
                    len: 1,
                },
            ],
        );
    }
    Program::assemble(code, hints, FRAME)
}

fn encoder_certificate() {
    let length = 1 << 17;
    let mut coefficients = vec![F64::ZERO; 2 * length];
    for (i, value) in coefficients[PROBE_PREFIX..PROBE_PREFIX + MASK_WORDS]
        .iter_mut()
        .enumerate()
    {
        *value = F64((i + 1) as u64);
    }
    coefficients[FRAME as usize + 30] = F64::ONE;
    AdditiveNttF64::standard((2 * length).ilog2() as usize).forward_transform_scalar(&mut coefficients);
    assert!(coefficients[..PROBE_PREFIX].iter().all(|value| *value == F64::ZERO));
    assert!(coefficients[PROBE_PREFIX..].iter().any(|value| *value != F64::ZERO));
    println!("Native NTT: all queries in the public-prefix subspace ignore the shifted masks and private tail.");
}

fn main() {
    assert_eq!(PROBE_PREFIX, 65536);
    lean_vm::init_prover_pool();
    match std::env::args().nth(1).as_deref() {
        None => {}
        #[cfg(feature = "zk-research")]
        Some("--count-prefix") => {
            count_prefix_audit();
            return;
        }
        _ => panic!("the optional --count-prefix mode requires --features zk-research"),
    }
    encoder_certificate();
    let public_input = [F192::new(17, 19, 0), F192::new(29, 31, 0)];
    let mut program = program(0);
    let mut shape = None;
    for exponent in [0, 1, 2, 1279, PROBE_PREFIX / 2, PROBE_PREFIX - 2, PROBE_PREFIX - 1] {
        let masks: Vec<_> = (0..MASK_WORDS)
            .map(|index| F192::new((index + exponent + 1) as u64, index as u64, 1))
            .collect();
        program.set_witness("masks", vec![masks.clone()]);
        program.set_witness("exponent", vec![vec![F192::from(g_pow(exponent))]]);
        let execution = program.execute(public_input);
        assert_eq!(execution.base_counts, [1, 1, 8, 2, 2, 8]);
        assert_eq!(execution.mem[..2], public_input);
        assert!(execution.mem[2..PROBE_PREFIX].iter().all(|value| *value == F192::ZERO));
        assert_eq!(execution.mem[PROBE_PREFIX..PROBE_PREFIX + MASK_WORDS], masks);
        assert_eq!(execution.mem[FRAME as usize + 3], execution.mem[exponent]);
        assert_eq!(
            execution.mem[FRAME as usize + 4],
            execution.mem[PROBE_PREFIX - 1 - exponent]
        );
        assert!(execution.unconstrained_reads.is_empty());
        if matches!(exponent, 0 | 1279) {
            let (proof, stats) = prove(&program, public_input, 1);
            verify(&program, &public_input, &proof).expect("native public-prefix range-check proof");
            let current = (stats.log_mem, stats.counts);
            if let Some(previous) = shape {
                assert_eq!(current, previous);
            }
            shape = Some(current);
            println!(
                "Complete native proof at exponent {exponent}, memory log {}, counts {:?}.",
                stats.log_mem, stats.counts
            );
        }
    }
    println!(
        "Seven valid exponents preserve the public prefix and unused masks; both public-input probe copies are exercised."
    );
    println!(
        "This is a native legality certificate, not a full ZK sampler or a privacy estimate for the Fiat-Shamir proofs."
    );
}

#[cfg(feature = "zk-research")]
fn count_openings(execution: &lean_vm::cpu::Execution, layout: &lean_vm::cpu::Layout) -> Vec<F64> {
    use fiat_shamir::merkle::PrunedMerklePaths;
    use pcs::whir;

    let log_lanes = whir::INITIAL_FOLDING_FACTOR;
    let lane_len = 1 << (layout.shape.mu - log_lanes);
    let position = layout.placements[3].offset;
    assert!(position.is_multiple_of(lane_len));
    let selected = position / lane_len;
    let lanes = layout.shape.n_lanes;
    let counts = &execution.memory_read_counts()[..lane_len];
    let mut scalar = counts.to_vec();
    scalar.resize(2 * lane_len, F64::ZERO);
    AdditiveNttF64::standard(scalar.len().ilog2() as usize).forward_transform_scalar(&mut scalar);
    let mut message = vec![F64::ZERO; lanes * lane_len];
    message[selected * lane_len..(selected + 1) * lane_len].copy_from_slice(counts);
    let (commitment, data) = whir::commit(&message, layout.shape.mu, log_lanes, 1);
    let queries: Vec<usize> = (0..128).collect();
    let paths = PrunedMerklePaths::prune(&data.merkle_tree, 2 * lane_len, &queries, |query| {
        data.codeword[query * lanes..(query + 1) * lanes].to_vec()
    });
    let raw = paths
        .open(&commitment.root, 2 * lane_len, &queries, lanes, 1 << log_lanes)
        .expect("authenticated count-lane openings");
    for (&query, path) in queries.iter().zip(raw) {
        assert_eq!(path.root(query), commitment.root);
        assert_eq!(path.leaf_data[(1 << log_lanes) - 1 - selected], scalar[query]);
    }
    assert_eq!(scalar[0], counts[0]);
    scalar[..128].to_vec()
}

#[cfg(feature = "zk-research")]
fn count_prefix_audit() {
    let public_input = [F192::new(17, 19, 0), F192::new(29, 31, 0)];
    let mut program = program(128);
    program.set_witness("dummy_pointer", vec![vec![F192::from(g_pow(FRAME as usize + 202))]]);
    program.set_witness(
        "public_values",
        vec![vec![public_input[0], public_input[1], F192::ZERO]],
    );
    let mut shape = None;
    let mut original = Vec::new();
    let mut repaired = None;
    for normalize in [false, true] {
        for exponent in [0, 1279] {
            let masks: Vec<_> = (0..MASK_WORDS)
                .map(|index| F192::new((index + exponent + 1) as u64, index as u64, 1))
                .collect();
            program.set_witness("masks", vec![masks.clone()]);
            program.set_witness("exponent", vec![vec![F192::from(g_pow(exponent))]]);
            let pointers = (0..128)
                .map(|index| {
                    let already_read = index == exponent || index == PROBE_PREFIX - 1 - exponent;
                    let address = if normalize && !already_read {
                        index
                    } else {
                        FRAME as usize + 200 + index.min(2)
                    };
                    F192::from(g_pow(address))
                })
                .collect();
            program.set_witness("count_pointers", vec![pointers]);
            let execution = program.execute(public_input);
            assert_eq!(execution.base_counts, [1, 1, 8, 256, 2, 8]);
            assert!(execution.unconstrained_reads.is_empty());
            assert_eq!(execution.mem[..2], public_input);
            assert!(execution.mem[2..PROBE_PREFIX].iter().all(|x| *x == F192::ZERO));
            assert_eq!(execution.mem[PROBE_PREFIX..PROBE_PREFIX + MASK_WORDS], masks);
            assert!(
                execution.memory_read_counts()[PROBE_PREFIX..PROBE_PREFIX + MASK_WORDS]
                    .iter()
                    .all(|x| *x == F64::ONE)
            );
            let expected = if normalize || exponent == 0 { g_pow(1) } else { F64::ONE };
            assert_eq!(execution.memory_read_counts()[0], expected);
            if normalize {
                assert!(execution.memory_read_counts()[..128].iter().all(|x| *x == g_pow(1)));
            }
            let (proof, stats) = prove(&program, public_input, 1);
            verify(&program, &public_input, &proof).expect("complete count-prefix native proof");
            let current = (stats.log_mem, stats.counts);
            if let Some(previous) = shape {
                assert_eq!(current, previous);
            }
            shape = Some(current);
            let layout = lean_vm::cpu::layout(
                &program.prog,
                stats.log_mem,
                stats.counts.map(|n| n.ilog2() as usize),
                public_input,
            );
            let values = count_openings(&execution, &layout);
            if normalize {
                if let Some(previous) = &repaired {
                    assert_eq!(&values, previous);
                }
                repaired = Some(values);
            } else {
                original.push(values[0]);
            }
            println!(
                "Count-prefix proof: normalize {normalize}, exponent {exponent}, memory log {}, stack log {}.",
                stats.log_mem, layout.shape.mu
            );
        }
    }
    assert_ne!(original[0], original[1]);
    println!("Public memory values alone leak through the authenticated count-lane query at zero.");
    println!(
        "Fixed-cost probe completion makes all 128 low-subspace count answers public while preserving unused value masks."
    );
    println!(
        "Separate forced encoder openings certify the projection; native Fiat-Shamir proofs use their ordinary queries."
    );
    println!("Other count/table/GKR disclosures and the full ZK sampler remain unproved.");
}
