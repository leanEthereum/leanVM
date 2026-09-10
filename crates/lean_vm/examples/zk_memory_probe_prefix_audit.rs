//! Native range checks with a public low-memory prefix and a relocated private frame.

use std::collections::HashMap;

use lean_vm::cpu::{DerefMode, MIN_LOG_MEM, Op, Program, hints::RHint, prove, verify};
use pcs::ntt::AdditiveNttF64;
use primitives::field::{F64, F192, g_pow};

const PROBE_PREFIX: usize = 1 << MIN_LOG_MEM;
const MASK_WORDS: usize = 1280;
const FRAME: u32 = (PROBE_PREFIX + MASK_WORDS) as u32;

fn program() -> Program {
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
    code.resize(32, Op::Set { o: 0, k: F192::ZERO });
    let hints = HashMap::from([
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
                    size: 44,
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
    encoder_certificate();
    let public_input = [F192::new(17, 19, 0), F192::new(29, 31, 0)];
    let mut program = program();
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
