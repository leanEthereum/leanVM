//! Valid frame-alias witnesses and the native two-query cancellation identity.

use std::collections::HashMap;

use fiat_shamir::merkle::PrunedMerklePaths;
use lean_vm::{
    cpu::{DerefMode, Op, Program, hints::RHint, layout, prove, verify},
    hash_flock::IV_CELLS,
};
use pcs::{ntt::AdditiveNttF64, whir};
use primitives::field::{F64, F192, g_pow};

const FRAME: u32 = 1280;

fn program() -> (Program, u32) {
    let mut code = vec![Op::Jump { oc: 0, od: 0, of: 1 }];
    for offset in 24..31 {
        code.push(Op::Set {
            o: offset,
            k: F192::ZERO,
        });
    }
    code.extend([
        Op::Set {
            o: 31,
            k: F192::from(g_pow(FRAME as usize)),
        },
        Op::Xor { a: 0, b: 0, c: 4 },
        Op::Mul { a: 0, b: 0, c: 5 },
        Op::Deref {
            o1: 31,
            o2: 0,
            o3: 7,
            mode: DerefMode::Cell,
        },
        Op::Jump { oc: 0, od: 0, of: 0 },
    ]);
    let compression = Op::Blake2s {
        ins: [0, 1, 2, 3],
        cv: 8,
        out: 10,
        md: 12,
    };
    code.extend(std::iter::repeat_n(compression, 4));
    code.push(Op::Jump { oc: 16, od: 17, of: 18 });
    let second = code.len() as u32;
    code.extend(std::iter::repeat_n(compression, 4));
    code.push(Op::Jump { oc: 20, od: 21, of: 22 });
    code.resize(64, Op::Set { o: 24, k: F192::ZERO });
    let hints = [1, second]
        .into_iter()
        .map(|pc| {
            (
                pc,
                vec![
                    RHint::WitnessStack {
                        name: "data".into(),
                        base: 0,
                        len: 10,
                    },
                    RHint::WitnessStack {
                        name: "metadata".into(),
                        base: 12,
                        len: 1,
                    },
                    RHint::WitnessStack {
                        name: "control".into(),
                        base: 16,
                        len: 7,
                    },
                ],
            )
        })
        .collect::<HashMap<_, _>>();
    (Program::assemble(code, hints, FRAME + 64), second)
}

fn valid_witnesses() {
    let (mut program, second) = program();
    let public = [F192::from(g_pow(1)), F192::from(g_pow(FRAME as usize))];
    let mut common = None;
    for alias in [false, true] {
        let destination = FRAME + if alias { 0 } else { 32 };
        let mut data = vec![F192::ZERO; 10];
        data[8..10].copy_from_slice(&IV_CELLS);
        let control = vec![
            F192::ONE,
            F192::from(g_pow(second as usize)),
            F192::from(g_pow(destination as usize)),
            F192::ZERO,
            F192::ONE,
            F192::from(g_pow(63)),
            F192::ONE,
        ];
        program.set_witness("data", vec![data.clone(), data]);
        program.set_witness("metadata", vec![vec![F192::new(64, u32::MAX as u64, 0)]; 2]);
        program.set_witness("control", vec![control.clone(), control]);
        let execution = program.execute(public);
        assert_eq!(execution.base_counts, [1, 1, 8, 1, 4, 8]);
        assert!(execution.unconstrained_reads.is_empty());
        assert_eq!(
            execution.mem[FRAME as usize + 10..FRAME as usize + 12],
            execution.mem[destination as usize + 10..destination as usize + 12]
        );
        let (proof, stats) = prove(&program, public, 1);
        verify(&program, &public, &proof).expect("valid frame-sharing proof");
        assert_eq!(stats.counts, execution.base_counts);
        let heights = stats.counts.map(|count| count.ilog2() as usize);
        let shape = layout(&program.prog, stats.log_mem, heights, public).shape;
        let observed = (stats.log_mem, heights, shape.mu);
        if let Some(previous) = common {
            assert_eq!(previous, observed);
        }
        common = Some(observed);
        println!("Native proof verifies with alias={alias}, the same compression values, public input and heights.");
    }
}

fn encoder_and_authentication() {
    let log_stack = 15;
    let lane_len = 1 << (log_stack - whir::INITIAL_FOLDING_FACTOR);
    let lanes = 35;
    let selected = 5;
    let queries = [700, 701];
    let mut secret_observations = Vec::new();
    for secret in 0..=1 {
        let mut reference = None;
        for randomizer in 1..=2 {
            let mut lane = vec![F64::ZERO; lane_len];
            for pair in 0..lane_len / 2 {
                let value = g_pow((pair * 7 + randomizer) % 256);
                lane[2 * pair] = value;
                lane[2 * pair + 1] = value;
            }
            lane[65] += F64(secret);
            let mut encoded = lane.clone();
            encoded.resize(2 * lane_len, F64::ZERO);
            AdditiveNttF64::standard(10).forward_transform_scalar(&mut encoded);
            let x = F64(queries[0] as u64);
            let observable = x * encoded[queries[0]] + (F64::ONE + x) * encoded[queries[1]];
            let mut message = vec![F64::ZERO; lanes * lane_len];
            message[selected * lane_len..(selected + 1) * lane_len].copy_from_slice(&lane);
            let (commitment, data) = whir::commit(&message, log_stack, whir::INITIAL_FOLDING_FACTOR, 1);
            let paths = PrunedMerklePaths::prune(&data.merkle_tree, 2 * lane_len, &queries, |query| {
                data.codeword[query * lanes..(query + 1) * lanes].to_vec()
            });
            let raw = paths
                .open(&commitment.root, 2 * lane_len, &queries, lanes, 64)
                .expect("authenticated query pair");
            let values: Vec<_> = raw
                .iter()
                .enumerate()
                .map(|(index, path)| {
                    assert_eq!(path.root(queries[index]), commitment.root);
                    path.leaf_data[63 - selected]
                })
                .collect();
            assert_eq!(observable, x * values[0] + (F64::ONE + x) * values[1]);
            if let Some(previous) = reference {
                assert_eq!(previous, observable);
            }
            reference = Some(observable);
        }
        secret_observations.push(reference.unwrap());
    }
    assert_eq!(secret_observations[0], F64::ZERO);
    assert_ne!(secret_observations[0], secret_observations[1]);
    println!("Native NTT and authenticated leaves preserve the two-query cancellation, independently of paired masks.");
    println!(
        "This is a small encoder certificate and a separate native witness pair, not a complete size-28 ZK-mode proof or a Fiat-Shamir probability theorem."
    );
}

fn main() {
    lean_vm::init_prover_pool();
    valid_witnesses();
    encoder_and_authentication();
}
