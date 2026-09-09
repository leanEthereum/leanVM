//! Native evidence for the fixed-memory-prefix privacy obstruction.

use std::collections::HashMap;

use fiat_shamir::merkle::PrunedMerklePaths;
use lean_vm::cpu::{
    DerefMode, Op, Program,
    filler::{self, frame as fr},
    hints::RHint,
    layout, prove, verify,
};
use pcs::{ntt::AdditiveNttF64, whir};
use primitives::field::{F64, F192, g_pow};

fn program() -> Program {
    let mut code = vec![
        Op::Xor { a: 2, b: 2, c: 3 },
        Op::Set {
            o: 1 << 19,
            k: F192::ZERO,
        },
        Op::Set {
            o: 4,
            k: F192::from(g_pow(2047)),
        },
        Op::Set { o: 5, k: F192::ONE },
        Op::Jump { oc: 4, od: 4, of: 5 },
    ];
    let mut blocks = Vec::new();
    for table in 0..6 {
        let scratch = fr::SCRATCH;
        let dummy = match table {
            0 => Op::Xor {
                a: scratch,
                b: scratch,
                c: scratch,
            },
            1 => Op::Mul {
                a: scratch,
                b: scratch,
                c: scratch,
            },
            2 => Op::Set {
                o: scratch,
                k: F192::ZERO,
            },
            3 => Op::Deref {
                o1: fr::PTR,
                o2: 0,
                o3: scratch,
                mode: DerefMode::Cell,
            },
            4 => Op::Jump {
                oc: fr::ZERO,
                od: fr::ZERO,
                of: fr::ZERO,
            },
            5 => Op::Blake2s {
                ins: [fr::DIGEST + 2, fr::DIGEST + 3, fr::DIGEST + 4, fr::DIGEST + 5],
                cv: scratch,
                out: fr::DIGEST,
                md: fr::ZERO,
            },
            _ => unreachable!(),
        };
        for size in filler::SIZES {
            blocks.push(filler::Block {
                pc: code.len() as u32,
                size: size as u32,
                table,
            });
            code.extend(std::iter::repeat_n(dummy, size));
            code.push(Op::Jump {
                oc: fr::DEST,
                od: fr::DEST,
                of: fr::NEXT_FP,
            });
        }
    }
    assert!(code.len() < 2048);
    code.resize(2048, Op::Set { o: 3, k: F192::ZERO });
    let hints = HashMap::from([(
        0,
        vec![RHint::WitnessStack {
            name: "bit".into(),
            base: 2,
            len: 1,
        }],
    )]);
    let mut program = Program::assemble(code, hints, 6);
    program.filler = blocks;
    program
}

fn encoder_and_authentication() {
    let log_stack = 15;
    let log_lanes = whir::INITIAL_FOLDING_FACTOR;
    let lane_len = 1 << (log_stack - log_lanes);
    let lanes = 35;
    let selected = 5;
    let domain = 2 * lane_len;
    for bit in 0..=1 {
        for seed in 1..=3u64 {
            let mut state = seed;
            let mut message: Vec<F64> = (0..lanes * lane_len)
                .map(|_| {
                    state ^= state << 13;
                    state ^= state >> 7;
                    state ^= state << 17;
                    F64(state)
                })
                .collect();
            message[selected * lane_len..selected * lane_len + 4].copy_from_slice(&[
                F64::ZERO,
                F64::ZERO,
                F64(bit),
                F64::ZERO,
            ]);
            let mut independent = message[selected * lane_len..(selected + 1) * lane_len].to_vec();
            independent.resize(domain, F64::ZERO);
            AdditiveNttF64::standard(domain.ilog2() as usize).forward_transform_scalar(&mut independent);
            let (commitment, data) = whir::commit(&message, log_stack, log_lanes, 1);
            let queries = [2, 3];
            let paths = PrunedMerklePaths::prune(&data.merkle_tree, domain, &queries, |query| {
                data.codeword[query * lanes..(query + 1) * lanes].to_vec()
            });
            let raw = paths
                .open(&commitment.root, domain, &queries, lanes, 1 << log_lanes)
                .expect("native authenticated openings");
            for (&query, path) in queries.iter().zip(raw) {
                assert_eq!(path.root(query), commitment.root);
                assert_eq!(path.leaf_data[(1 << log_lanes) - 1 - selected], F64(bit));
                assert_eq!(independent[query], F64(bit));
            }
        }
    }
    println!("Native scalar NTT, interleaved commitment and authenticated pruned openings expose the same prefix bit.");
}

fn valid_execution_pair() {
    let mut program = program();
    let public_input = [F192::ZERO; 2];
    let mut common_shape = None;
    for bit in 0..=1 {
        program.set_witness("bit", vec![vec![F192::new(bit, bit, bit)]]);
        let execution = program.execute(public_input);
        assert_eq!(execution.mem.len(), 1 << 20);
        assert_eq!(execution.mem[2], F192::new(bit, bit, bit));
        assert_eq!(execution.mem[3], F192::ZERO);
        assert_eq!(execution.mem[1 << 19], F192::ZERO);
        assert!(execution.unconstrained_reads.is_empty());
        let (proof, stats) = prove(&program, public_input, 1);
        verify(&program, &public_input, &proof).expect("complete native VM proof");
        let heights = stats.counts.map(|count| count.ilog2() as usize);
        let layout = layout(&program.prog, stats.log_mem, heights, public_input);
        let lane_len = 1 << (layout.shape.mu - whir::INITIAL_FOLDING_FACTOR);
        let selected = (0..3)
            .find(|&column| layout.placements[column].offset.is_multiple_of(lane_len))
            .expect("aligned memory limb");
        let shape = (stats.log_mem, heights, layout.shape.mu, selected);
        if let Some(previous) = common_shape {
            assert_eq!(shape, previous);
        }
        common_shape = Some(shape);
        println!(
            "Valid bit-{bit} execution and complete proof: memory log {}, tables {heights:?}, stack log {}, aligned limb {selected}.",
            stats.log_mem, layout.shape.mu
        );
    }
    println!("The complete proofs use ordinary Fiat-Shamir queries; the exceptional openings were checked separately.");
}

fn main() {
    lean_vm::init_prover_pool();
    encoder_and_authentication();
    valid_execution_pair();
}
