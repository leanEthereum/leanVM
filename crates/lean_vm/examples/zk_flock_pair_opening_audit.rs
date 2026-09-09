//! Valid frame-alias witnesses and the native two-query cancellation identity.

use std::collections::HashMap;
use std::io::Read;

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

fn valid_pointer_witnesses() {
    let mut code = vec![Op::Jump { oc: 0, od: 0, of: 1 }];
    for offset in 0..4 {
        code.push(Op::Set {
            o: offset,
            k: F192::ZERO,
        });
    }
    code.extend([
        Op::Set {
            o: 12,
            k: F192::new(64, u32::MAX as u64, 0),
        },
        Op::Set {
            o: 14,
            k: F192::from(g_pow(31)),
        },
        Op::Set { o: 15, k: F192::ONE },
        Op::Set { o: 20, k: IV_CELLS[1] },
        Op::Xor { a: 0, b: 0, c: 16 },
        Op::Mul { a: 0, b: 0, c: 17 },
        Op::Deref {
            o1: 18,
            o2: 0,
            o3: 19,
            mode: DerefMode::Cell,
        },
    ]);
    code.extend(std::iter::repeat_n(
        Op::Blake2s {
            ins: [0, 1, 2, 3],
            cv: 8,
            out: 10,
            md: 12,
        },
        8,
    ));
    code.push(Op::Jump { oc: 14, od: 14, of: 15 });
    code.resize(32, Op::Set { o: 0, k: F192::ZERO });
    let hints = HashMap::from([(
        1,
        vec![
            RHint::WitnessStack {
                name: "cv".into(),
                base: 8,
                len: 2,
            },
            RHint::WitnessStack {
                name: "pointer".into(),
                base: 18,
                len: 1,
            },
        ],
    )]);
    let mut program = Program::assemble(code, hints, FRAME + 32);
    let public = [F192::from(g_pow(1)), F192::from(g_pow(FRAME as usize))];
    let mut common = None;
    for offset in [9, 20] {
        program.set_witness("cv", vec![IV_CELLS.to_vec()]);
        program.set_witness("pointer", vec![vec![F192::from(g_pow((FRAME + offset) as usize))]]);
        let execution = program.execute(public);
        assert_eq!(execution.base_counts, [1, 1, 8, 1, 2, 8]);
        assert!(execution.unconstrained_reads.is_empty());
        assert_eq!(execution.mem[FRAME as usize + 19], IV_CELLS[1]);
        let (proof, stats) = prove(&program, public, 1);
        verify(&program, &public, &proof).expect("valid private read-target proof");
        assert_eq!(stats.counts, execution.base_counts);
        let observed = (
            stats.log_mem,
            stats.counts,
            execution.mem[FRAME as usize + 10..FRAME as usize + 12].to_vec(),
        );
        if let Some(previous) = &common {
            assert_eq!(previous, &observed);
        }
        common = Some(observed);
        println!(
            "Native proof verifies for private read offset {offset}, with common compression values, public input and heights."
        );
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

fn matching_certificate(queries: usize) {
    assert!((1..=1 << 17).contains(&queries));
    let mut input = String::new();
    std::io::stdin()
        .read_to_string(&mut input)
        .expect("source positions on stdin");
    let positions: Vec<usize> = input.split_whitespace().map(|value| value.parse().unwrap()).collect();
    assert_eq!(positions.len(), 8128);
    assert!(
        positions
            .iter()
            .all(|&position| position < 1 << 18 && position & 1 == 0)
    );
    let mut unique = positions.clone();
    unique.sort_unstable();
    unique.dedup();
    assert_eq!(positions.len(), unique.len());
    let kernel_positions: Vec<_> = (0usize..4096)
        .filter(|index| (index >> 6).count_ones() <= 1)
        .map(|index| {
            let sparse = (3 << 8) | ((index & 127) << 1);
            let bank = 64 + (index >> 7);
            (sparse & 7) | ((sparse >> 7) << 3) | (bank << 7) | (((sparse >> 3) & 15) << 14)
        })
        .collect();
    assert_eq!(kernel_positions.len(), 448);
    let mut basis: Vec<_> = (0..18).map(|bit| F64(1 << bit)).collect();
    let mut roots = [F64::ZERO; 18];
    let mut inverses = roots;
    for bit in 0..18 {
        roots[bit] = basis[bit];
        inverses[bit] = basis[bit].inv();
        for value in &mut basis[bit + 1..] {
            *value *= *value + roots[bit];
        }
    }
    let check_terms: Vec<_> = positions
        .iter()
        .step_by(2032)
        .copied()
        .zip([F64(3), F64(5), F64(17), F64(257)])
        .collect();
    let mut encoded = vec![F64::ZERO; 1 << 19];
    for &(position, coefficient) in &check_terms {
        encoded[position] = coefficient;
    }
    AdditiveNttF64::standard(19).forward_transform_scalar(&mut encoded);
    for start in (0..queries).step_by(4096) {
        let count = (queries - start).min(4096);
        parallel::for_each(count, |offset| {
            let query = (1 << 18) + 2 * (start + offset);
            let mut value = F64(query as u64);
            let mut factors = roots;
            for bit in 0..18 {
                factors[bit] = value * inverses[bit];
                value *= value + roots[bit];
            }
            let mut low = [F64::ONE; 256];
            let mut high = [F64::ONE; 512];
            for index in 1usize..256 {
                let bit = index.trailing_zeros() as usize;
                low[index] = low[index & (index - 1)] * factors[bit + 1];
            }
            for index in 1usize..512 {
                let bit = index.trailing_zeros() as usize;
                high[index] = high[index & (index - 1)] * factors[bit + 9];
            }
            let observed = check_terms.iter().fold(F64::ZERO, |sum, &(position, coefficient)| {
                sum + coefficient * low[(position >> 1) & 255] * high[position >> 9]
            });
            assert_eq!(observed, encoded[query]);
            assert_eq!(observed, encoded[query + 1]);
            let mut kernel_pivots = [0u64; 64];
            let mut kernel_rank = 0;
            for &position in &kernel_positions {
                let mut value = (low[(position >> 1) & 255] * high[position >> 9]).0;
                while value != 0 {
                    let bit = 63 - value.leading_zeros() as usize;
                    if kernel_pivots[bit] == 0 {
                        kernel_pivots[bit] = value;
                        kernel_rank += 1;
                        break;
                    }
                    value ^= kernel_pivots[bit];
                }
                if kernel_rank == 64 {
                    break;
                }
            }
            assert_eq!(kernel_rank, 64, "original adjacent-source kernel rank at query {query}");
            let mut pivots = [0u64; 64];
            let mut rank = 0;
            let mut anchor = None;
            let mut bases = 0;
            for &position in &positions {
                let mut value = (low[(position >> 1) & 255] * high[position >> 9]).0;
                if let Some(first) = anchor {
                    value ^= first;
                } else {
                    anchor = Some(value);
                    continue;
                }
                while value != 0 {
                    let bit = 63 - value.leading_zeros() as usize;
                    if pivots[bit] == 0 {
                        pivots[bit] = value;
                        rank += 1;
                        break;
                    }
                    value ^= pivots[bit];
                }
                if rank == 64 {
                    bases += 1;
                    if bases == 112 {
                        break;
                    }
                    pivots.fill(0);
                    rank = 0;
                    anchor = None;
                }
            }
            assert_eq!(bases, 112, "affine-basis packing at query {query}");
        });
        println!(
            "Certified 224 disjoint affine bases at {} of 131072 adjacent query pairs.",
            start + count
        );
    }
    assert_eq!(
        queries,
        1 << 17,
        "a partial run is diagnostic, not the complete certificate"
    );
    println!(
        "Exhaustive native-field certificate: every pair in g^18 + V18 has 224 disjoint affine bases and original-source kernel rank 64."
    );
}

fn main() {
    lean_vm::init_prover_pool();
    let mut arguments = std::env::args().skip(1);
    if arguments.next().as_deref() == Some("--matching-certificate") {
        let queries = arguments.next().map_or(1 << 17, |value| value.parse().unwrap());
        matching_certificate(queries);
        return;
    }
    valid_witnesses();
    valid_pointer_witnesses();
    encoder_and_authentication();
}
