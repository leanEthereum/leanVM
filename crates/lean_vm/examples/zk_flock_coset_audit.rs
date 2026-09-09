//! Native packing, encoding and authentication checks for the Flock coset audit.

use std::io;

use fiat_shamir::merkle::PrunedMerklePaths;
use flock::hash;
use pcs::{ntt::AdditiveNttF64, whir};
use primitives::field::F64;

fn rank(mut rows: Vec<Vec<F64>>) -> usize {
    let mut rank = 0;
    for column in 0..rows[0].len() {
        let Some(pivot) = (rank..rows.len()).find(|&row| rows[row][column] != F64::ZERO) else {
            continue;
        };
        rows.swap(rank, pivot);
        let inverse = rows[rank][column].inv();
        for value in &mut rows[rank][column..] {
            *value *= inverse;
        }
        let (pivots, remaining) = rows.split_at_mut(rank + 1);
        let pivot = &pivots[rank];
        for row in remaining {
            let factor = row[column];
            for (value, &basis) in row[column..].iter_mut().zip(&pivot[column..]) {
                *value += factor * basis;
            }
        }
        rank += 1;
    }
    rank
}

fn main() {
    lean_vm::init_prover_pool();
    let input = io::read_to_string(io::stdin()).expect("audit input");
    let mut words = input
        .split_whitespace()
        .map(|word| word.parse::<u64>().expect("unsigned word"));
    let mut blocks = vec![hash::pinned_compression([0; 16])];
    for _ in 0..7 {
        blocks.push(hash::pinned_compression(std::array::from_fn(|_| {
            words
                .next()
                .expect("profile message")
                .try_into()
                .expect("u32 message word")
        })));
    }
    let (z, a, b, _) = hash::generate_witness_with_ab_packed_and_lincheck(&blocks, 3);
    assert!(z.iter().zip(&a).zip(&b).all(|((&z, &a), &b)| z == a & b));
    let bits: Vec<bool> = z
        .iter()
        .flat_map(|&word| (0..64).map(move |bit| (word >> bit) & 1 != 0))
        .collect();
    assert!(hash::satisfies(&bits, 3));
    for &value in &z[..256] {
        assert_eq!(value, words.next().expect("reference baseline"));
    }
    let differences: Vec<Vec<F64>> = z[256..]
        .chunks_exact(256)
        .map(|block| {
            block
                .iter()
                .zip(&z[..256])
                .map(|(&value, &baseline)| {
                    let difference = value ^ baseline;
                    assert_eq!(difference, words.next().expect("reference profile difference"));
                    F64(difference)
                })
                .collect()
        })
        .collect();
    assert!(words.next().is_none());
    assert_eq!(rank(differences.clone()), 7);

    let queries: Vec<usize> = (4..11).collect();
    let encoded: Vec<Vec<F64>> = differences
        .iter()
        .map(|profile| {
            let mut values = profile.clone();
            values.resize(1 << 12, F64::ZERO);
            AdditiveNttF64::standard(12).forward_transform_scalar(&mut values);
            values
        })
        .collect();
    for centre in [0, 256, 1024, 3072] {
        let columns: Vec<Vec<F64>> = encoded
            .iter()
            .map(|values| queries.iter().map(|&query| values[centre ^ query]).collect())
            .collect();
        assert_eq!(rank(columns), 7);
    }

    let log_stack = 15;
    let lanes = 35;
    let selected = 5;
    let lane_len = 1 << (log_stack - whir::INITIAL_FOLDING_FACTOR);
    let domain = 2 * lane_len;
    let padding: Vec<Vec<F64>> = encoded[..6]
        .iter()
        .map(|values| queries.iter().map(|&query| values[query]).collect())
        .collect();
    for bit in 0..=1 {
        let mut message: Vec<F64> = (0..lanes * lane_len).map(|index| F64(index as u64)).collect();
        message[selected * lane_len..(selected + 1) * lane_len].fill(F64::ZERO);
        for (profile, difference) in differences.iter().enumerate() {
            let coefficient = F64(if profile < 6 { 17 + profile as u64 } else { bit });
            for (slot, &value) in difference.iter().enumerate() {
                message[selected * lane_len + slot] += coefficient * value;
            }
        }
        let (commitment, data) = whir::commit(&message, log_stack, whir::INITIAL_FOLDING_FACTOR, 1);
        let paths = PrunedMerklePaths::prune(&data.merkle_tree, domain, &queries, |query| {
            data.codeword[query * lanes..(query + 1) * lanes].to_vec()
        });
        let raw = paths
            .open(
                &commitment.root,
                domain,
                &queries,
                lanes,
                1 << whir::INITIAL_FOLDING_FACTOR,
            )
            .expect("authenticated openings");
        let observed: Vec<F64> = queries
            .iter()
            .zip(raw)
            .map(|(&query, path)| {
                assert_eq!(path.root(query), commitment.root);
                path.leaf_data[(1 << whir::INITIAL_FOLDING_FACTOR) - 1 - selected]
            })
            .collect();
        let mut columns = padding.clone();
        columns.push(observed);
        assert_eq!(rank(columns), 6 + bit as usize);
    }
    println!(
        "Native valid witnesses match every reference packed word; the scalar NTT and authenticated openings preserve the distinguishing subspace."
    );
    println!("This is a small-shape encoder certificate, not a complete ZK-mode VM proof.");
}
