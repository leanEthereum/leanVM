use backend::{poseidon_hash_slice, poseidon16_compress_pair};
use lean_vm::F;

use crate::{
    Commitment,
    config::{DIGEST_LEN, ParameterProfile, fs_block},
    encoding::{Codeword, Codewords},
};

pub type Digest = [F; DIGEST_LEN];

/// Hashes the systematic symbols of one codeword into its public row digest.
pub fn row_hash(profile: ParameterProfile, row: &Codeword) -> Digest {
    let systematic: Vec<F> = (0..profile.k).map(|i| row[i * profile.systematic_stride()]).collect();
    poseidon_hash_slice(&systematic)
}

/// Hashes all rows' symbols in one cell column into a Merkle leaf.
pub fn column_hash(profile: ParameterProfile, codewords: &Codewords, cell: usize) -> Digest {
    let start = cell * profile.c;
    let mut values = Vec::with_capacity(profile.n * profile.c);
    for row in codewords {
        values.extend_from_slice(&row[start..start + profile.c]);
    }
    poseidon_hash_slice(&values)
}

/// Builds a complete binary Poseidon Merkle tree from a power-of-two leaf set.
pub fn merkle_layers(leaves: &[Digest]) -> Vec<Vec<Digest>> {
    assert!(leaves.len().is_power_of_two());
    let mut layers = vec![leaves.to_vec()];
    while layers.last().unwrap().len() > 1 {
        let next = layers
            .last()
            .unwrap()
            .chunks_exact(2)
            .map(|pair| poseidon16_compress_pair(&pair[0], &pair[1]))
            .collect();
        layers.push(next);
    }
    layers
}

/// Returns the root of a complete binary Poseidon Merkle tree.
pub fn merkle_root(leaves: &[Digest]) -> Digest {
    merkle_layers(leaves).last().unwrap()[0]
}

/// Derives the public RS Fiat-Shamir digest from the profile and commitment.
pub fn fiat_shamir_digest(commitment: &Commitment) -> Digest {
    let mut values = Vec::with_capacity((3 + commitment.profile.n) * DIGEST_LEN);
    values.extend_from_slice(&fs_block());
    values.extend_from_slice(&commitment.profile.profile_block());
    for hash in &commitment.row_hashes {
        values.extend_from_slice(hash);
    }
    values.extend_from_slice(&commitment.root);
    poseidon_hash_slice(&values)
}
