use std::collections::{BTreeSet, HashMap};

use backend::{PrimeCharacteristicRing, PrimeField32, poseidon_hash_slice, poseidon16_compress_pair};
use lean_vm::F;

use crate::{
    Commitment, DIGEST_LEN, DemoError, ParameterProfile, PreparedStatement, ProofBundle,
    encoding::{Codewords, Data, ErasureDecoder, encode},
    hashing::{Digest, column_hash, merkle_layers, row_hash},
    prepare_statement, prove_codewords, verify_execution_proof,
};

#[derive(Clone, Debug)]
pub struct AuxiliaryData {
    pub profile: ParameterProfile,
    pub codewords: Codewords,
    pub merkle_layers: Vec<Vec<Digest>>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CellOpening {
    pub index: usize,
    pub cells: Vec<Vec<F>>,
    pub authentication_path: Vec<Digest>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Transcript {
    pub openings: Vec<CellOpening>,
}

/// Encodes data and constructs the public row and column commitments.
pub fn encode_and_commit(profile: ParameterProfile, data: &Data) -> Result<(Commitment, AuxiliaryData), DemoError> {
    profile.validate()?;
    if data.len() != profile.n || data.iter().any(|blob| blob.len() != profile.k) {
        return Err(DemoError::InvalidDataShape);
    }
    let codewords = encode(profile, data);
    let row_hashes = codewords.iter().map(|row| row_hash(profile, row)).collect();
    let leaves: Vec<_> = (0..profile.n_cells())
        .map(|cell| column_hash(profile, &codewords, cell))
        .collect();
    let merkle_layers = merkle_layers(&leaves);
    let commitment = Commitment {
        profile,
        row_hashes,
        root: merkle_layers.last().unwrap()[0],
    };
    Ok((
        commitment,
        AuxiliaryData {
            profile,
            codewords,
            merkle_layers,
        },
    ))
}

/// Runs the complete convenience workflow while retaining the prepared statement.
pub fn commit(
    profile: ParameterProfile,
    data: &Data,
) -> Result<(PreparedStatement, AuxiliaryData, ProofBundle), DemoError> {
    let (commitment, aux) = encode_and_commit(profile, data)?;
    let prepared = prepare_statement(commitment)?;
    let proof = prove_codewords(&prepared, &aux.codewords)?;
    Ok((prepared, aux, proof))
}

/// Opens requested cell columns and attaches their complete Merkle paths.
pub fn query(aux: &AuxiliaryData, indices: &[usize]) -> Result<Transcript, DemoError> {
    let profile = aux.profile;
    let mut seen = BTreeSet::new();
    let mut openings = Vec::with_capacity(indices.len());
    for &index in indices {
        if index >= profile.n_cells() || !seen.insert(index) {
            return Err(DemoError::InvalidQuery);
        }
        let start = index * profile.c;
        let cells = aux
            .codewords
            .iter()
            .map(|row| row[start..start + profile.c].to_vec())
            .collect();
        let mut node = index;
        let mut authentication_path = Vec::with_capacity(profile.merkle_depth());
        for layer in aux.merkle_layers.iter().take(profile.merkle_depth()) {
            authentication_path.push(layer[node ^ 1]);
            node /= 2;
        }
        openings.push(CellOpening {
            index,
            cells,
            authentication_path,
        });
    }
    Ok(Transcript { openings })
}

/// Derives the requested number of distinct cell indices from public randomness.
pub fn sample_query_indices(
    commitment: &Commitment,
    randomness: &[F; DIGEST_LEN],
    count: usize,
) -> Result<Vec<usize>, DemoError> {
    let n_cells = commitment.profile.n_cells();
    if count == 0 || count > n_cells {
        return Err(DemoError::InvalidQuery);
    }

    let mut state = poseidon16_compress_pair(&commitment.root, randomness);
    let mut counter = 0;
    let mut seen = BTreeSet::new();
    let mut indices = Vec::with_capacity(count);
    while indices.len() < count {
        for value in state {
            let canonical = value.as_canonical_u32();
            let modulus = F::ORDER_U32;
            let unbiased_limit = modulus - modulus % n_cells as u32;
            if canonical >= unbiased_limit {
                continue;
            }
            let index = canonical as usize % n_cells;
            if seen.insert(index) {
                indices.push(index);
                if indices.len() == count {
                    break;
                }
            }
        }
        counter += 1;
        let mut counter_block = [F::ZERO; DIGEST_LEN];
        counter_block[0] = F::from_usize(counter);
        state = poseidon16_compress_pair(&state, &counter_block);
    }
    Ok(indices)
}

/// Returns the canonical byte size of the public row hashes and Merkle root.
pub fn commitment_size_bytes(commitment: &Commitment) -> usize {
    (commitment.row_hashes.len() + 1) * DIGEST_LEN * size_of::<u32>()
}

/// Returns the canonical byte size of queried indices, cells, and Merkle paths.
pub fn transcript_size_bytes(transcript: &Transcript) -> usize {
    transcript
        .openings
        .iter()
        .map(|opening| {
            size_of::<u32>()
                + opening.cells.iter().map(Vec::len).sum::<usize>() * size_of::<u32>()
                + opening.authentication_path.len() * DIGEST_LEN * size_of::<u32>()
        })
        .sum()
}

/// Rehashes each opened column and verifies its full path against the public root.
pub fn verify_openings(commitment: &Commitment, transcript: &Transcript) -> bool {
    let profile = commitment.profile;
    let mut seen = BTreeSet::new();
    transcript.openings.iter().all(|opening| {
        if opening.index >= profile.n_cells()
            || !seen.insert(opening.index)
            || opening.cells.len() != profile.n
            || opening.cells.iter().any(|cell| cell.len() != profile.c)
            || opening.authentication_path.len() != profile.merkle_depth()
        {
            return false;
        }
        let values: Vec<F> = opening.cells.iter().flatten().copied().collect();
        let mut digest = poseidon_hash_slice(&values);
        let mut node = opening.index;
        for sibling in &opening.authentication_path {
            digest = if node.is_multiple_of(2) {
                poseidon16_compress_pair(&digest, sibling)
            } else {
                poseidon16_compress_pair(sibling, &digest)
            };
            node /= 2;
        }
        digest == commitment.root
    })
}

/// Rebuilds the public LeanVM statement, verifies its proof, and checks openings.
pub fn verify(commitment: &Commitment, proof: &ProofBundle, transcript: &Transcript) -> Result<bool, DemoError> {
    verify_execution_proof(commitment, proof)?;
    Ok(verify_openings(commitment, transcript))
}

/// Collects distinct valid cells and reconstructs every original systematic blob.
pub fn reconstruct(commitment: &Commitment, transcripts: &[Transcript]) -> Result<Data, DemoError> {
    let profile = commitment.profile;
    let mut openings = HashMap::new();
    for transcript in transcripts {
        if !verify_openings(commitment, transcript) {
            return Err(DemoError::InvalidOpening);
        }
        for opening in &transcript.openings {
            openings.entry(opening.index).or_insert_with(|| opening.clone());
        }
    }
    if openings.len() < profile.reconstruction_threshold_cells() {
        return Err(DemoError::InsufficientCells);
    }

    let mut indices: Vec<_> = openings.keys().copied().collect();
    indices.sort_unstable();
    let symbol_indices: Vec<_> = indices
        .iter()
        .flat_map(|&index| (0..profile.c).map(move |offset| index * profile.c + offset))
        .collect();
    let decoder = ErasureDecoder::new(profile, &symbol_indices).ok_or(DemoError::ReconstructionFailed)?;
    (0..profile.n)
        .map(|row| {
            let values: Vec<_> = indices
                .iter()
                .flat_map(|&index| {
                    let opening = &openings[&index];
                    (0..profile.c).map(move |offset| opening.cells[row][offset])
                })
                .collect();
            decoder.reconstruct_blob(&values).ok_or(DemoError::ReconstructionFailed)
        })
        .collect()
}

/// Reports how many systematic positions can occur inside one cell.
pub fn systematic_symbols_per_cell(profile: ParameterProfile) -> usize {
    (0..profile.c)
        .filter(|offset| offset.is_multiple_of(profile.systematic_stride()))
        .count()
}
