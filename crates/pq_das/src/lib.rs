mod config;
mod encoding;
mod hashing;
mod membership;
mod protocol;

use std::{
    collections::BTreeMap,
    fmt::{Display, Formatter},
};

use backend::{ArenaVec, PrimeCharacteristicRing, arena_vec};
use lean_compiler::{CompilationFlags, ProgramSource, compile_program_with_flags};
use lean_prover::{
    default_whir_config,
    prove_execution::{ExecutionProof, prove_execution},
    verify_execution::verify_execution,
};
use lean_vm::{Bytecode, ExecutionWitness, F, Hints};

pub use config::*;
pub use encoding::{Blob, Codeword, Codewords, Data, ErasureDecoder, demo_data, encode, encode_blob};
pub use hashing::Digest;
pub use protocol::{
    AuxiliaryData, CellOpening, Transcript, commit, commitment_size_bytes, encode_and_commit, query, reconstruct,
    sample_query_indices, systematic_symbols_per_cell, transcript_size_bytes, verify, verify_openings,
};

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Commitment {
    pub profile: ParameterProfile,
    pub row_hashes: Vec<Digest>,
    pub root: Digest,
}

#[derive(Debug, Clone)]
pub struct ProofBundle {
    pub execution: ExecutionProof,
}

#[derive(Debug, Clone)]
pub struct PreparedStatement {
    /// Public profile, row hashes, and Merkle root represented by this statement.
    pub commitment: Commitment,
    /// Public special-barycentric vector generated once during preparation.
    pub check_vector: membership::CheckVector,
    /// Compact profile bytecode with the statement values bound read-only.
    pub bytecode: Bytecode,
}

#[derive(Debug)]
pub enum DemoError {
    InvalidDataShape,
    InvalidQuery,
    InvalidOpening,
    InsufficientCells,
    ReconstructionFailed,
    ChallengeOnDomain,
    Profile(ProfileError),
    Prover(lean_prover::ProverError),
    Verification(backend::ProofError),
}

impl Display for DemoError {
    /// Formats each demo failure as a concise user-facing diagnostic.
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::InvalidDataShape => write!(f, "data dimensions do not match the selected profile"),
            Self::InvalidQuery => write!(f, "query contains an invalid or duplicate cell index"),
            Self::InvalidOpening => write!(f, "invalid cell opening"),
            Self::InsufficientCells => write!(f, "not enough distinct cells to reconstruct"),
            Self::ReconstructionFailed => write!(f, "RS reconstruction failed"),
            Self::ChallengeOnDomain => write!(f, "Fiat-Shamir challenge lies on the interpolation domain"),
            Self::Profile(err) => write!(f, "invalid parameter profile: {err}"),
            Self::Prover(err) => write!(f, "LeanVM prover failed: {err}"),
            Self::Verification(err) => write!(f, "LeanVM verification failed: {err}"),
        }
    }
}

impl std::error::Error for DemoError {}

impl From<ProfileError> for DemoError {
    /// Converts profile validation failures into the demo's unified error type.
    fn from(value: ProfileError) -> Self {
        Self::Profile(value)
    }
}

impl From<lean_prover::ProverError> for DemoError {
    /// Converts LeanVM prover failures into the demo's unified error type.
    fn from(value: lean_prover::ProverError) -> Self {
        Self::Prover(value)
    }
}

/// Loads the embedded generalized zkDSL verifier program.
fn guest_source() -> ProgramSource {
    ProgramSource::Raw(include_str!("../zkdsl/main.py").to_string())
}

/// Creates profile-specific zkDSL replacements and read-only memory pointers.
fn compilation_flags(commitment: &Commitment) -> Result<CompilationFlags, DemoError> {
    commitment.profile.validate()?;
    if commitment.row_hashes.len() != commitment.profile.n {
        return Err(DemoError::InvalidDataShape);
    }
    let profile = commitment.profile;
    let mut replacements = BTreeMap::new();
    for (name, value) in [
        ("N_PLACEHOLDER", profile.n),
        ("M_PLACEHOLDER", profile.m),
        ("K_PLACEHOLDER", profile.k),
        ("C_PLACEHOLDER", profile.c),
        ("N_CELLS_PLACEHOLDER", profile.n_cells()),
        ("SYSTEMATIC_STRIDE_PLACEHOLDER", profile.systematic_stride()),
        ("ROW_CHUNKS_PLACEHOLDER", profile.k / DIGEST_LEN),
        ("COLUMN_CHUNKS_PLACEHOLDER", profile.n * profile.c / DIGEST_LEN),
        ("MERKLE_DEPTH_PLACEHOLDER", profile.merkle_depth()),
        ("TREE_DIGESTS_PLACEHOLDER", 2 * profile.n_cells() - 1),
        ("PUBLIC_ROW_HASHES_PTR_PLACEHOLDER", DIGEST_LEN),
        ("PUBLIC_ROOT_PTR_PLACEHOLDER", DIGEST_LEN + profile.n * DIGEST_LEN),
        ("CHECK_VECTOR_PTR_PLACEHOLDER", 2 * DIGEST_LEN + profile.n * DIGEST_LEN),
    ] {
        replacements.insert(name.to_string(), value.to_string());
    }

    let mut sizes = Vec::with_capacity(profile.merkle_depth() + 1);
    let mut offsets = Vec::with_capacity(profile.merkle_depth() + 1);
    let mut size = profile.n_cells();
    let mut offset = 0;
    loop {
        sizes.push(size);
        offsets.push(offset);
        if size == 1 {
            break;
        }
        offset += size;
        size /= 2;
    }
    replacements.insert(
        "LEVEL_SIZES_PLACEHOLDER".to_string(),
        format!("[{}]", sizes.iter().map(usize::to_string).collect::<Vec<_>>().join(",")),
    );
    replacements.insert(
        "LEVEL_OFFSETS_PLACEHOLDER".to_string(),
        format!(
            "[{}]",
            offsets.iter().map(usize::to_string).collect::<Vec<_>>().join(",")
        ),
    );
    Ok(CompilationFlags { replacements })
}

/// Returns the legacy fixed public-input block; statement data lives read-only.
fn leanvm_public_input() -> [F; DIGEST_LEN] {
    [F::ZERO; DIGEST_LEN]
}

/// Flattens public hashes, root, and L into LeanVM's bound read-only segment.
fn read_only_data(commitment: &Commitment, check_vector: &membership::CheckVector) -> Vec<F> {
    let mut data =
        Vec::with_capacity(commitment.profile.n * DIGEST_LEN + DIGEST_LEN + commitment.profile.m * EXT_DEGREE);
    data.extend(commitment.row_hashes.iter().flatten().copied());
    data.extend_from_slice(&commitment.root);
    data.extend(check_vector.iter().flatten().copied());
    data
}

/// Generates L once and compiles the reusable statement-bound LeanVM bytecode.
pub fn prepare_statement(commitment: Commitment) -> Result<PreparedStatement, DemoError> {
    let check_vector = membership::check_vector(&commitment).ok_or(DemoError::ChallengeOnDomain)?;
    let bytecode = compile_program_with_flags(&guest_source(), compilation_flags(&commitment)?)
        .with_read_only_data(read_only_data(&commitment, &check_vector));
    Ok(PreparedStatement {
        commitment,
        check_vector,
        bytecode,
    })
}

/// Packages only the private codeword matrix into the LeanVM witness.
fn witness(bytecode: &Bytecode, codewords: &Codewords) -> ExecutionWitness {
    let flattened: Vec<_> = codewords.iter().flat_map(|row| row.iter().copied()).collect();
    let mut hints = Hints::default();
    hints.insert(bytecode, "codewords", arena_vec![ArenaVec::from_slice(&flattened)]);
    ExecutionWitness {
        hints,
        ..Default::default()
    }
}

/// Proves the prepared row-hash, Merkle-root, and RS dot-product statement.
pub fn prove_codewords(prepared: &PreparedStatement, codewords: &Codewords) -> Result<ProofBundle, DemoError> {
    let profile = prepared.commitment.profile;
    if codewords.len() != profile.n || codewords.iter().any(|row| row.len() != profile.m) {
        return Err(DemoError::InvalidDataShape);
    }
    let execution = prove_execution(
        &prepared.bytecode,
        &leanvm_public_input(),
        &witness(&prepared.bytecode, codewords),
        &default_whir_config(profile.whir_log_inv_rate),
        false,
    )?;
    Ok(ProofBundle { execution })
}

/// Recomputes Fiat-Shamir and L from the public commitment before verifying.
pub fn verify_execution_proof(commitment: &Commitment, proof: &ProofBundle) -> Result<(), DemoError> {
    // The verifier never accepts L from the prover. Re-preparing the statement
    // independently binds the proof to the unique L derived from public data.
    let prepared = prepare_statement(commitment.clone())?;
    verify_execution(
        &prepared.bytecode,
        &leanvm_public_input(),
        proof.execution.proof.clone(),
    )
    .map(|_| ())
    .map_err(DemoError::Verification)
}

#[cfg(test)]
mod tests {
    use super::*;
    use backend::PrimeCharacteristicRing;

    /// Creates native commitment material without invoking the LeanVM prover.
    fn native_material(profile: ParameterProfile) -> (Data, Commitment, AuxiliaryData) {
        let data = demo_data(profile);
        let codewords = encode(profile, &data);
        let row_hashes = codewords.iter().map(|row| hashing::row_hash(profile, row)).collect();
        let leaves: Vec<_> = (0..profile.n_cells())
            .map(|cell| hashing::column_hash(profile, &codewords, cell))
            .collect();
        let merkle_layers = hashing::merkle_layers(&leaves);
        let commitment = Commitment {
            profile,
            row_hashes,
            root: merkle_layers.last().unwrap()[0],
        };
        let aux = AuxiliaryData {
            profile,
            codewords,
            merkle_layers,
        };
        (data, commitment, aux)
    }

    #[test]
    /// Exercises generalized native commitments, openings, and reconstruction.
    fn native_protocol_roundtrip_and_tamper_detection() {
        let profile = ParameterProfile::TINY;
        let (data, commitment, aux) = native_material(profile);

        let transcript = query(&aux, &[1]).unwrap();
        assert!(verify_openings(&commitment, &transcript));
        assert_eq!(
            reconstruct(&commitment, std::slice::from_ref(&transcript)).unwrap(),
            data
        );

        let mut bad = transcript;
        bad.openings[0].cells[0][0] += F::ONE;
        assert!(!verify_openings(&commitment, &bad));
    }

    #[test]
    /// Confirms all built-in profiles satisfy the implementation constraints.
    fn predefined_profiles_are_valid() {
        for profile in [
            ParameterProfile::TINY,
            ParameterProfile::MEDIUM,
            ParameterProfile::LARGE,
            ParameterProfile::STRESS,
            ParameterProfile::BLOB_128K_1,
            ParameterProfile::BLOB_128K_4,
            ParameterProfile::BLOB_128K_16,
        ] {
            profile.validate().unwrap();
        }
    }

    #[test]
    /// Pins the minimum distinct-cell counts that match LeanVM's availability-soundness target.
    fn predefined_profiles_have_expected_sampling_counts() {
        for (profile, expected) in [
            (ParameterProfile::TINY, 1),
            (ParameterProfile::MEDIUM, 16),
            (ParameterProfile::LARGE, 63),
            (ParameterProfile::STRESS, 105),
            (ParameterProfile::BLOB_128K_1, 114),
            (ParameterProfile::BLOB_128K_4, 114),
            (ParameterProfile::BLOB_128K_16, 114),
        ] {
            let count = profile.sampling_count(SAMPLING_SOUNDNESS_BITS);
            assert_eq!(count, expected);
            assert!(profile.sampling_log2_failure(count) <= -(SAMPLING_SOUNDNESS_BITS as f64));
            if count > 1 {
                assert!(profile.sampling_log2_failure(count - 1) > -(SAMPLING_SOUNDNESS_BITS as f64));
            }
        }
    }

    #[test]
    /// Proves and verifies the complete generalized construction on the tiny profile.
    fn leanvm_end_to_end() {
        backend::parallel::init();
        let profile = ParameterProfile::TINY;
        let data = demo_data(profile);
        let (prepared, aux, proof) = commit(profile, &data).unwrap();
        let query_indices = sample_query_indices(&prepared.commitment, &[F::from_u32(42); DIGEST_LEN], 1).unwrap();
        let transcript = query(&aux, &query_indices).unwrap();
        assert!(verify(&prepared.commitment, &proof, &transcript).unwrap());
        assert_eq!(reconstruct(&prepared.commitment, &[transcript]).unwrap(), data);

        let mut wrong_commitment = prepared.commitment.clone();
        wrong_commitment.root[0] += F::ONE;
        assert!(verify_execution_proof(&wrong_commitment, &proof).is_err());

        let mut wrong_row_hash = prepared.commitment.clone();
        wrong_row_hash.row_hashes[0][0] += F::ONE;
        assert!(verify_execution_proof(&wrong_row_hash, &proof).is_err());
    }

    #[test]
    /// Confirms the guest rejects a row that violates its public RS check vector.
    fn guest_rejects_non_member_codeword() {
        backend::parallel::init();
        let profile = ParameterProfile::TINY;
        let (_, mut commitment, aux) = native_material(profile);
        let mut codewords = aux.codewords;
        codewords[0][1] += F::ONE;
        commitment.row_hashes = codewords.iter().map(|row| hashing::row_hash(profile, row)).collect();
        let leaves: Vec<_> = (0..profile.n_cells())
            .map(|cell| hashing::column_hash(profile, &codewords, cell))
            .collect();
        commitment.root = hashing::merkle_root(&leaves);
        let prepared = prepare_statement(commitment).unwrap();
        let execution_witness = witness(&prepared.bytecode, &codewords);
        assert!(
            lean_vm::try_execute_bytecode(&prepared.bytecode, &leanvm_public_input(), &execution_witness, false)
                .is_err()
        );
    }
}
