use std::time::Instant;

use backend::{PrimeCharacteristicRing, PrimeField32};
use clap::{Parser, ValueEnum};
use lean_vm::F;
use pq_das::{
    DIGEST_LEN, ParameterProfile, SAMPLING_SOUNDNESS_BITS, commitment_size_bytes, demo_data, encode_and_commit,
    prepare_statement, prove_codewords, query, reconstruct, sample_query_indices, transcript_size_bytes,
    verify_execution_proof, verify_openings,
};

#[derive(Clone, Copy, Debug, ValueEnum)]
enum ProfileName {
    Tiny,
    Medium,
    Large,
    Stress,
    #[value(name = "blob-128k-1")]
    Blob128K1,
    #[value(name = "blob-128k-4")]
    Blob128K4,
    #[value(name = "blob-128k-16")]
    Blob128K16,
    Custom,
}

#[derive(Debug, Parser)]
#[command(about = "Benchmark the parameterized PQ-DAS LeanVM construction")]
struct Cli {
    #[arg(long, value_enum, default_value_t = ProfileName::Tiny)]
    profile: ProfileName,

    #[arg(long)]
    n: Option<usize>,

    #[arg(long)]
    m: Option<usize>,

    #[arg(long)]
    k: Option<usize>,

    #[arg(long)]
    c: Option<usize>,

    #[arg(long, default_value_t = 1)]
    whir_log_inv_rate: usize,

    #[arg(long)]
    skip_reconstruction: bool,
}

impl Cli {
    /// Resolves a named or custom CLI selection into a validated parameter profile.
    fn selected_profile(&self) -> Result<ParameterProfile, Box<dyn std::error::Error>> {
        let mut profile = match self.profile {
            ProfileName::Tiny => ParameterProfile::TINY,
            ProfileName::Medium => ParameterProfile::MEDIUM,
            ProfileName::Large => ParameterProfile::LARGE,
            ProfileName::Stress => ParameterProfile::STRESS,
            ProfileName::Blob128K1 => ParameterProfile::BLOB_128K_1,
            ProfileName::Blob128K4 => ParameterProfile::BLOB_128K_4,
            ProfileName::Blob128K16 => ParameterProfile::BLOB_128K_16,
            ProfileName::Custom => ParameterProfile::custom(
                self.n.ok_or("custom profile requires --n")?,
                self.m.ok_or("custom profile requires --m")?,
                self.k.ok_or("custom profile requires --k")?,
                self.c.ok_or("custom profile requires --c")?,
                self.whir_log_inv_rate,
            )?,
        };
        profile.whir_log_inv_rate = self.whir_log_inv_rate;
        profile.validate()?;
        Ok(profile)
    }
}

/// Runs one complete benchmark for the selected generalized PQ-DAS profile.
fn main() -> Result<(), Box<dyn std::error::Error>> {
    backend::parallel::init();
    let cli = Cli::parse();
    let profile = cli.selected_profile()?;
    let data = demo_data(profile);

    let started = Instant::now();
    let (commitment, aux) = encode_and_commit(profile, &data)?;
    let commitment_time = started.elapsed();

    let started = Instant::now();
    let prepared = prepare_statement(commitment)?;
    let preprocessing_time = started.elapsed();

    let started = Instant::now();
    let proof = prove_codewords(&prepared, &aux.codewords)?;
    let proving_time = started.elapsed();

    let sample_count = profile.sampling_count(SAMPLING_SOUNDNESS_BITS);
    let indices = sample_query_indices(&prepared.commitment, &[F::from_u32(42); DIGEST_LEN], sample_count)?;
    let transcript = query(&aux, &indices)?;

    let started = Instant::now();
    verify_execution_proof(&prepared.commitment, &proof)?;
    let proof_verification_time = started.elapsed();

    let started = Instant::now();
    let openings_accepted = verify_openings(&prepared.commitment, &transcript);
    let opening_verification_time = started.elapsed();
    let accepted = openings_accepted;
    let (reconstruction, reconstruction_time) = if cli.skip_reconstruction {
        (None, None)
    } else {
        let reconstruction_indices = sample_query_indices(
            &prepared.commitment,
            &[F::from_u32(84); DIGEST_LEN],
            profile.reconstruction_threshold_cells(),
        )?;
        let reconstruction_transcript = query(&aux, &reconstruction_indices)?;
        let started = Instant::now();
        let correct = reconstruct(&prepared.commitment, &[reconstruction_transcript])? == data;
        (Some(correct), Some(started.elapsed()))
    };
    let commitment_bytes = commitment_size_bytes(&prepared.commitment);
    let proof_field_elements = proof.execution.proof.proof_size_fe();
    let proof_bytes = proof_field_elements * size_of::<u32>();
    let sample_bytes = transcript_size_bytes(&transcript);

    println!("PQ-DAS LeanVM demo");
    println!(
        "profile: {} (n={}, m={}, k={}, rho={}/{}, c={}, cells={}, threshold={})",
        profile.name,
        profile.n,
        profile.m,
        profile.k,
        profile.k,
        profile.m,
        profile.c,
        profile.n_cells(),
        profile.reconstruction_threshold_cells(),
    );
    println!(
        "root: {:?}",
        prepared.commitment.root.map(|value| value.as_canonical_u32())
    );
    println!("proof accepted: {accepted}");
    println!("bytecode instructions: {}", prepared.bytecode.size());
    println!(
        "read-only public elements: {}",
        prepared.bytecode.read_only_data().len()
    );
    println!("sampling soundness target: {SAMPLING_SOUNDNESS_BITS} bits");
    println!(
        "sampling log2 failure bound: {:.3}",
        profile.sampling_log2_failure(sample_count)
    );
    println!("opened cells: {sample_count}");
    println!("commitment size: {commitment_bytes} bytes");
    println!("proof size: {proof_field_elements} field elements ({proof_bytes} bytes)");
    println!("sample size: {sample_bytes} bytes");
    match reconstruction {
        Some(correct) => println!("reconstruction correct: {correct}"),
        None => println!("reconstruction: skipped"),
    }
    if let Some(elapsed) = reconstruction_time {
        println!("reconstruction time: {:.3}s", elapsed.as_secs_f64());
    }
    println!("encoding + commitment time: {:.3}s", commitment_time.as_secs_f64());
    println!("prover preprocessing time: {:.3}s", preprocessing_time.as_secs_f64());
    println!("LeanVM proving time: {:.3}s", proving_time.as_secs_f64());
    println!(
        "verifier statement rebuild + LeanVM proof verification time: {:.3}s",
        proof_verification_time.as_secs_f64()
    );
    println!(
        "opening verification time: {:.3}s",
        opening_verification_time.as_secs_f64()
    );
    Ok(())
}
