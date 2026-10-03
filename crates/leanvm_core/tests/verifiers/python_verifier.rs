//! Pins `python-verifier/verifier.py` against `leanvm_core::cpu::VerifyingKey::verify`: the same
//! protocol is written out in Rust and in Python, so any protocol change must land
//! in both, and this is what catches the Python one drifting.

use fiat_shamir::transcript::RawProof;
use leanvm_core::cpu::{CpuError, Program, VerifyingKey};
use leanvm_core::pcs::Rate;
use leanvm_core::rv::Region;
use leanvm_core::rv::asm::*;
use primitives::field::F192;
use std::path::{Path, PathBuf};
use std::process::{Command, Output};
use std::time::Instant;

/// One statement laid out the way the Python verifier takes it: the program's verifying
/// key, then the output.
pub struct PythonStatement {
    directory: PathBuf,
    key: PathBuf,
    output: PathBuf,
}

impl PythonStatement {
    pub fn new(tag: &str, program: &Program, output: &[u64; 4]) -> Self {
        // One directory per statement, not per tag: the tests share a process, so two of
        // them naming the same tag would write each other's files and check the wrong
        // proof, which python would ACCEPT, silently proving nothing.
        static NEXT: std::sync::atomic::AtomicUsize = std::sync::atomic::AtomicUsize::new(0);
        let unique = NEXT.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
        let directory =
            std::env::temp_dir().join(format!("leanvm-python-verifier-{tag}-{}-{unique}", std::process::id()));
        std::fs::create_dir_all(&directory).expect("create test directory");
        let statement = Self {
            key: directory.join("key.bin"),
            output: directory.join("output.bin"),
            directory,
        };
        statement.write_key(&program.verifying_key().to_bytes());
        let output: Vec<u8> = output.iter().flat_map(|w| w.to_le_bytes()).collect();
        std::fs::write(&statement.output, output).expect("write the output");
        statement
    }

    /// Have Python read `key` as the program's verifying key.
    fn write_key(&self, key: &[u8]) {
        std::fs::write(&self.key, key).expect("write the verifying key");
    }

    /// Write `raw` as the two files Python reads and run the verifier on it: the
    /// scalar stream as 24-byte little-endian elements, and every opening's leaf
    /// words followed by its sibling digests. Neither file carries a length, the
    /// reader deriving every leaf width and tree height from the protocol it is
    /// replaying.
    pub fn verify(&self, raw: &RawProof) -> Output {
        let mut stream = Vec::new();
        for scalar in &raw.stream {
            for limb in [scalar.c0, scalar.c1, scalar.c2] {
                stream.extend(limb.to_le_bytes());
            }
        }
        let mut openings = Vec::new();
        for opening in &raw.merkle {
            for word in &opening.leaf_data {
                openings.extend(word.0.to_le_bytes());
            }
            for digest in &opening.path {
                openings.extend(digest);
            }
        }
        let stream_path = self.directory.join("stream.bin");
        let openings_path = self.directory.join("merkle_openings.bin");
        std::fs::write(&stream_path, stream).expect("write scalar stream");
        std::fs::write(&openings_path, openings).expect("write Merkle openings");
        Command::new("python3")
            .arg(Path::new(env!("CARGO_MANIFEST_DIR")).join("../../python-verifier/verifier.py"))
            .arg(&self.key)
            .arg(&self.output)
            .arg(stream_path)
            .arg(openings_path)
            .output()
            .expect("run native Python verifier")
    }

    /// Python refused, and refused the way it should: through its own error path, not
    /// through a traceback, which exits nonzero just the same and would hide a crash.
    pub fn assert_rejects(output: &Output, what: &str) {
        let stderr = String::from_utf8_lossy(&output.stderr);
        assert!(!output.status.success(), "Python accepted {what}");
        assert!(
            stderr.starts_with("verification failed:"),
            "Python crashed on {what} rather than rejecting it:\n{stderr}"
        );
    }

    pub fn assert_accepts(&self, raw: &RawProof) {
        let output = self.verify(raw);
        assert!(
            output.status.success(),
            "native Python verification failed:\n{}",
            String::from_utf8_lossy(&output.stderr),
        );
        assert_eq!(String::from_utf8_lossy(&output.stdout).trim(), "verification succeeded");
    }
}

impl Drop for PythonStatement {
    fn drop(&mut self) {
        let _ = std::fs::remove_dir_all(&self.directory);
    }
}

/// Both verifiers reject a proof whose announcement or commitment root is not a
/// canonical encoding, one checked against another program's key or a key whose root is
/// altered, and one whose program opening is tampered with.
#[test]
fn test_python_verifier() {
    let (program, _) = super::programs::fibonacci();
    let key = program.verifying_key();
    let (proof, output, stats) = program.prove(&[], Rate::MIN).expect("the run halts");
    // Python reads the RAW proof: same protocol, each query carrying its own
    // full Merkle path instead of one octopus over the batch. A Rust verify
    // expands the wire form, so the pruning is written once.
    let raw = key.verify_to_raw(&output, &proof).expect("honest proof verifies");
    let encoded = bincode::serialize(&proof).expect("serialize proof");
    let statement = PythonStatement::new("tamper", &program, &output);
    let verification_started = Instant::now();
    statement.assert_accepts(&raw);
    let verification_time = verification_started.elapsed();

    let mut malformed_announcement = proof.clone();
    malformed_announcement.stream[0].c1 = 1;
    assert_eq!(
        key.verify(&output, &malformed_announcement),
        Err(CpuError::NonCanonicalSize)
    );
    let mut raw_announcement = raw.clone();
    raw_announcement.stream[0].c1 = 1;
    PythonStatement::assert_rejects(&statement.verify(&raw_announcement), "a noncanonical announcement");

    // Neither a padding row's clock nor a failed row's can end the run.
    let final_clock = leanvm_core::tables::N_TABLES + 1;
    let honest = proof.stream[final_clock].c0;
    for clock in [
        0,
        honest ^ leanvm_core::tables::SEED_CLOCK,
        honest | 1 << leanvm_core::tables::FAIL_BIT,
    ] {
        let mut forged = proof.clone();
        forged.stream[final_clock] = F192::new(clock, 0, 0);
        assert_eq!(key.verify(&output, &forged), Err(CpuError::FinalClock));
        let mut raw_forged = raw.clone();
        raw_forged.stream[final_clock] = F192::new(clock, 0, 0);
        let refused = statement.verify(&raw_forged);
        PythonStatement::assert_rejects(&refused, "a final clock that is not live");
        assert!(String::from_utf8_lossy(&refused.stderr).contains("the final clock is not a live clock"));
    }

    let mut malformed_root = proof.clone();
    // Past the announcement: the table heights, the rate, the final clock.
    let root_offset = leanvm_core::tables::N_TABLES + 2;
    malformed_root.stream[root_offset].c2 = 1;
    assert!(key.verify(&output, &malformed_root).is_err());
    let mut raw_root = raw.clone();
    raw_root.stream[root_offset].c2 = 1;
    PythonStatement::assert_rejects(&statement.verify(&raw_root), "a noncanonical commitment root");

    // A proof is about the program whose key checks it.
    let other = Program::new(
        &Asm::new().li(Reg::A0, 7).exit().finish(),
        Region::TEXT.base(),
        vec![],
        2,
        0,
    )
    .expect("valid instruction program");
    assert!(other.verifying_key().verify(&output, &proof).is_err());
    let python = PythonStatement::new("other", &other, &output).verify(&raw);
    PythonStatement::assert_rejects(&python, "a proof checked against another program's key");

    // The key's root is the program: altering it names another table.
    let mut altered = key.to_bytes();
    altered[0] ^= 1;
    let altered_key = VerifyingKey::from_bytes(&altered).expect("a root is any 32 bytes");
    assert!(altered_key.verify(&output, &proof).is_err());
    statement.write_key(&altered);
    PythonStatement::assert_rejects(&statement.verify(&raw), "a key whose root is altered");
    statement.write_key(&key.to_bytes());

    // The program's opening comes last, on the stream and in the Merkle openings.
    let mut scalar = proof.clone();
    scalar.stream.last_mut().expect("a proof has scalars").c0 ^= 1;
    assert!(matches!(key.verify(&output, &scalar), Err(CpuError::ProgramOpen(_))));
    let mut raw_scalar = raw.clone();
    raw_scalar.stream.last_mut().expect("a proof has scalars").c0 ^= 1;
    PythonStatement::assert_rejects(&statement.verify(&raw_scalar), "a tampered program opening scalar");
    let mut leaf = proof;
    let word = leaf
        .merkle
        .last_mut()
        .and_then(|opening| opening.leaf_data.last_mut())
        .and_then(|words| words.last_mut())
        .expect("the program's opening has a leaf word");
    word.0 ^= 1;
    assert!(matches!(key.verify(&output, &leaf), Err(CpuError::ProgramOpen(_))));
    let mut raw_leaf = raw;
    raw_leaf
        .merkle
        .last_mut()
        .and_then(|opening| opening.leaf_data.last_mut())
        .expect("the program's opening has a leaf word")
        .0 ^= 1;
    PythonStatement::assert_rejects(&statement.verify(&raw_leaf), "a tampered program opening leaf");

    println!(
        "{} instructions; proved {} cycles in {} bytes; Python verified in {:.2?}",
        program.rv().entries().len(),
        stats.cycles,
        encoded.len(),
        verification_time,
    );
}

/// The PCS rate changes WHIR's ladder: how many levels it folds through, how wide a leaf
/// is and how many queries each level takes. Every other cross-check runs at the fastest
/// rate, so the slowest one is checked here, where the two verifiers would otherwise
/// agree only by never being asked.
#[test]
fn the_python_verifier_follows_the_slowest_rate() {
    let (program, _) = super::programs::fibonacci();
    let (proof, output, _) = program.prove(&[], Rate::MAX).expect("the run halts");
    let raw = program
        .verifying_key()
        .verify_to_raw(&output, &proof)
        .expect("honest proof verifies");
    PythonStatement::new("rate", &program, &output).assert_accepts(&raw);
}
