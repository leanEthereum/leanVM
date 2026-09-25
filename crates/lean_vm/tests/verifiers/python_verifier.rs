//! Pins `python-verifier/verifier.py` against `lean_vm::cpu::verify`: the same
//! protocol is written out in Rust and in Python, so any protocol change must land
//! in both, and this is what catches the Python one drifting.

use fiat_shamir::transcript::RawProof;
use lean_vm::cpu::{prove, verify, verify_to_raw};
use std::path::{Path, PathBuf};
use std::process::{Command, Output};
use std::time::Instant;

/// One statement laid out the way the Python verifier takes it: the bytecode
/// multilinear, then what else is public (where the run starts, RAM's size and first
/// words, the input, the output), not a structured program.
pub struct PythonStatement {
    directory: PathBuf,
    bytecode: PathBuf,
    public: PathBuf,
}

impl PythonStatement {
    pub fn new(tag: &str, program: &lean_vm::cpu::Program, input: &[u64; 4], output: &[u64; 4]) -> Self {
        // One directory per statement, not per tag: the tests share a process, so two of
        // them naming the same tag would write each other's files and check the wrong
        // proof, which python would ACCEPT, silently proving nothing.
        static NEXT: std::sync::atomic::AtomicUsize = std::sync::atomic::AtomicUsize::new(0);
        let unique = NEXT.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
        let directory =
            std::env::temp_dir().join(format!("leanvm-python-verifier-{tag}-{}-{unique}", std::process::id()));
        std::fs::create_dir_all(&directory).expect("create test directory");
        let statement = Self {
            bytecode: directory.join("bytecode.bin"),
            public: directory.join("public.bin"),
            directory,
        };
        let rv = &program.rv;
        let table: Vec<u8> = lean_vm::cpu::layout::bytecode_table(rv)
            .iter()
            .flat_map(|w| w.0.to_le_bytes())
            .collect();
        std::fs::write(&statement.bytecode, &table).expect("write bytecode");
        let public: Vec<u8> = [
            rv.entry_pc,
            rv.log_ram as u64,
            rv.log_advice as u64,
            rv.image.len() as u64,
        ]
        .iter()
        .chain(&rv.image)
        .chain(input)
        .chain(output)
        .flat_map(|w| w.to_le_bytes())
        .collect();
        std::fs::write(&statement.public, &public).expect("write the public words");
        statement
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
            .arg(&self.bytecode)
            .arg(&self.public)
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
/// canonical encoding, and agree on everything before that.
#[test]
fn test_python_verifier() {
    let (program, _) = super::programs::fibonacci();
    let input = [0; 4];
    let (proof, output, stats) = prove(&program, input, &[], 1).expect("the run halts");
    // Python reads the RAW proof: same protocol, each query carrying its own
    // full Merkle path instead of one octopus over the batch. A Rust verify
    // expands the wire form, so the pruning is written once.
    let raw = verify_to_raw(&program, &input, &output, &proof).expect("honest proof verifies");
    let encoded = bincode::serialize(&proof).expect("serialize proof");
    let statement = PythonStatement::new("tamper", &program, &input, &output);
    let verification_started = Instant::now();
    statement.assert_accepts(&raw);
    let verification_time = verification_started.elapsed();

    let mut malformed_announcement = proof.clone();
    malformed_announcement.stream[0].c1 = 1;
    assert!(verify(&program, &input, &output, &malformed_announcement).is_err());
    let mut raw_announcement = raw.clone();
    raw_announcement.stream[0].c1 = 1;
    PythonStatement::assert_rejects(&statement.verify(&raw_announcement), "a noncanonical announcement");

    let mut malformed_root = proof.clone();
    // Past the announcement: the table heights, the rate, the final clock.
    let root_offset = lean_vm::tables::N_TABLES + 2;
    malformed_root.stream[root_offset].c2 = 1;
    assert!(verify(&program, &input, &output, &malformed_root).is_err());
    let mut raw_root = raw.clone();
    raw_root.stream[root_offset].c2 = 1;
    PythonStatement::assert_rejects(&statement.verify(&raw_root), "a noncanonical commitment root");

    // A decoded table is RISC-V only if it says so: one whose first entry writes `x0`
    // is refused before anything is verified.
    let table = std::fs::read(&statement.bytecode).expect("read bytecode");
    let (ad_slot, entries) = (7, table.len() / 8 / 16);
    let mut writes_x0 = table.clone();
    writes_x0[8 * ad_slot * entries..][..8].copy_from_slice(&0u64.to_le_bytes());
    std::fs::write(&statement.bytecode, writes_x0).expect("write bytecode");
    let python = statement.verify(&raw);
    PythonStatement::assert_rejects(&python, "a table that writes x0");
    assert!(
        String::from_utf8_lossy(&python.stderr).contains("misnames a register"),
        "Python refused a table that writes x0 for the wrong reason"
    );
    std::fs::write(&statement.bytecode, table).expect("restore bytecode");

    println!(
        "{} instructions; proved {} cycles in {} bytes; Python verified in {:.2?}",
        program.rv.entries.len(),
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
    let input = [0; 4];
    let rate = lean_vm::pcs::MAX_LOG_INV_RATE;
    let (proof, output, _) = prove(&program, input, &[], rate).expect("the run halts");
    let raw = verify_to_raw(&program, &input, &output, &proof).expect("honest proof verifies");
    PythonStatement::new("rate", &program, &input, &output).assert_accepts(&raw);
}
