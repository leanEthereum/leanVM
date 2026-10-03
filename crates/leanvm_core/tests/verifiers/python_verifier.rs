//! Pins `python-verifier/verifier.py` against `leanvm_core::cpu::Program::verify`: the same
//! protocol is written out in Rust and in Python, so any protocol change must land
//! in both, and this is what catches the Python one drifting.

use fiat_shamir::transcript::RawProof;
use leanvm_core::cpu::CpuError;
use leanvm_core::pcs::Rate;
use primitives::field::F192;
use std::path::{Path, PathBuf};
use std::process::{Command, Output};
use std::time::Instant;

/// One statement laid out the way the Python verifier takes it: the bytecode
/// multilinear, then what else is public (where the run starts, RAM's size and first
/// words, the output), not a structured program.
pub struct PythonStatement {
    directory: PathBuf,
    bytecode: PathBuf,
    public: PathBuf,
}

impl PythonStatement {
    pub fn new(tag: &str, program: &leanvm_core::cpu::Program, output: &[u64; 4]) -> Self {
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
        let rv = program.rv();
        let table: Vec<u8> = leanvm_core::cpu::Lookup::Bytecode
            .table(rv)
            .iter()
            .flat_map(|w| w.0.to_le_bytes())
            .collect();
        std::fs::write(&statement.bytecode, &table).expect("write bytecode");
        let public: Vec<u8> = [
            rv.entry_pc(),
            rv.log_ram() as u64,
            rv.log_advice() as u64,
            rv.image().len() as u64,
        ]
        .iter()
        .chain(rv.image())
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
    let (proof, output, stats) = program.prove(&[], Rate::MIN).expect("the run halts");
    // Python reads the RAW proof: same protocol, each query carrying its own
    // full Merkle path instead of one octopus over the batch. A Rust verify
    // expands the wire form, so the pruning is written once.
    let raw = program.verify_to_raw(&output, &proof).expect("honest proof verifies");
    let encoded = bincode::serialize(&proof).expect("serialize proof");
    let statement = PythonStatement::new("tamper", &program, &output);
    let verification_started = Instant::now();
    statement.assert_accepts(&raw);
    let verification_time = verification_started.elapsed();

    let mut malformed_announcement = proof.clone();
    malformed_announcement.stream[0].c1 = 1;
    assert_eq!(
        program.verify(&output, &malformed_announcement),
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
        assert_eq!(program.verify(&output, &forged), Err(CpuError::FinalClock));
        let mut raw_forged = raw.clone();
        raw_forged.stream[final_clock] = F192::new(clock, 0, 0);
        let refused = statement.verify(&raw_forged);
        PythonStatement::assert_rejects(&refused, "a final clock that is not live");
        assert!(String::from_utf8_lossy(&refused.stderr).contains("the final clock is not a live clock"));
    }

    let mut malformed_root = proof;
    // Past the announcement: the table heights, the rate, the final clock.
    let root_offset = leanvm_core::tables::N_TABLES + 2;
    malformed_root.stream[root_offset].c2 = 1;
    assert!(program.verify(&output, &malformed_root).is_err());
    let mut raw_root = raw.clone();
    raw_root.stream[root_offset].c2 = 1;
    PythonStatement::assert_rejects(&statement.verify(&raw_root), "a noncanonical commitment root");

    // A decoded table is RISC-V only if it says so: one whose first entry writes `x0`
    // is refused before anything is verified.
    let table = std::fs::read(&statement.bytecode).expect("read bytecode");
    let (ad_slot, entries) = (6, table.len() / 8 / 16);
    let mut writes_x0 = table.clone();
    writes_x0[8 * ad_slot * entries..][..8].copy_from_slice(&0u64.to_le_bytes());
    std::fs::write(&statement.bytecode, writes_x0).expect("write bytecode");
    let python = statement.verify(&raw);
    PythonStatement::assert_rejects(&python, "a table that writes x0");
    assert!(
        String::from_utf8_lossy(&python.stderr).contains("misnames a register"),
        "Python refused a table that writes x0 for the wrong reason"
    );
    // A load and a jump read no `rs2`, a store and a branch write no `rd`, a branch has no immediate, and a doubleword
    // load or store has no flags: their tables hold those fields at constants, `x0`, the sink and zero, so an entry
    // naming another value is refused. The other fields are set to the class's legal values, so that this is the first
    // rule broken.
    use leanvm_core::rv::{Branch, Class, Jump};
    // The class tag `g^t`, which is `2^t` since `g = x`.
    let tag = |class| 1u64 << leanvm_core::tables::table_of(class).expect("the class has a table");
    for (class, fields, reason) in [
        (Class::Load, vec![(3, 0), (5, 1)], "reads an rs2"),
        (Class::Store, vec![(3, 0), (6, 1)], "writes an rd"),
        (Class::Ld, vec![(3, 0), (5, 1)], "reads an rs2"),
        (Class::Sd, vec![(3, 0), (6, 1)], "writes an rd"),
        (Class::Ld, vec![(3, 1)], "flags are not its class's"),
        (Class::Jump, vec![(3, Jump::DIRECT), (10, 1), (5, 1)], "reads an rs2"),
        (Class::Branch, vec![(3, Branch::EQ), (6, 1)], "writes an rd"),
        (
            Class::Branch,
            vec![(3, Branch::EQ), (6, 32), (7, 4)],
            "has an immediate",
        ),
    ] {
        let mut malformed = table.clone();
        for (slot, value) in std::iter::once((2, tag(class))).chain(fields) {
            malformed[8 * slot * entries..][..8].copy_from_slice(&value.to_le_bytes());
        }
        std::fs::write(&statement.bytecode, malformed).expect("write malformed register");
        let refused = statement.verify(&raw);
        PythonStatement::assert_rejects(&refused, reason);
        assert!(String::from_utf8_lossy(&refused.stderr).contains(reason), "{reason}");
    }
    // Setting an exit selector on an ordinary instruction is a malformed public table.
    let mut forged_exit = table.clone();
    forged_exit[8 * leanvm_core::tables::EXIT_SLOT * entries..][..8].copy_from_slice(&1u64.to_le_bytes());
    std::fs::write(&statement.bytecode, forged_exit).expect("write forged exit");
    let refused = statement.verify(&raw);
    PythonStatement::assert_rejects(&refused, "an ordinary instruction marked as an exit");
    assert!(String::from_utf8_lossy(&refused.stderr).contains("an exit entry is not ECALL"));
    // Control shapes a class does not have: a branch that links or jumps to a computed target, a direct jump that
    // does not link, `JALR` without its link or its indirection, and anything else moving control at all.
    let (add, branch, jump) = (tag(Class::Add), tag(Class::Branch), tag(Class::Jump));
    for (class, flags, dt, link, indirect) in [
        (branch, Branch::EQ, 0x44, 1, 1),
        (branch, Branch::EQ, 0, 1, 0),
        (branch, Branch::EQ, 0, 0, 1),
        (jump, Jump::DIRECT, 0, 0, 0),
        (jump, Jump::DIRECT, 0x44, 1, 1),
        (jump, 0, 0, 0, 1),
        (jump, 0, 0, 1, 0),
        (jump, 0, 0x44, 1, 1),
        (add, 0, 0x44, 0, 0),
        (add, 0, 0, 1, 0),
        (add, 0, 0, 0, 1),
    ] {
        let mut malformed = table.clone();
        for (slot, value) in [(2, class), (3, flags), (9, dt), (10, link), (11, indirect)] {
            malformed[8 * slot * entries..][..8].copy_from_slice(&value.to_le_bytes());
        }
        std::fs::write(&statement.bytecode, malformed).expect("write malformed control flow");
        let refused = statement.verify(&raw);
        PythonStatement::assert_rejects(&refused, "malformed control flow");
        assert!(String::from_utf8_lossy(&refused.stderr).contains("invalid control flow"));
    }
    std::fs::write(&statement.bytecode, table).expect("restore bytecode");
    // The legal shapes pass: a direct jump, a branch, `JALR`, each with the sink as `rd` and no `rs2` or immediate.
    let control_shapes = Command::new("python3")
        .arg("-c")
        .arg(format!(
            r#"import runpy, sys
from pathlib import Path
v = runpy.run_path(sys.argv[1])
data = Path(sys.argv[2]).read_bytes()
words = [v['K'](int.from_bytes(data[i:i+8], 'little')) for i in range(0, len(data), 8)]
v['check_bytecode'](words)
n = len(words) // 16
for tag, flags, link, jalr in [({jump}, {direct}, 1, 0), ({branch}, {eq}, 0, 0), ({jump}, 0, 1, 1)]:
    candidate = words.copy()
    for slot, value in [(2, tag), (3, flags), (5, 0), (6, 32), (7, 0), (9, 0), (10, link), (11, jalr)]:
        candidate[slot * n] = v['K'](value)
    v['check_bytecode'](candidate)
"#,
            direct = Jump::DIRECT,
            eq = Branch::EQ,
        ))
        .arg(Path::new(env!("CARGO_MANIFEST_DIR")).join("../../python-verifier/verifier.py"))
        .arg(&statement.bytecode)
        .output()
        .expect("validate legal control shapes");
    assert!(
        control_shapes.status.success(),
        "{}",
        String::from_utf8_lossy(&control_shapes.stderr)
    );

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
    let raw = program.verify_to_raw(&output, &proof).expect("honest proof verifies");
    PythonStatement::new("rate", &program, &output).assert_accepts(&raw);
}
