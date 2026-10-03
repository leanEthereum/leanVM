//! Pins `python-verifier/verifier.py` against `leanvm_core::cpu::Program::verify`: the same
//! protocol is written out in Rust and in Python, so any protocol change must land
//! in both, and this is what catches the Python one drifting.

use fiat_shamir::transcript::Proof;
use leanvm_core::cpu::CpuError;
use leanvm_core::pcs::Rate;
use primitives::field::{F64, F192};
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

    /// Run the verifier on `proof`'s own bytes, the ones a Rust verifier receives.
    pub fn verify(&self, proof: &Proof) -> Output {
        self.verify_bytes(&proof.to_bytes())
    }

    /// Run the verifier on `bytes` as a proof, whether or not they encode one.
    pub fn verify_bytes(&self, bytes: &[u8]) -> Output {
        let proof_path = self.directory.join("proof.bin");
        std::fs::write(&proof_path, bytes).expect("write the proof");
        Command::new("python3")
            .arg(Path::new(env!("CARGO_MANIFEST_DIR")).join("../../python-verifier/verifier.py"))
            .arg(&self.bytecode)
            .arg(&self.public)
            .arg(proof_path)
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

    pub fn assert_accepts(&self, proof: &Proof) {
        let output = self.verify(proof);
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

/// Both verifiers reject a malformed proof (bytes that encode none, an announcement or
/// commitment root that is not a canonical encoding, Merkle data that does not
/// authenticate) and agree on everything before that.
#[test]
fn test_python_verifier() {
    let (program, _) = super::programs::fibonacci();
    let (proof, output, stats) = program.prove(&[], Rate::MIN).expect("the run halts");
    program.verify(&output, &proof).expect("honest proof verifies");
    let bytes = proof.to_bytes();
    let statement = PythonStatement::new("tamper", &program, &output);
    let verification_started = Instant::now();
    statement.assert_accepts(&proof);
    let verification_time = verification_started.elapsed();

    // Python decodes the bytes itself, and refuses what `Proof::from_bytes` refuses: a proof
    // cut short, one claiming a longer stream than it holds, one with bytes past its end.
    let truncated = &bytes[..bytes.len() - 1];
    let mut overlong = bytes.clone();
    overlong[..8].copy_from_slice(&u64::MAX.to_le_bytes());
    let trailing = [bytes.as_slice(), &[0]].concat();
    for (what, reason, malformed) in [
        ("a truncated proof", "the proof is truncated", truncated),
        ("an overlong stream", "the proof is truncated", &overlong),
        ("a proof with trailing bytes", "the proof has trailing bytes", &trailing),
    ] {
        assert!(Proof::from_bytes(malformed).is_none(), "Rust decoded {what}");
        let refused = statement.verify_bytes(malformed);
        PythonStatement::assert_rejects(&refused, what);
        assert!(String::from_utf8_lossy(&refused.stderr).contains(reason), "{what}");
    }

    let mut malformed_announcement = proof.clone();
    malformed_announcement.stream[0].c1 = 1;
    assert_eq!(
        program.verify(&output, &malformed_announcement),
        Err(CpuError::NonCanonicalSize)
    );
    PythonStatement::assert_rejects(
        &statement.verify(&malformed_announcement),
        "a noncanonical announcement",
    );

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
        let refused = statement.verify(&forged);
        PythonStatement::assert_rejects(&refused, "a final clock that is not live");
        assert!(String::from_utf8_lossy(&refused.stderr).contains("the final clock is not a live clock"));
    }

    let mut malformed_root = proof.clone();
    // Past the announcement: the table heights, the rate, the final clock.
    let root_offset = leanvm_core::tables::N_TABLES + 2;
    malformed_root.stream[root_offset].c2 = 1;
    assert!(program.verify(&output, &malformed_root).is_err());
    PythonStatement::assert_rejects(&statement.verify(&malformed_root), "a noncanonical commitment root");

    // The L0 phase's Merkle data as the proof stores it: each row only its leaf image's tail,
    // the committed lanes, and one octopus holding each sibling the queried paths need once.
    type Tamper = fn(&mut Proof);
    let merkle_tampers: [(&str, &str, Tamper); 5] = [
        ("a tampered sibling", "Merkle root mismatch", |p| {
            p.merkle[0].sibling_hashes[0][0] ^= 1;
        }),
        ("a tampered leaf tail word", "Merkle root mismatch", |p| {
            p.merkle[0].leaf_data[0].last_mut().expect("a row").0 ^= 1;
        }),
        ("a row that stores a zero of its prefix", "the wrong width", |p| {
            p.merkle[0].leaf_data[0].insert(0, F64::ZERO);
        }),
        ("an octopus missing a sibling", "missing a sibling", |p| {
            p.merkle[0].sibling_hashes.pop();
        }),
        ("an octopus with a sibling left over", "siblings left over", |p| {
            p.merkle[0].sibling_hashes.push([0; 32]);
        }),
    ];
    for (what, reason, tamper) in merkle_tampers {
        let mut tampered = proof.clone();
        tamper(&mut tampered);
        assert!(program.verify(&output, &tampered).is_err(), "Rust accepted {what}");
        let refused = statement.verify(&tampered);
        PythonStatement::assert_rejects(&refused, what);
        assert!(String::from_utf8_lossy(&refused.stderr).contains(reason), "{what}");
    }

    // A decoded table is RISC-V only if it says so: one whose first entry writes `x0`
    // is refused before anything is verified.
    let table = std::fs::read(&statement.bytecode).expect("read bytecode");
    let (ad_slot, entries) = (6, table.len() / 8 / 16);
    let mut writes_x0 = table.clone();
    writes_x0[8 * ad_slot * entries..][..8].copy_from_slice(&0u64.to_le_bytes());
    std::fs::write(&statement.bytecode, writes_x0).expect("write bytecode");
    let python = statement.verify(&proof);
    PythonStatement::assert_rejects(&python, "a table that writes x0");
    assert!(
        String::from_utf8_lossy(&python.stderr).contains("misnames a register"),
        "Python refused a table that writes x0 for the wrong reason"
    );
    // A load reads no `rs2`, a store writes no `rd`, and a doubleword one has no flags: their tables hold those fields
    // at constants, `x0`, the sink and zero, so an entry naming another register or a flag is refused.
    for (class, slot, reason) in [
        (leanvm_core::rv::Class::Load, 5, "reads an rs2"),
        (leanvm_core::rv::Class::Store, 6, "writes an rd"),
        (leanvm_core::rv::Class::Ld, 5, "reads an rs2"),
        (leanvm_core::rv::Class::Sd, 6, "writes an rd"),
        (leanvm_core::rv::Class::Ld, 3, "flags are not its class's"),
    ] {
        // The class tag `g^t`, which is `2^t` since `g = x`.
        let tag = 1u64 << leanvm_core::tables::table_of(class).expect("the class has a table");
        let mut malformed = table.clone();
        for (slot, value) in [(2, tag), (3, 0), (slot, 1)] {
            malformed[8 * slot * entries..][..8].copy_from_slice(&value.to_le_bytes());
        }
        std::fs::write(&statement.bytecode, malformed).expect("write malformed register");
        let refused = statement.verify(&proof);
        PythonStatement::assert_rejects(&refused, reason);
        assert!(String::from_utf8_lossy(&refused.stderr).contains(reason), "{reason}");
    }
    // Setting an exit selector on an ordinary instruction is a malformed public table.
    let mut forged_exit = table.clone();
    forged_exit[8 * leanvm_core::tables::EXIT_SLOT * entries..][..8].copy_from_slice(&1u64.to_le_bytes());
    std::fs::write(&statement.bytecode, forged_exit).expect("write forged exit");
    let refused = statement.verify(&proof);
    PythonStatement::assert_rejects(&refused, "an ordinary instruction marked as an exit");
    assert!(String::from_utf8_lossy(&refused.stderr).contains("an exit entry is not ECALL"));
    let branch = leanvm_core::rv::Alu::SUB | leanvm_core::rv::Alu::BR_EQ;
    let always = leanvm_core::rv::Alu::ALWAYS;
    let jalr = leanvm_core::rv::Alu::CLEAR_BIT0;
    for (flags, dt, link, indirect) in [
        (branch, 0x44, 1, 1),
        (always, 0, 0, 0),
        (0, 0x44, 0, 0),
        (0, 0, 1, 0),
        (0, 0, 0, 1),
        (jalr, 0, 0, 1),
        (jalr, 0, 1, 0),
        (jalr, 0x44, 1, 1),
        (branch, 0, 1, 0),
        (branch, 0, 0, 1),
        (always, 0x44, 1, 1),
    ] {
        let mut malformed = table.clone();
        for (slot, value) in [(3, flags), (9, dt), (10, link), (11, indirect)] {
            malformed[8 * slot * entries..][..8].copy_from_slice(&value.to_le_bytes());
        }
        std::fs::write(&statement.bytecode, malformed).expect("write malformed control flow");
        let refused = statement.verify(&proof);
        PythonStatement::assert_rejects(&refused, "malformed control flow");
        assert!(String::from_utf8_lossy(&refused.stderr).contains("invalid control flow"));
    }
    std::fs::write(&statement.bytecode, table).expect("restore bytecode");
    let control_shapes = Command::new("python3")
        .arg("-c")
        .arg(
            r#"import runpy, sys
from pathlib import Path
v = runpy.run_path(sys.argv[1])
data = Path(sys.argv[2]).read_bytes()
words = [v['K'](int.from_bytes(data[i:i+8], 'little')) for i in range(0, len(data), 8)]
v['check_bytecode'](words)
n = len(words) // 16
for flags, link, jalr in [(1 << 14, 1, 0), (1 | (1 << 8), 0, 0), (1 << 7, 1, 1)]:
    candidate = words.copy()
    for slot, value in [(3, flags), (9, 0), (10, link), (11, jalr)]:
        candidate[slot * n] = v['K'](value)
    v['check_bytecode'](candidate)
"#,
        )
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
        bytes.len(),
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
    program.verify(&output, &proof).expect("honest proof verifies");
    PythonStatement::new("rate", &program, &output).assert_accepts(&proof);
}
