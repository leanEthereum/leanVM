//! Pins `python-verifier/verifier.py` against `leanvm_core::Program::verify`: the same
//! protocol is written out in Rust and in Python, so any protocol change must land
//! in both, and this is what catches the Python one drifting.

use fiat_shamir::transcript::RawProof;
use leanvm_core::{Alu, Class, Clock, CpuError, EXIT_SLOT, Lookup, PerTable, Program, Rate, Region, TableId};
use primitives::field::{F64, F192};
use std::path::{Path, PathBuf};
use std::process::{Command, Output};
use std::sync::atomic::{AtomicUsize, Ordering};
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
    pub fn new(tag: &str, program: &Program, output: &[u64; 4]) -> Self {
        // One directory per statement, not per tag: the tests share a process, so two of
        // them naming the same tag would write each other's files and check the wrong
        // proof, which python would ACCEPT, silently proving nothing.
        static NEXT: AtomicUsize = AtomicUsize::new(0);
        let unique = NEXT.fetch_add(1, Ordering::Relaxed);
        let directory =
            std::env::temp_dir().join(format!("leanvm-python-verifier-{tag}-{}-{unique}", std::process::id()));
        std::fs::create_dir_all(&directory).expect("create test directory");
        let statement = Self {
            bytecode: directory.join("bytecode.bin"),
            public: directory.join("public.bin"),
            directory,
        };
        let rv = program.rv();
        let table: Vec<u8> = Lookup::Bytecode
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
        self.verify_with(raw, None)
    }

    /// The verifier run through `prelude` when one is given: a Python script that receives the verifier's path then its
    /// arguments, and may wrap the verifier's functions before calling its `main`.
    pub fn verify_with(&self, raw: &RawProof, prelude: Option<&str>) -> Output {
        self.command(raw, prelude).output().expect("run native Python verifier")
    }

    /// The claims Python's `verify_core` leaves on `raw`, as it renders them, once it
    /// has checked them.
    pub fn deferred(&self, raw: &RawProof) -> String {
        let output = self
            .command(raw, None)
            .arg("--deferred")
            .output()
            .expect("run native Python verifier");
        let stdout = String::from_utf8_lossy(&output.stdout);
        assert!(
            output.status.success(),
            "native Python verification failed:\n{}",
            String::from_utf8_lossy(&output.stderr),
        );
        let claims = stdout.trim().strip_suffix("verification succeeded");
        claims.expect("the verdict follows the claims").trim().to_owned()
    }

    fn command(&self, raw: &RawProof, prelude: Option<&str>) -> Command {
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
        let mut command = Command::new("python3");
        if let Some(prelude) = prelude {
            command.arg("-c").arg(prelude);
        }
        command
            .arg(Path::new(env!("CARGO_MANIFEST_DIR")).join("../../python-verifier/verifier.py"))
            .arg(&self.bytecode)
            .arg(&self.public)
            .arg(stream_path)
            .arg(openings_path);
        command
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
    let encoded = bincode::serialize(&proof.0).expect("serialize proof");
    let statement = PythonStatement::new("tamper", &program, &output);
    let verification_started = Instant::now();
    statement.assert_accepts(&raw);
    let verification_time = verification_started.elapsed();

    let mut malformed_announcement = proof.clone();
    malformed_announcement.0.stream[0].c1 = 1;
    assert_eq!(
        program.verify(output.into(), &malformed_announcement),
        Err(CpuError::NonCanonicalSize.into())
    );
    let mut raw_announcement = raw.clone();
    raw_announcement.stream[0].c1 = 1;
    PythonStatement::assert_rejects(&statement.verify(&raw_announcement), "a noncanonical announcement");

    // Neither a padding row's clock nor a failed row's can end the run.
    //
    // A padding row of the exit pushes the exit marker at its clock, zero, which only a final clock zero would meet.
    let final_clock = leanvm_core::N_TABLES + 1;
    let honest = proof.0.stream[final_clock].c0;
    for clock in [0, honest ^ Clock::SEED_CLOCK, honest | 1 << Clock::FAIL_BIT] {
        let mut forged = proof.clone();
        forged.0.stream[final_clock] = F192::new(clock, 0, 0);
        assert_eq!(program.verify(output.into(), &forged), Err(CpuError::FinalClock.into()));
        let mut raw_forged = raw.clone();
        raw_forged.stream[final_clock] = F192::new(clock, 0, 0);
        let refused = statement.verify(&raw_forged);
        PythonStatement::assert_rejects(&refused, "a final clock that is not live");
        assert!(String::from_utf8_lossy(&refused.stderr).contains("the final clock is not a live clock"));
    }

    let mut malformed_root = proof;
    // Past the announcement: the table heights, the rate, the final clock.
    let root_offset = leanvm_core::N_TABLES + 2;
    malformed_root.0.stream[root_offset].c2 = 1;
    assert!(program.verify(output.into(), &malformed_root).is_err());
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
    // A load reads no `rs2`, a store writes no `rd`, and a doubleword one has no flags: their tables hold those fields
    // at constants, `x0`, the sink and zero, so an entry naming another register or a flag is refused.
    for (class, slot, reason) in [
        (Class::Load, 5, "reads an rs2"),
        (Class::Store, 6, "writes an rd"),
        (Class::Ld, 5, "reads an rs2"),
        (Class::Sd, 6, "writes an rd"),
        (Class::Ld, 3, "flags are not its class's"),
    ] {
        // The class tag `g^t`, which is `2^t` since `g = x`.
        let tag = 1u64 << TableId::of(class).expect("the class has a table").index();
        let mut malformed = table.clone();
        for (slot, value) in [(2, tag), (3, 0), (slot, 1)] {
            malformed[8 * slot * entries..][..8].copy_from_slice(&value.to_le_bytes());
        }
        std::fs::write(&statement.bytecode, malformed).expect("write malformed register");
        let refused = statement.verify(&raw);
        PythonStatement::assert_rejects(&refused, reason);
        assert!(String::from_utf8_lossy(&refused.stderr).contains(reason), "{reason}");
    }
    // Setting an exit selector on an ordinary instruction is a malformed public table.
    let mut forged_exit = table.clone();
    forged_exit[8 * EXIT_SLOT * entries..][..8].copy_from_slice(&1u64.to_le_bytes());
    std::fs::write(&statement.bytecode, forged_exit).expect("write forged exit");
    let refused = statement.verify(&raw);
    PythonStatement::assert_rejects(&refused, "an ordinary instruction marked as an exit");
    assert!(String::from_utf8_lossy(&refused.stderr).contains("an exit entry is not ECALL"));
    // A jump's shape is its flags': only a branch or a `jal` has an offset, and a `jal` links `pc + 4` as a constant
    // added to `x0`. Entry 0's fields are set in full, so each case breaks that rule alone.
    let alu = 1u64 << TableId::ALU.index();
    let link = Region::TEXT.base() + 4;
    for (what, fields) in [
        (
            "an addition with an offset",
            [(2, alu), (3, 0), (4, 0), (5, 0), (7, 0), (9, 0x44)],
        ),
        (
            "a jal reading a register",
            [(2, alu), (3, Alu::ALWAYS), (4, 1), (5, 0), (7, link), (9, 0x44)],
        ),
        (
            "a jal linking another address",
            [(2, alu), (3, Alu::ALWAYS), (4, 0), (5, 0), (7, link + 4), (9, 0x44)],
        ),
        (
            "a jalr with an offset",
            [
                (2, alu),
                (3, Alu::INDIRECT | Alu::ALWAYS),
                (4, 0),
                (5, 0),
                (7, 0),
                (9, 0x44),
            ],
        ),
    ] {
        let mut malformed = table.clone();
        for (slot, value) in fields {
            malformed[8 * slot * entries..][..8].copy_from_slice(&value.to_le_bytes());
        }
        std::fs::write(&statement.bytecode, malformed).expect("write malformed control flow");
        let refused = statement.verify(&raw);
        PythonStatement::assert_rejects(&refused, what);
        assert!(
            String::from_utf8_lossy(&refused.stderr).contains("invalid control flow"),
            "{what}"
        );
    }
    std::fs::write(&statement.bytecode, &table).expect("restore bytecode");
    // The legal shapes of entry 0: a `jal` to `pc + 4`, a branch with an offset, a `jalr`.
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
for fields in [[(2, {alu}), (3, {always}), (4, 0), (5, 0), (7, {link}), (9, 0)], [(2, {alu}), (3, {branch}), (9, 0x44)], [(2, {alu}), (3, {indirect}), (5, 0), (9, 0)]]:
    candidate = words.copy()
    for slot, value in fields:
        candidate[slot * n] = v['K'](value)
    v['check_bytecode'](candidate)
"#,
            always = Alu::ALWAYS,
            branch = Alu::SUB | Alu::BR_EQ,
            indirect = Alu::INDIRECT | Alu::ALWAYS,
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

// What Rust refuses when it builds a program or reads a pruned opening, Python refuses on the files it is handed.
#[test]
fn the_python_verifier_refuses_what_rust_cannot_express() {
    let (program, _) = super::programs::fibonacci();
    let (proof, output, _) = program.prove(&[], Rate::MIN).expect("the run halts");
    let raw = program.verify_to_raw(&output, &proof).expect("honest proof verifies");
    let statement = PythonStatement::new("shape", &program, &output);
    let refuses = |what: &str, reason: &str| {
        let refused = statement.verify(&raw);
        PythonStatement::assert_rejects(&refused, what);
        assert!(String::from_utf8_lossy(&refused.stderr).contains(reason), "{what}");
    };

    // The entry point is the first public word: misaligned, below the text, at the halt slot and past it.
    let public = std::fs::read(&statement.public).expect("read the public words");
    let (text_base, halt_pc) = (Region::TEXT.base(), program.rv().halt_pc());
    for entry_pc in [program.rv().entry_pc() + 2, text_base - 4, halt_pc, halt_pc + 4] {
        let mut forged = public.clone();
        forged[..8].copy_from_slice(&entry_pc.to_le_bytes());
        std::fs::write(&statement.public, forged).expect("write the public words");
        refuses(
            "an entry point off the text",
            "the entry pc is not an instruction of the text",
        );
    }
    std::fs::write(&statement.public, public).expect("restore the public words");

    // The padding entry before the halt slot is illegal: its flags, `ad`, `pc4` and exit selector each have one value.
    let table = std::fs::read(&statement.bytecode).expect("read bytecode");
    let entries = table.len() / 8 / 16;
    let write = |slot: usize, entry: usize, value: u64| {
        let mut forged = table.clone();
        forged[8 * (slot * entries + entry)..][..8].copy_from_slice(&value.to_le_bytes());
        std::fs::write(&statement.bytecode, forged).expect("write bytecode");
    };
    for slot in [3, 6, 8, EXIT_SLOT] {
        write(slot, entries - 2, 1);
        refuses(
            "a noncanonical illegal entry",
            "an illegal entry is not in its one form",
        );
    }
    // A halt slot tagged as an ALU entry is otherwise a well-formed `addi` to the sink.
    let alu = 1u64 << TableId::ALU.index();
    write(2, entries - 1, alu);
    refuses("a readable halt slot", "the halt slot is not an illegal entry");
    std::fs::write(&statement.bytecode, table).expect("restore bytecode");

    // The first opening is a level-0 query, whose leaf leads with the lanes the stack never fills.
    let mut forged = raw.clone();
    forged.merkle[0].leaf_data[0] = F64(1);
    let refused = statement.verify(&forged);
    PythonStatement::assert_rejects(&refused, "a nonzero absent lane");
    assert!(String::from_utf8_lossy(&refused.stderr).contains("a leaf's absent lanes are not zero"));
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

/// Every ring-switched claim joins the opening's one family through its slices: both verifiers reject a moved slice of
/// the first, a middle and the last flock circuit, the last circuit's form value, a moved multiplicity bit, and a moved
/// register bit of the last table and of the first, a table the bus point settles. Python also rejects a family target
/// off by one and a family combined by the wrong challenge.
#[test]
fn both_verifiers_bind_every_circuits_slices() {
    let (program, _) = super::programs::fibonacci();
    let (proof, output, _) = program.prove(&[], Rate::MIN).expect("the run halts");
    let raw = program.verify_to_raw(&output, &proof).expect("honest proof verifies");
    assert_eq!(raw.stream, proof.0.stream, "the raw proof's scalars are the proof's");
    let statement = PythonStatement::new("slices", &program, &output);

    // Where the table sumcheck (ending on the multiplicity bits) and the batched reductions (ending on each circuit's
    // 64 slices and its form's value, in circuit order) stop reading the stream, as the Python verifier reads it.
    let prelude = r#"import runpy, sys
v = runpy.run_path(sys.argv[1])
g = v['main'].__globals__
def recorded(name):
    inner = g[name]
    def wrapped(*args):
        out = inner(*args)
        print(name, args[-1].stream_offset)
        return out
    g[name] = wrapped
recorded('table_sumcheck')
recorded('verify_flock')
Table = g['Table']
read_registers = Table.read_registers
def read_recorded(table, transcript):
    out = read_registers(table, transcript)
    print('register_bits', transcript.stream_offset - len(out[1]))
    return out
Table.read_registers = read_recorded
sys.exit(v['main'](sys.argv[2:]))
"#;
    let traced = statement.verify_with(&raw, Some(prelude));
    assert!(traced.status.success(), "{}", String::from_utf8_lossy(&traced.stderr));
    let stdout = String::from_utf8_lossy(&traced.stdout);
    let ends = |name: &str| -> Vec<usize> {
        (stdout.lines())
            .filter_map(|line| line.strip_prefix(name)?.trim().parse().ok())
            .collect()
    };
    let n = leanvm_core::N_FLOCKS;
    let [flock_end] = ends("verify_flock")[..] else {
        panic!("one batched reduction")
    };
    let [bits_end] = ends("table_sumcheck")[..] else {
        panic!("one table sumcheck")
    };
    let slices = |f: usize| flock_end - (n - f) * 65;
    // The announced heights lead the stream; the last table's register bits end right before the multiplicity bits.
    let taus = PerTable::from_fn(|t: TableId| proof.0.stream[t.index()].c0 as usize);
    let register_end = bits_end - Lookup::Bytecode.multiplicity_bits(&taus);
    // The first table's register bits, the only columns of a settled table the table sumcheck sends, come first.
    let settled_bits = ends("register_bits")[0];
    for at in [
        slices(0),
        slices(n / 2) + 7,
        slices(n - 1) + 63,
        flock_end - 1,
        bits_end - 1,
        register_end - 1,
        settled_bits,
    ] {
        let mut forged = proof.clone();
        forged.0.stream[at] += F192::ONE;
        assert!(
            program.verify(output.into(), &forged).is_err(),
            "Rust accepted a moved scalar at {at}"
        );
        let mut raw_forged = raw.clone();
        raw_forged.stream[at] += F192::ONE;
        PythonStatement::assert_rejects(&statement.verify(&raw_forged), "a moved slice, form value or bit");
    }

    let shifted = r#"import runpy, sys
v = runpy.run_path(sys.argv[1])
g = v['main'].__globals__
ring_switch = g['ring_switch']
def shifted(claims, transcript):
    weight, target = ring_switch(claims, transcript)
    return weight, target + g['ONE']
g['ring_switch'] = shifted
sys.exit(v['main'](sys.argv[2:]))
"#;
    PythonStatement::assert_rejects(&statement.verify_with(&raw, Some(shifted)), "a wrong family target");

    let wrong_gamma = r#"import runpy, sys
v = runpy.run_path(sys.argv[1])
g = v['main'].__globals__
ring_switch, powers = g['ring_switch'], g['powers']
def wrong_gamma(claims, transcript):
    g['powers'] = lambda base, n: powers(base + g['ONE'], n)
    try:
        return ring_switch(claims, transcript)
    finally:
        g['powers'] = powers
g['ring_switch'] = wrong_gamma
sys.exit(v['main'](sys.argv[2:]))
"#;
    PythonStatement::assert_rejects(&statement.verify_with(&raw, Some(wrong_gamma)), "a wrong gamma_rs");
}
