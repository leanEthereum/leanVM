//! ACT4, the RISC-V architectural tests (riscv-arch-test 4.1.0), its I and M suites:
//! generated for leanVM's memory map by `conformance/act4/generate.sh`, which runs every
//! test on the Sail reference model and builds it again with Sail's results inside,
//! so that it checks itself. Not checked in: `generate.sh` writes them to the ignored
//! `conformance/act4/elf/`, or `LEANVM_ACT4` names another directory, which is how CI runs
//! them. Run on the interpreter, proven, and checked by the native verifier. A test exits
//! with the output zero when every check passes. Both tests are `#[ignore]`d, since
//! they need the generated files: `cargo test --release -p leanvm_core --test verifiers
//! -- --ignored act4`.

use leanvm_core::{Guest, Machine, Program, ProvenRun, Prover, Rate, Region, Trap};
use std::path::{Path, PathBuf};

/// Every test of the two suites, as `(extension, instruction)`, the file being
/// `<extension>/<extension>-<instruction>-00.elf`.
const TESTS: [(&str, &[&str]); 2] = [
    (
        "I",
        &[
            "add", "addi", "addiw", "addw", "and", "andi", "auipc", "beq", "bge", "bgeu", "blt", "bltu", "bne",
            "fence", "jal", "jalr", "lb", "lbu", "ld", "lh", "lhu", "lui", "lw", "lwu", "nop", "or", "ori", "sb", "sd",
            "sh", "sll", "slli", "slliw", "sllw", "slt", "slti", "sltiu", "sltu", "sra", "srai", "sraiw", "sraw",
            "srl", "srli", "srliw", "srlw", "sub", "subw", "sw", "xor", "xori",
        ],
    ),
    (
        "M",
        &[
            "div", "divu", "divuw", "divw", "mul", "mulh", "mulhsu", "mulhu", "mulw", "rem", "remu", "remuw", "remw",
        ],
    ),
];

const PASS: [u64; 4] = [0; 4];
const CYCLE_CAP: u64 = 1 << 20;

struct Test {
    name: String,
    text: Vec<u32>,
    program: Program,
}

/// Every test, from the directory holding exactly their files.
fn suite() -> Vec<Test> {
    let root = std::env::var_os("LEANVM_ACT4").map_or_else(
        || PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../../conformance/act4/elf"),
        PathBuf::from,
    );
    let listing = |directory: &Path| -> Vec<String> {
        let mut names: Vec<String> = std::fs::read_dir(directory)
            .unwrap_or_else(|error| {
                panic!(
                    "{}: {error}; generate the files with conformance/act4/generate.sh",
                    directory.display()
                )
            })
            .map(|entry| entry.unwrap().file_name().into_string().unwrap())
            .collect();
        names.sort();
        names
    };
    assert_eq!(
        listing(&root),
        TESTS.map(|(extension, _)| extension),
        "{}",
        root.display()
    );
    let mut suite = Vec::new();
    for (extension, instructions) in TESTS {
        let directory = root.join(extension);
        let names: Vec<String> = instructions
            .iter()
            .map(|name| format!("{extension}-{name}-00"))
            .collect();
        let files: Vec<String> = names.iter().map(|name| format!("{name}.elf")).collect();
        assert_eq!(listing(&directory), files, "{}", directory.display());
        for name in names {
            let elf = std::fs::read(directory.join(format!("{name}.elf"))).unwrap();
            let guest = Guest::from_elf(&elf).unwrap_or_else(|error| panic!("{name}: {error}"));
            let program = Program::from_elf(&elf).unwrap();
            suite.push(Test {
                name,
                text: guest.text,
                program,
            });
        }
    }
    suite
}

/// What ACT4's failure handler knows of a failing check. It reads the check's
/// instructions back from the text, which leanVM cannot read, so the handler traps
/// there, loading from `x5 - 6`, with `x5` the return address of the check's `jal`,
/// behind which the text holds the check's label and the address of its description,
/// and `x4` its register save area, where the registers are.
fn failed_check(test: &Test, machine: &Machine, trap: &Trap) -> Option<String> {
    let link = machine.registers().cells()[5];
    if !matches!(*trap, Trap::Unmapped { address, .. } if address == link.wrapping_sub(6)) {
        return None;
    }
    let word = |pc: u64| {
        test.text
            .get(pc.checked_sub(Region::TEXT.base())? as usize / 4)
            .copied()
    };
    let ram = |address: u64| {
        machine
            .memory()
            .ram()
            .get(address.checked_sub(Region::RAM.base())? as usize / 8)
            .copied()
    };
    // `ld expected, offset(signature)`, `beq expected, actual`, `jal x5, handler`.
    let (load, beq) = (word(link.wrapping_sub(12))?, word(link.wrapping_sub(8))?);
    if load & 0x707f != 0x3003 || beq & 0x707f != 0x63 {
        return None;
    }
    let saved = |register: u32| ram(machine.registers().cells()[4].wrapping_add(8 * register as u64));
    let actual = (beq >> 20) & 31;
    let signature = saved((load >> 15) & 31)?.wrapping_add((load as i32 >> 20) as u64);
    let description = u64::from(word(link.wrapping_add(8))?) | u64::from(word(link.wrapping_add(12))?) << 32;
    let description: Vec<u8> = (description..)
        .map_while(|address| Some((ram(address)? >> (8 * (address % 8))) as u8).filter(|&byte| byte != 0))
        .collect();
    Some(format!(
        "{}: x{actual} = {:#x}, Sail's is {:#x}",
        String::from_utf8_lossy(&description),
        saved(actual)?,
        ram(signature)?,
    ))
}

/// What the interpreter says of a test, as a failure message if it is not a pass.
fn check_run(test: &Test) -> Result<(), String> {
    let name = &test.name;
    let mut machine = Machine::new(test.program.rv(), &[]);
    match machine.run_for(CYCLE_CAP) {
        Ok(Some(PASS)) => Ok(()),
        Ok(Some([1, called_from, ..])) => Err(format!("{name}: fails, halting from {called_from:#x}")),
        Ok(Some(output)) => Err(format!("{name}: exits with {output:?}")),
        Ok(None) => Err(format!("{name}: runs past {CYCLE_CAP} cycles")),
        Err(trap) => Err(failed_check(test, &machine, &trap)
            .map_or_else(|| format!("{name}: {trap}"), |check| format!("{name}: {check}"))),
    }
}

#[test]
#[ignore = "needs the ELF files of conformance/act4/generate.sh"]
fn act4_on_the_interpreter() {
    let failures: Vec<String> = suite().iter().filter_map(|test| check_run(test).err()).collect();
    assert!(failures.is_empty(), "{}", failures.join("\n"));
}

/// Every architectural test proven and checked by the native verifier.
#[test]
#[ignore = "needs the ELF files of conformance/act4/generate.sh"]
fn act4_proven() {
    for Test { name, program, .. } in suite() {
        let ProvenRun { proof, output, .. } = Prover::new(Rate::MIN)
            .prove(&program, &[])
            .unwrap_or_else(|trap| panic!("{name}: {trap}"));
        assert_eq!(output, PASS, "{name}: the prover's output");
        program
            .verify(output, &proof)
            .unwrap_or_else(|error| panic!("{name}: {error:?}"));
    }
}
