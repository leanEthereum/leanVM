//! The two verifiers agree on their constants.
//!
//! `python-verifier/verifier.py` writes out the same protocol a second time, which means
//! writing out its constants a second time: the region bases and caps, the clock's bits
//! and slots, the flock and WHIR parameters, and every class's block size and legal
//! flags. The end-to-end tests catch a Python circuit that computes the wrong thing, but
//! a constant that drifts changes what each side ACCEPTS, and only a statement they both
//! reject would show it. So the two lists are rendered the same way and diffed here.

use leanvm_core::rv::hash;
use leanvm_core::tables::CLASSES;
use std::fmt::Write;

/// What the Rust verifier's constants come to, in the format `protocol_constants()`
/// prints: sorted `name value` lines, a list being comma-separated.
fn rust_constants() -> String {
    let mut lines: Vec<String> = Vec::new();
    let mut scalar = |name: &str, value: u64| lines.push(format!("{name} {value}"));

    scalar("ADVICE_BASE", leanvm_core::rv::ADVICE_BASE);
    scalar("BAD_SLOT", leanvm_core::tables::BAD_SLOT as u64);
    scalar("BUS_BITS", leanvm_core::leaf::N_TUPLE_BITS as u64);
    scalar("EXIT_SLOT", leanvm_core::tables::EXIT_SLOT as u64);
    scalar("CLOCK_START", leanvm_core::tables::CLOCK_START);
    scalar("FAIL_BIT", leanvm_core::tables::FAIL_BIT as u64);
    scalar("FLOCK_K_SKIP", flock::zerocheck::K_SKIP as u64);
    scalar("FLOCK_MIN_LOG_SIZE", leanvm_core::class_flock::MIN_CUBE_LOG as u64);
    scalar("HASH_OUT_WORD", hash::OUT / 8);
    scalar("HASH_WORDS", hash::WORDS as u64);
    scalar(
        "INITIAL_FOLDING_FACTOR",
        pcs::whir_config::INITIAL_FOLDING_FACTOR as u64,
    );
    scalar("LIVE_BIT", leanvm_core::tables::LIVE_BIT as u64);
    scalar("LOG_COUNT_BITS", leanvm_core::lookup::LOG_COUNT_BITS as u64);
    scalar("LOG_PACKING", pcs::pack::LOG_PACKING as u64);
    scalar("LOG_REGISTERS", leanvm_core::rv::LOG_REGS as u64);
    scalar("MAX_LOG_ADVICE", leanvm_core::rv::MAX_LOG_ADVICE as u64);
    scalar("MAX_LOG_RAM", leanvm_core::rv::MAX_LOG_RAM as u64);
    scalar("MAX_LOG_ROWS", leanvm_core::cpu::MAX_LOG_ROWS as u64);
    scalar("MAX_LOG_TEXT", leanvm_core::rv::MAX_LOG_TEXT as u64);
    scalar("MAX_STACKED_LOG", leanvm_core::pcs::MAX_MU as u64);
    scalar("MIN_STACKED_LOG", leanvm_core::pcs::MIN_MU as u64);
    scalar("NUM_FRAMEWORK_COLUMNS", leanvm_core::cpu::Q_BASE as u64);
    scalar("QUERY_GRINDING_BITS", pcs::whir_config::QUERY_GRINDING_BITS as u64);
    scalar("RAM_BASE", leanvm_core::rv::RAM_BASE);
    scalar("RAM_SLOT", leanvm_core::tables::RAM_SLOT as u64);
    scalar("RESIDUAL_MAX_LOG", pcs::whir_config::RESIDUAL_MAX_LOG as u64);
    let rs_domain = pcs::whir_config::RS_DOMAIN_INITIAL_REDUCTION_FACTOR;
    scalar("RS_DOMAIN_INITIAL_REDUCTION_FACTOR", rs_domain as u64);
    let rs_domain_rest = pcs::whir_config::RS_DOMAIN_SUBSEQUENT_REDUCTION_FACTOR;
    scalar("RS_DOMAIN_SUBSEQUENT_REDUCTION_FACTOR", rs_domain_rest as u64);
    scalar("SEED_CLOCK", leanvm_core::tables::SEED_CLOCK);
    scalar("SINK", leanvm_core::rv::SINK as u64);
    scalar("SLOT_BITS", leanvm_core::tables::SLOT_BITS as u64);
    scalar(
        "SUBSEQUENT_FOLDING_FACTOR",
        pcs::whir_config::SUBSEQUENT_FOLDING_FACTOR as u64,
    );
    scalar("SYSCALL_REGISTER", leanvm_core::rv::SYSCALL_REG as u64);
    scalar("SYS_EXIT", leanvm_core::rv::SYS_EXIT);
    scalar("TEXT_BASE", leanvm_core::rv::TEXT_BASE);

    let list = |values: &[u64]| values.iter().map(u64::to_string).collect::<Vec<_>>().join(",");
    lines.push(format!(
        "OUTPUT_REGISTERS {}",
        list(&leanvm_core::rv::OUTPUT_REGS.map(u64::from))
    ));
    lines.push(format!(
        "REGISTER_SLOTS {}",
        list(&leanvm_core::tables::REG_SLOTS.map(u64::from))
    ));

    for (t, spec) in CLASSES.iter().enumerate() {
        use leanvm_core::class_flock::{circuit, flock_index, stride_log};
        use leanvm_core::tables::Part;
        let clock = circuit(flock_index(t, Part::Clock));
        let circuit = circuit(flock_index(t, Part::Class));
        let prefix = format!("TABLE.{}", spec.name.to_lowercase());
        let mut line = String::new();
        for (field, value) in [
            ("opcode", t as u64),
            ("k_log", spec.k_log as u64),
            ("const_pos", circuit.const_pos() as u64),
            ("slot_bits", stride_log(spec, Part::Class) as u64),
            ("clock_k_log", clock.k_log() as u64),
            ("clock_const_pos", clock.const_pos() as u64),
            ("min_log_height", leanvm_core::class_flock::n_blocks_log(spec, 1) as u64),
            ("ports", spec.ports.len() as u64),
            ("width", leanvm_core::tables::tables()[t].n_committed_columns() as u64),
        ] {
            line.clear();
            write!(line, "{prefix}.{field} {value}").unwrap();
            lines.push(line.clone());
        }
        lines.push(format!(
            "{prefix}.slots {}",
            list(&spec.slots().iter().map(|&s| s as u64).collect::<Vec<_>>())
        ));
        let mut flags = leanvm_core::rv::legal_flags(spec.class).to_vec();
        flags.sort_unstable();
        lines.push(format!("{prefix}.legal_flags {}", list(&flags)));
    }
    lines.sort();
    lines.join("\n")
}

#[test]
fn constants_match_the_python_verifier() {
    let verifier = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../../python-verifier/verifier.py");
    let dumped = std::process::Command::new("python3")
        .arg(&verifier)
        .arg("--constants")
        .output()
        .expect("run the Python verifier");
    assert!(dumped.status.success(), "{}", String::from_utf8_lossy(&dumped.stderr));
    let python = String::from_utf8(dumped.stdout).expect("utf-8").trim().to_string();
    let rust = rust_constants();

    let parse = |dump: &str| -> std::collections::BTreeMap<String, String> {
        dump.lines()
            .filter_map(|line| line.split_once(' '))
            .map(|(name, value)| (name.to_string(), value.to_string()))
            .collect()
    };
    let (theirs, ours) = (parse(&python), parse(&rust));
    let names: std::collections::BTreeSet<&String> = theirs.keys().chain(ours.keys()).collect();
    let differences: Vec<String> = names
        .into_iter()
        .filter(|name| theirs.get(*name) != ours.get(*name))
        .map(|name| {
            let missing = "(missing)".to_string();
            let (them, us) = (theirs.get(name).unwrap_or(&missing), ours.get(name).unwrap_or(&missing));
            format!("  {name}: python {them}, rust {us}")
        })
        .collect();
    assert!(
        differences.is_empty(),
        "the two verifiers disagree on {} constant(s):\n{}",
        differences.len(),
        differences.join("\n")
    );
}
