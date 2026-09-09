//! Pins `python-verifier`'s `WHIR_QUERIES` against the Rust query search. The
//! Python verifier tabulates rather than repeating that search, which would make
//! cross-language float identity part of the protocol.

use pcs::LOG_PACKING;
use pcs::whir_config::WhirSecurityConfig;
use std::path::Path;
use std::process::Command;

/// The range, then `rate log_n q0 q1 …` per entry.
const DUMP: &str = "\
import sys; sys.path.insert(0, '.')
import verifier as v
print(v.MIN_STACKED_LOG, v.MAX_STACKED_LOG)
for rate in range(1, 5):
    for log_n in range(v.MIN_STACKED_LOG, v.MAX_STACKED_LOG + 1):
        row = v.WHIR_QUERIES[rate - 1][log_n - v.MIN_STACKED_LOG]
        print(rate, log_n, ' '.join(map(str, row)))
";

#[test]
fn whir_query_table_matches_rust() {
    let directory = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../python-verifier");
    let output = Command::new("python3")
        .arg("-c")
        .arg(DUMP)
        .current_dir(&directory)
        .output()
        .expect("run python3 to dump the table");
    assert!(
        output.status.success(),
        "dumping WHIR_QUERIES failed:\n{}",
        String::from_utf8_lossy(&output.stderr)
    );
    let dumped = String::from_utf8(output.stdout).expect("table dump is utf-8");
    let mut lines = dumped.lines();

    let mut range = lines.next().expect("range line").split_whitespace();
    let mut next_bound = || range.next().expect("a bound").parse::<usize>().expect("a bound");
    let (min_log, max_log) = (next_bound(), next_bound());
    // Every verifier admits the same committed-size window, and `pcs::MAX_MU` is the
    // one knob that sets it. `python-verifier` is standalone and dependency-free, so
    // it cannot read the Rust constant and keeps a literal; this is what stops the
    // two drifting, and names the edit when the knob moves.
    assert_eq!(
        (min_log, max_log),
        (lean_vm::pcs::MIN_MU, lean_vm::pcs::MAX_MU),
        "set MIN_STACKED_LOG / MAX_STACKED_LOG in python-verifier/verifier.py to {} / {}",
        lean_vm::pcs::MIN_MU,
        lean_vm::pcs::MAX_MU
    );

    let mut checked = 0;
    for line in lines {
        let mut fields = line.split_whitespace().map(|f| f.parse::<usize>().expect("an integer"));
        let rate = fields.next().expect("rate");
        let log_n = fields.next().expect("log_n");
        let tabulated: Vec<usize> = fields.collect();

        // Python's `log_n` is the packed size; the Rust search unpacks it itself.
        let m = log_n + LOG_PACKING;
        let config = WhirSecurityConfig::derive_config_with_log_inv_rate(m, rate)
            .unwrap_or_else(|e| panic!("rate {rate}, log_n {log_n}: the search itself failed: {e}"))
            .to_config()
            .unwrap_or_else(|e| panic!("rate {rate}, log_n {log_n}: {e}"));
        assert_eq!(
            config.queries, tabulated,
            "rate {rate}, log_n {log_n}: WHIR_QUERIES is stale, regenerate it with print_whir_query_table"
        );
        // Hardcoded on the Python side, so it must hold wherever the table does.
        let expected_ood: Vec<usize> = std::iter::once(0)
            .chain(std::iter::repeat_n(1, config.queries.len() - 1))
            .collect();
        assert_eq!(
            config.ood_samples, expected_ood,
            "rate {rate}, log_n {log_n}: OOD samples are no longer 'none at level 0, one after'"
        );
        checked += 1;
    }
    assert_eq!(
        checked,
        4 * (max_log - min_log + 1),
        "the table is not the range it claims"
    );
}

/// Regenerates the literal the pin above checks: paste its output over `WHIR_QUERIES` in
/// `python-verifier/verifier.py`.
/// `cargo test --release -p lean_vm --test verifiers print_whir_query_table -- --ignored --nocapture`
#[test]
#[ignore = "manual table regeneration"]
fn print_whir_query_table() {
    let rates: Vec<String> = (1..=4)
        .map(|rate| {
            let rows: Vec<String> = (lean_vm::pcs::MIN_MU..=lean_vm::pcs::MAX_MU)
                .map(|log_n| {
                    let config = WhirSecurityConfig::derive_config_with_log_inv_rate(log_n + LOG_PACKING, rate)
                        .unwrap()
                        .to_config()
                        .unwrap();
                    let queries: Vec<String> = config.queries.iter().map(usize::to_string).collect();
                    format!("({})", queries.join(","))
                })
                .collect();
            format!("({})", rows.join(", "))
        })
        .collect();
    println!("WHIR_QUERIES = ({})  # fmt: skip", rates.join(", "));
}
