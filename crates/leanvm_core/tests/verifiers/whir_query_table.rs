//! Pins `python-verifier`'s WHIR configurations, its `WHIR_QUERIES` and the ladder it
//! builds around them, against the Rust table (`pcs::whir::config_for_rate`), which `pcs`
//! pins to the floating-point soundness derivation. Both verifiers tabulate rather than
//! repeating that search, which would make float identity part of the protocol. A stale
//! Python table fails with the line to paste over it.

use pcs::whir::{MAX_LOG_INV_RATE, MIN_LOG_INV_RATE, config_for_rate};
use std::path::Path;
use std::process::Command;

/// The range, then `rate log_n rates | folds | queries | grinding | ood` per entry.
const DUMP: &str = "\
import sys; sys.path.insert(0, '.')
import verifier as v
print(v.MIN_STACKED_LOG, v.MAX_STACKED_LOG)
for rate in range(1, 5):
    for log_n in range(v.MIN_STACKED_LOG, v.MAX_STACKED_LOG + 1):
        c = v.derive_config(log_n, rate)
        fields = (c.log_inv_rates, c.folds, c.queries, c.grinding_bits, c.ood_samples)
        print(rate, log_n, ' | '.join(' '.join(map(str, f)) for f in fields))
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
        "dumping the WHIR configurations failed:\n{}\nIf WHIR_QUERIES in python-verifier/verifier.py is stale, replace it with:\n{}",
        String::from_utf8_lossy(&output.stderr),
        python_table()
    );
    let dumped = String::from_utf8(output.stdout).expect("table dump is utf-8");
    let mut lines = dumped.lines();

    let mut range = lines.next().expect("range line").split_whitespace();
    let mut next_bound = || range.next().expect("a bound").parse::<usize>().expect("a bound");
    let (min_log, max_log) = (next_bound(), next_bound());
    // Every verifier admits the same committed-size window, and the WHIR table's
    // `pcs::whir::MAX_LOG_N` is the one knob that sets it. `python-verifier` is standalone
    // and dependency-free, so it cannot read the Rust constant and keeps a literal; this
    // is what stops the two drifting, and names the edit when the knob moves.
    assert_eq!(
        (min_log, max_log),
        (leanvm_core::MIN_MU, leanvm_core::MAX_MU),
        "set MIN_STACKED_LOG / MAX_STACKED_LOG in python-verifier/verifier.py to {} / {}",
        leanvm_core::MIN_MU,
        leanvm_core::MAX_MU
    );

    let mut checked = 0;
    for line in lines {
        let (rate, log_n, rest) = {
            let mut head = line.splitn(3, ' ');
            let mut next = || head.next().expect("a field");
            (
                next().parse::<usize>().expect("rate"),
                next().parse::<usize>().expect("log_n"),
                next(),
            )
        };
        let fields: Vec<Vec<usize>> = rest
            .split(" | ")
            .map(|f| f.split_whitespace().map(|x| x.parse().expect("an integer")).collect())
            .collect();
        let [rates, folds, queries, grinding, ood] = fields.as_slice() else {
            panic!("rate {rate}, log_n {log_n}: expected rates | folds | queries | grinding | ood, got {rest}")
        };

        let config = config_for_rate(log_n, rate).unwrap_or_else(|e| panic!("rate {rate}, log_n {log_n}: {e}"));
        assert_eq!(
            config.queries(),
            queries,
            "rate {rate}, log_n {log_n}: WHIR_QUERIES in python-verifier/verifier.py is stale, replace it with:\n{}",
            python_table()
        );
        assert_eq!(
            config.log_inv_rates(),
            rates,
            "rate {rate}, log_n {log_n}: the rate ladders differ"
        );
        let rust_folds: Vec<usize> = std::iter::once(config.initial_k())
            .chain(config.level_ks().iter().copied())
            .collect();
        assert_eq!(
            &rust_folds, folds,
            "rate {rate}, log_n {log_n}: the fold ladders differ"
        );
        assert_eq!(
            config.grinding_bits(),
            grinding,
            "rate {rate}, log_n {log_n}: the grinding ladders differ"
        );
        assert_eq!(
            config.ood_samples(),
            ood,
            "rate {rate}, log_n {log_n}: the OOD ladders differ"
        );
        checked += 1;
    }
    assert_eq!(
        checked,
        4 * (max_log - min_log + 1),
        "the table is not the range it claims"
    );
}

/// `WHIR_QUERIES` as `python-verifier/verifier.py` writes it, from the Rust table.
fn python_table() -> String {
    let rates: Vec<String> = (MIN_LOG_INV_RATE..=MAX_LOG_INV_RATE)
        .map(|rate| {
            let rows: Vec<String> = (leanvm_core::MIN_MU..=leanvm_core::MAX_MU)
                .map(|log_n| {
                    let config = config_for_rate(log_n, rate).unwrap();
                    let queries: Vec<String> = config.queries().iter().map(usize::to_string).collect();
                    format!("({})", queries.join(","))
                })
                .collect();
            format!("({})", rows.join(", "))
        })
        .collect();
    format!("WHIR_QUERIES = ({})  # fmt: skip", rates.join(", "))
}
