//! Pins both verifiers' `WHIR_QUERIES`, the Rust one's and the Lean one's (`formal/Statement/LeanVmVerifier.lean`),
//! against the prover's query search. They tabulate rather than repeat that search, which would make cross-language
//! float identity part of the protocol.

use leanvm_core::pcs::{MAX_LOG_INV_RATE, MAX_MU, MIN_LOG_INV_RATE, MIN_MU};
use pcs::LOG_PACKING;
use pcs::whir_config::{ProverConfig, WhirSecurityConfig};

/// The prover's query search at a packed size and rate.
fn search(log_n: usize, rate: usize) -> ProverConfig {
    // `log_n` is the packed size; the Rust search unpacks it itself.
    WhirSecurityConfig::derive_config_with_log_inv_rate(log_n + LOG_PACKING, rate)
        .unwrap_or_else(|e| panic!("rate {rate}, log_n {log_n}: the search itself failed: {e}"))
        .to_config()
        .unwrap_or_else(|e| panic!("rate {rate}, log_n {log_n}: {e}"))
}

/// A table's entries, per rate, per stack size in the window, each a list `[q,…]`.
fn entries(queries: impl Fn(usize, usize) -> Vec<usize>) -> Vec<Vec<String>> {
    (MIN_LOG_INV_RATE..=MAX_LOG_INV_RATE)
        .map(|rate| {
            (MIN_MU..=MAX_MU)
                .map(|log_n| {
                    let counts: Vec<String> = queries(log_n, rate).iter().map(usize::to_string).collect();
                    format!("[{}]", counts.join(","))
                })
                .collect()
        })
        .collect()
}

/// The table as the Lean literal, without whitespace: `[[[q,…],…],…]`.
fn lean_literal(rows: &[Vec<String>]) -> String {
    let rows: Vec<String> = rows.iter().map(|row| format!("[{}]", row.join(","))).collect();
    format!("[{}]", rows.join(","))
}

#[test]
fn lean_query_table_matches_rust() {
    let path = concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/../../formal/Statement/LeanVmVerifier.lean"
    );
    let source = std::fs::read_to_string(path).unwrap_or_else(|e| panic!("read {path}: {e}"));
    for (name, value) in [("minLogStack", MIN_MU), ("maxLogStack", MAX_MU)] {
        assert!(
            source.contains(&format!("def {name} : ℕ := {value}\n")),
            "set {name} in formal/Statement/LeanVmVerifier.lean to {value}"
        );
    }
    let head = "def queryTable : List (List (List ℕ)) :=";
    let body = &source[source.find(head).expect("`queryTable` in the Lean verifier") + head.len()..];
    let lean: String = body[..body.find("\n\n").unwrap_or(body.len())]
        .chars()
        .filter(|c| !c.is_whitespace())
        .collect();
    let rust = lean_literal(&entries(|log_n, rate| {
        verifier::whir_queries(log_n, rate).expect("in the window").to_vec()
    }));
    assert_eq!(
        lean, rust,
        "the Lean verifier's queryTable differs from crates/verifier's WHIR_QUERIES: regenerate both with print_whir_query_table"
    );
}

/// Every admitted shape's proof fits the wire format: its Merkle phases, their queries, leaf widths and tree heights.
#[test]
fn every_shape_fits_the_wire_format() {
    use fiat_shamir::{MAX_HEIGHT, MAX_LEAF_WORDS, MAX_PHASES, MAX_QUERIES};
    for rate in MIN_LOG_INV_RATE..=MAX_LOG_INV_RATE {
        for log_n in MIN_MU..=MAX_MU {
            let config = search(log_n, rate);
            let shapes = config.level_shapes(log_n);
            assert!(
                shapes.levels <= MAX_PHASES,
                "rate {rate}, log_n {log_n}: {} phases",
                shapes.levels
            );
            for level in 0..shapes.levels {
                let height = shapes.block_len[level].trailing_zeros() as usize;
                // Level 0 commits base-field lanes, deeper levels three words a lane.
                let leaf_words = (1 << shapes.ks[level]) * if level == 0 { 1 } else { 3 };
                assert!(
                    config.queries[level] <= MAX_QUERIES && height <= MAX_HEIGHT && leaf_words <= MAX_LEAF_WORDS,
                    "rate {rate}, log_n {log_n}, level {level}: past the wire format's bounds"
                );
            }
        }
    }
}

#[test]
fn whir_query_table_matches_the_search() {
    for rate in MIN_LOG_INV_RATE..=MAX_LOG_INV_RATE {
        for log_n in MIN_MU..=MAX_MU {
            let config = search(log_n, rate);
            assert_eq!(
                verifier::whir_queries(log_n, rate),
                Some(&config.queries[..]),
                "rate {rate}, log_n {log_n}: crates/verifier's WHIR_QUERIES is stale, regenerate it with print_whir_query_table"
            );
            // Hardcoded in the verifiers, so it must hold wherever the table does.
            let expected_ood: Vec<usize> = std::iter::once(0)
                .chain(std::iter::repeat_n(1, config.queries.len() - 1))
                .collect();
            assert_eq!(
                config.ood_samples, expected_ood,
                "rate {rate}, log_n {log_n}: OOD samples are no longer 'none at level 0, one after'"
            );
        }
    }
    // The verifier admits exactly the prover's committed-size window, which `pcs::MAX_MU` sets.
    assert_eq!(verifier::whir_queries(MIN_MU - 1, 1), None);
    assert_eq!(verifier::whir_queries(MAX_MU + 1, 1), None);
}

/// Regenerates the literals the pins above check: the rows go over `WHIR_QUERIES` in `crates/verifier/src/whir.rs`,
/// the last line over `queryTable` in `formal/Statement/LeanVmVerifier.lean`.
/// `cargo test --release -p leanvm_core --test verifiers print_whir_query_table -- --ignored --nocapture`
#[test]
#[ignore = "manual table regeneration"]
fn print_whir_query_table() {
    let rows = entries(|log_n, rate| search(log_n, rate).queries);
    for row in &rows {
        let row: Vec<String> = row.iter().map(|entry| format!("&{entry}")).collect();
        println!("    [{}],", row.join(", "));
    }
    println!("{}", lean_literal(&rows));
}
