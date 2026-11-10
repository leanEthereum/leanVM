//! Pins both verifiers' `WHIR_QUERIES`, the Rust one's and the Lean one's (`formal/Statement/LeanVmVerifier.lean`),
//! against the prover's query search, and both verifiers' grinding constants against the prover's. They tabulate
//! rather than repeat that search, which would make cross-language float identity part of the protocol.

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

/// A table's entries, per rate `1..=4`, per stack size in the window, each a list `[q,…]`.
fn entries(queries: impl Fn(usize, usize) -> Vec<usize>) -> Vec<Vec<String>> {
    (1..=4)
        .map(|rate| {
            (leanvm_core::pcs::MIN_MU..=leanvm_core::pcs::MAX_MU)
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

/// The Lean verifier's source.
fn lean_verifier() -> String {
    let path = concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/../../formal/Statement/LeanVmVerifier.lean"
    );
    std::fs::read_to_string(path).unwrap_or_else(|e| panic!("read {path}: {e}"))
}

/// Each constant `def name : ℕ := value` of the Lean verifier is the given value.
fn assert_lean_constants(source: &str, constants: &[(&str, usize)]) {
    for (name, value) in constants {
        assert!(
            source.contains(&format!("def {name} : ℕ := {value}\n")),
            "set {name} in formal/Statement/LeanVmVerifier.lean to {value}"
        );
    }
}

#[test]
fn lean_query_table_matches_rust() {
    let source = lean_verifier();
    assert_lean_constants(
        &source,
        &[
            ("minLogStack", leanvm_core::pcs::MIN_MU),
            ("maxLogStack", leanvm_core::pcs::MAX_MU),
        ],
    );
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

#[test]
fn whir_query_table_matches_the_search() {
    let (min_log, max_log) = (leanvm_core::pcs::MIN_MU, leanvm_core::pcs::MAX_MU);
    for rate in 1..=4 {
        for log_n in min_log..=max_log {
            let config = search(log_n, rate);
            assert_eq!(
                verifier::whir_queries(log_n, rate),
                Some(&config.queries[..]),
                "rate {rate}, log_n {log_n}: crates/verifier's WHIR_QUERIES is stale, regenerate it with print_whir_query_table"
            );
            // Hardcoded in the verifiers, so it must hold wherever the table does.
            let expected_ood: Vec<usize> = std::iter::once(0)
                .chain(std::iter::repeat_n(2, config.queries.len() - 1))
                .collect();
            assert_eq!(
                config.ood_samples, expected_ood,
                "rate {rate}, log_n {log_n}: OOD points are no longer 'none at level 0, two after'"
            );
        }
    }
    // The verifier admits exactly the prover's committed-size window, which `pcs::MAX_MU` sets.
    assert_eq!(verifier::whir_queries(min_log - 1, 1), None);
    assert_eq!(verifier::whir_queries(max_log + 1, 1), None);
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

/// The grinds the verifiers hardcode, the Rust one's and the Lean one's, are the prover's. A verifier asking for fewer
/// bits than the prover grinds still accepts every honest proof, so only this catches a drift below the target.
#[test]
fn grinding_constants_match_the_prover() {
    use pcs::whir_config as prover;
    let rust = [
        verifier::SECURITY_BITS,
        verifier::QUERY_GRINDING_BITS,
        verifier::FOLD_GRINDING_BITS,
        verifier::BATCH_GRINDING_BITS,
        verifier::OOD_GRINDING_BITS,
        verifier::OOD_SAMPLES as u32,
    ];
    let expected = [
        leanvm_core::SECURITY_BITS,
        prover::QUERY_GRINDING_BITS,
        prover::FOLD_GRINDING_BITS,
        prover::BATCH_GRINDING_BITS,
        prover::OOD_GRINDING_BITS,
        prover::OOD_SAMPLES as u32,
    ];
    assert_eq!(rust, expected, "crates/verifier's grinding constants");
    assert_lean_constants(
        &lean_verifier(),
        &[
            ("securityBits", leanvm_core::SECURITY_BITS as usize),
            ("queryGrindingBits", prover::QUERY_GRINDING_BITS as usize),
            ("foldGrindingBits", prover::FOLD_GRINDING_BITS as usize),
            ("batchGrindingBits", prover::BATCH_GRINDING_BITS as usize),
            ("oodGrindingBits", prover::OOD_GRINDING_BITS as usize),
            ("oodSamples", prover::OOD_SAMPLES),
            ("maxStackedClaims", prover::MAX_STACKED_CLAIMS),
        ],
    );
}
