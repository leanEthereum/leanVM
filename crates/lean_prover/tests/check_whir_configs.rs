use std::fmt::Write;
use std::fs;
use std::path::PathBuf;

use backend::{TwoAdicField, WhirConfig};
use lean_prover::default_whir_config;
use lean_vm::{EF, F, MAX_WHIR_LOG_INV_RATE, MIN_WHIR_LOG_INV_RATE};

fn expected_whir_configs_line() -> String {
    let mut entries: Vec<String> = Vec::new();

    for log_inv_rate in MIN_WHIR_LOG_INV_RATE..=MAX_WHIR_LOG_INV_RATE {
        let builder = default_whir_config(log_inv_rate);
        let first_ff = builder.folding_factor.at_round(0);
        let max_nv = F::TWO_ADICITY + first_ff - log_inv_rate;

        for num_variables in first_ff..=max_nv {
            let cfg: WhirConfig<EF> = WhirConfig::new(&builder, num_variables);

            let mut rounds = String::from("(");
            for (i, r) in cfg.round_parameters.iter().enumerate() {
                if i > 0 {
                    rounds.push(',');
                }
                write!(
                    rounds,
                    "({},{},{},{})",
                    r.num_queries, r.ood_samples, r.query_pow_bits, r.folding_pow_bits
                )
                .unwrap();
            }
            if cfg.round_parameters.len() == 1 {
                rounds.push(',');
            }
            rounds.push(')');

            entries.push(format!(
                "({},{},{},{},{},{},{})",
                log_inv_rate,
                num_variables,
                cfg.commitment_ood_samples,
                cfg.starting_folding_pow_bits,
                cfg.final_queries,
                cfg.final_query_pow_bits,
                rounds,
            ));
        }
    }

    format!("WHIR_CONFIGS = ({})", entries.join(","))
}

fn strip_ws(s: &str) -> String {
    s.chars().filter(|c| !c.is_whitespace()).collect()
}

#[test]
fn check_whir_configs_in_python_verifier() {
    let expected = expected_whir_configs_line();
    println!("{expected}");

    let verifier_py = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("python-verifier/verifier.py");
    let src =
        fs::read_to_string(&verifier_py).unwrap_or_else(|e| panic!("failed to read {}: {e}", verifier_py.display()));

    assert!(
        strip_ws(&src).contains(&strip_ws(&expected)),
        "WHIR_CONFIGS in {} is out of sync with Rust `default_whir_config`. Replace the line with the one printed above.",
        verifier_py.display(),
    );
}
