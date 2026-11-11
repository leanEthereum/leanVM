//! Writes the deployed fold rounds into `AffineCombinerDeployedTable.lean`: for every rate exponent `1..=4` and stack
//! size `15..=28`, each level's `(κ, R, k, Aend, [(m, D, B)])` of the prover's search
//! (`WhirSecurityConfig::derive_config_with_log_inv_rate(log_n + LOG_PACKING, R)`), between the file's first shape and
//! `foldTable`, and the pin `../../../leanvm-rev` in its header.
//!
//! Usage: `whir-fold-table <AffineCombinerDeployedTable.lean> [--check]`; `--check` fails when the file is stale.

use pcs::LOG_PACKING;
use pcs::whir_config::WhirSecurityConfig;

const FIRST: &str = "/-- Rate exponent 1, stack size 15. -/";
const AFTER: &str = "/-- The deployed levels";
const PIN: &str = "at leanVM `";

/// The unsigned integer after `key` in `s`, from `at`, and the position after it.
fn field(s: &str, at: usize, key: &str) -> (u128, usize) {
    let start = s[at..].find(key).unwrap_or_else(|| panic!("no `{key}` in the config")) + at + key.len();
    let end = start + s[start..].find(|c: char| !c.is_ascii_digit()).expect("a number");
    (s[start..end].parse().expect("a number"), end)
}

/// One shape's levels as the Lean list, from the config's `Debug` form (its thresholds and witnesses are
/// crate-private).
fn shape(log_n: usize, rate: usize) -> String {
    let cfg = WhirSecurityConfig::derive_config_with_log_inv_rate(log_n + LOG_PACKING, rate)
        .unwrap_or_else(|e| panic!("rate {rate}, log_n {log_n}: {e}"));
    cfg.to_config().unwrap_or_else(|e| panic!("rate {rate}, log_n {log_n}: {e}"));
    let s = format!("{cfg:?}");
    let mut levels = Vec::new();
    let mut at = 0;
    while let Some(off) = s[at..].find("WhirLevelConfig {") {
        at += off;
        let (r, p) = field(&s, at, "log_inv_rate: ");
        let (kappa, p) = field(&s, p, "log_msg_cols: ");
        let (k, p) = field(&s, p, "k: ");
        let (agreement, p) = field(&s, p, "agreement: ");
        let rounds_end = p + s[p..].find(']').expect("the rounds");
        let mut rounds = Vec::new();
        let mut q = p;
        while let Some(off) = s[q..rounds_end].find("AffineWitness {") {
            q += off;
            let (m, q1) = field(&s, q, "m: ");
            let (d, q2) = field(&s, q1, "big_d: ");
            let (b, q3) = field(&s, q2, "b: ");
            rounds.push(format!("({m}, {d}, {b})"));
            q = q3;
        }
        assert_eq!(rounds.len() as u128, k, "rate {rate}, log_n {log_n}: one witness per round");
        levels.push(format!("({kappa}, {r}, {k}, {agreement}, [{}])", rounds.join(", ")));
        at = rounds_end;
    }
    assert!(!levels.is_empty(), "rate {rate}, log_n {log_n}: no levels");
    format!(
        "/-- Rate exponent {rate}, stack size {log_n}. -/\ndef foldTable_{rate}_{log_n} : List (ℕ × ℕ × ℕ × ℕ × List (ℕ × ℕ × ℕ)) :=\n  [{}]\n\n",
        levels.join(",\n    ")
    )
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let path = args.get(1).expect("usage: whir-fold-table <AffineCombinerDeployedTable.lean> [--check]");
    let check = args.get(2).is_some_and(|a| a == "--check");
    let old = std::fs::read_to_string(path).unwrap_or_else(|e| panic!("read {path}: {e}"));
    let rev_path = concat!(env!("CARGO_MANIFEST_DIR"), "/../../../leanvm-rev");
    let rev = std::fs::read_to_string(rev_path).unwrap_or_else(|e| panic!("read {rev_path}: {e}"));
    let rev = &rev.trim()[..9];

    let data: String = (1..=4)
        .flat_map(|rate| (15..=28).map(move |log_n| shape(log_n, rate)))
        .collect();
    let first = old.find(FIRST).expect("the first shape");
    let after = old.find(AFTER).expect("`foldTable`");
    let pin = old.find(PIN).expect("the pin") + PIN.len();
    let pin_end = pin + old[pin..].find('`').expect("the pin's end");
    let new = format!("{}{rev}{}{data}{}", &old[..pin], &old[pin_end..first], &old[after..]);

    if check {
        if new != old {
            eprintln!("{path} is stale: rerun whir-fold-table");
            std::process::exit(1);
        }
    } else {
        std::fs::write(path, new).unwrap_or_else(|e| panic!("write {path}: {e}"));
    }
}
