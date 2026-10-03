//! Recursion: prove an inner program, then one outer proof that `arity` copies of its proof verify.

use bench::Plan;
use leanvm::recursion::{self, Inner};
use leanvm::{Program, Proved, Prover, Rate};
use primitives::{pretty_f64, pretty_integer};

use crate::{fibonacci, workload};

/// The tables' names, in the recursion machine's order.
pub const TABLES: [&str; 6] = ["EMUL", "EXK", "HASH", "SPLIT", "CAST", "PUB"];

/// The inner program: Fibonacci of `n` steps, or `n` leanXMSS signatures.
pub fn inner(program: &str, n: usize) -> (String, Program, Vec<u64>, [u64; 4]) {
    match program {
        "fibonacci" => {
            let (p, out) = fibonacci::fibonacci_program(n);
            (format!("Fibonacci, N = {}", pretty_integer(&n)), p, Vec::new(), out)
        }
        "leanxmss" => {
            let w = workload::leanxmss(n);
            (w.title.clone(), w.program(), w.advice, w.expected)
        }
        other => crate::guest::refuse(format_args!("no inner program {other}: fibonacci or leanxmss")),
    }
}

/// Prove the inner program at `inner_rate`, then the recursion over `arity` copies of its proof at `rate`, and
/// print the report.
pub fn run(program: &str, n: usize, arity: usize, inner_rate: Rate, prover: &Prover, rate: Rate, plan: Plan) {
    let (title, program, advice, expected) = inner(program, n);
    let Proved { proof, output, .. } = prover.prove(&program, &advice, inner_rate).expect("the run halts");
    assert_eq!(output, expected, "the inner output is the native reference's");
    let inners = vec![
        Inner {
            program: &program,
            proof: &proof,
            output,
        };
        arity
    ];
    let (outer, prove_time) = plan.warm_then_measure(|last| {
        let _quiet = (!last).then(bench::suppress_tracing);
        recursion::prove(prover, &inners, rate).expect("honest inner proofs")
    });
    let programs = vec![&program; arity];
    let (_, verify_time) = Plan::new(plan.repeat, 0).measure_quiet(|last| {
        let _quiet = (!last).then(bench::suppress_tracing);
        recursion::verify(&programs, &outer, rate).expect("the outer proof verifies");
    });
    let stats = recursion::stats(&programs, &outer.inners).expect("valid shapes");

    let statement_words: usize = outer.inners.iter().map(recursion::InnerStatement::n_words).sum();
    let proof_bytes = outer.proof.to_bytes().len();
    println!(
        "Recursion over {arity} x {title}, inner log-inv-rate {}",
        inner_rate.log_inv_rate()
    );
    let rows: Vec<String> = TABLES
        .iter()
        .zip(stats.rows.iter().zip(&stats.log_rows))
        .map(|(name, (rows, log))| format!("{name} {} (2^{log})", pretty_integer(rows)))
        .collect();
    println!("  rows                        : {}", rows.join("  "));
    println!(
        "  committed words             : {} (2^{:.3}), {} per inner proof",
        pretty_integer(&stats.committed),
        (stats.committed as f64).log2(),
        pretty_integer(&(stats.committed / arity))
    );
    println!(
        "  proof size                  : {:.1} KiB outer proof, {:.1} KiB statement",
        proof_bytes as f64 / 1024.0,
        (statement_words * 24) as f64 / 1024.0
    );
    println!(
        "  proving                     : {} s{}   {} s per inner proof      peak memory {} GiB",
        pretty_f64(prove_time.mean()),
        prove_time.spread(),
        pretty_f64(prove_time.mean() / arity as f64),
        pretty_f64(bench::peak_rss_bytes() as f64 / (1u64 << 30) as f64)
    );
    println!(
        "  verifying                   : {} ms",
        pretty_f64(verify_time.mean() * 1000.0)
    );
}
