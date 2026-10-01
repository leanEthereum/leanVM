//! Prove and verify a run of a guest's ELF executable.

use bench::Plan;
use leanvm::{Program, Proved, Prover, Rate, verify};
use primitives::{pretty_f64, pretty_integer};

pub fn parse_word(word: &str) -> Result<u64, std::num::ParseIntError> {
    match word.strip_prefix("0x") {
        Some(hex) => u64::from_str_radix(hex, 16),
        None => word.parse(),
    }
}

/// An error and its causes, outermost first.
fn chain(error: &dyn std::error::Error) -> String {
    let mut text = error.to_string();
    let mut source = error.source();
    while let Some(cause) = source {
        text = format!("{text}: {cause}");
        source = cause.source();
    }
    text
}

/// What the user got wrong, said once and plainly: none of these is a bug here.
pub fn refuse(what: std::fmt::Arguments) -> ! {
    eprintln!("{what}");
    std::process::exit(1)
}

pub fn run_guest(elf: &std::path::Path, advice: &[u64], prover: &Prover, rate: Rate, plan: Plan) {
    let bytes = std::fs::read(elf).unwrap_or_else(|e| refuse(format_args!("{}: {e}", elf.display())));
    let program =
        Program::from_elf(&bytes).unwrap_or_else(|e| refuse(format_args!("{}: {}", elf.display(), chain(&e))));

    let (
        Proved {
            proof, output, stats, ..
        },
        prove_time,
    ) = plan.warm_then_measure(|last| {
        let _quiet = (!last).then(bench::suppress_tracing);
        prover
            .prove(&program, advice, rate)
            .unwrap_or_else(|e| refuse(format_args!("the run has no proof: {e}")))
    });
    let (_, verify_time) = Plan::new(plan.repeat, 0).measure_quiet(|last| {
        let _quiet = (!last).then(bench::suppress_tracing);
        verify(&program, &output, &proof).unwrap()
    });

    println!("{}", elf.display());
    println!("  advice                      : {} words", pretty_integer(advice.len()));
    println!("  output                      : {output:x?}");
    println!("  cycles (VM steps)           : {}", pretty_integer(stats.cycles));
    println!("    details                   : {}", stats.details());
    let proof_bytes = proof.to_bytes().len();
    println!("  proof size                  : {:.1} KiB", proof_bytes as f64 / 1024.0);
    let cycles_per_second = (stats.cycles as f64 / prove_time.mean()).round() as u64;
    println!(
        "  proving                     : {} s{}   {} cycles/s      peak memory {} GiB",
        pretty_f64(prove_time.mean()),
        prove_time.spread(),
        pretty_integer(cycles_per_second),
        pretty_f64(bench::peak_rss_bytes() as f64 / (1u64 << 30) as f64)
    );
    println!(
        "  verifying                   : {} ms",
        pretty_f64(verify_time.mean() * 1000.0)
    );
}
