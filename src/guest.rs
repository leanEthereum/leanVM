//! Prove and verify a run of a guest's ELF executable.

use leanvm::{Program, prove, verify};
use primitives::{bench::Plan, pretty_f64, pretty_integer};

pub fn parse_word(word: &str) -> Result<u64, std::num::ParseIntError> {
    match word.strip_prefix("0x") {
        Some(hex) => u64::from_str_radix(hex, 16),
        None => word.parse(),
    }
}

/// What the user got wrong, said once and plainly: none of these is a bug here.
fn refuse(what: std::fmt::Arguments) -> ! {
    eprintln!("{what}");
    std::process::exit(1)
}

pub fn run_guest(elf: &std::path::Path, input: &[u64], advice: &[u64], log_inv_rate: usize, plan: Plan) {
    let bytes = std::fs::read(elf).unwrap_or_else(|e| refuse(format_args!("{}: {e}", elf.display())));
    let program = Program::from_elf(&bytes).unwrap_or_else(|e| refuse(format_args!("{}: {e}", elf.display())));
    if input.len() > 4 {
        refuse(format_args!("the public input is at most four words"));
    }
    let input: [u64; 4] = std::array::from_fn(|i| input.get(i).copied().unwrap_or(0));
    if advice.len() > 1 << program.rv.log_advice {
        refuse(format_args!(
            "the guest's advice region holds {} words, not {}",
            1u64 << program.rv.log_advice,
            advice.len()
        ));
    }

    let (result, prove_time) = plan.warm_then_measure(|last| {
        let _quiet = (!last).then(primitives::suppress_tracing);
        prove(&program, input, advice, log_inv_rate)
    });
    let (proof, output, stats) = result.unwrap_or_else(|trap| refuse(format_args!("the run has no proof: {trap}")));
    let (_, verify_time) = Plan::new(plan.repeat, 0).measure_quiet(|last| {
        let _quiet = (!last).then(primitives::suppress_tracing);
        verify(&program, &input, &output, &proof).unwrap()
    });

    println!("{}", elf.display());
    println!("  input                       : {input:x?}");
    println!("  output                      : {output:x?}");
    println!("  cycles (VM steps)           : {}", pretty_integer(stats.cycles));
    println!("    details                   : {}", stats.details());
    let proof_bytes = bincode::serialized_size(&proof).expect("proof is serializable");
    println!("  proof size                  : {:.1} KiB", proof_bytes as f64 / 1024.0);
    let cycles_per_second = (stats.cycles as f64 / prove_time.mean()).round() as u64;
    println!(
        "  proving                     : {} s{}   {} cycles/s      peak memory {} GiB",
        pretty_f64(prove_time.mean()),
        prove_time.spread(),
        pretty_integer(cycles_per_second),
        pretty_f64(primitives::bench::peak_rss_bytes() as f64 / (1u64 << 30) as f64)
    );
    println!(
        "  verifying                   : {} ms",
        pretty_f64(verify_time.mean() * 1000.0)
    );
}
