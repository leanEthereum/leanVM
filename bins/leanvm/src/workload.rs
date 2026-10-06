//! A guest workload, proven and verified the way the benchmarks report it.

use crate::guest::refuse;
use bench::Plan;
use leanvm::{Program, ProvenRun, Prover};
use primitives::{pretty_f64, pretty_integer};

/// One run of a guest (`programs/`): what it is given and what it must output.
pub struct Workload {
    /// What the report calls the run.
    pub title: String,
    /// The guest's ELF file.
    pub elf: &'static [u8],
    /// What the guest checks, which the statement does not cover.
    pub advice: Vec<u64>,
    /// The output the native reference computed, so a proof of anything else fails.
    pub expected: [u64; 4],
    /// How many items the run covers.
    pub items: usize,
    /// What one item is called.
    pub item: &'static str,
}

impl Workload {
    /// The guest, loaded.
    pub fn program(&self) -> Program {
        Program::from_elf(self.elf).expect("a guest's ELF file")
    }
}

/// Verify `n` leanXMSS signatures, one key each.
pub fn leanxmss(n: usize) -> Workload {
    let run = leanxmss_host::batch(n);
    Workload {
        title: format!("leanXMSS verification, {n} signatures"),
        elf: leanxmss_host::ELF,
        advice: run.advice,
        expected: run.expected,
        items: n,
        item: "signature",
    }
}

/// Verify `n` leanSPHINCS signatures, one key each.
pub fn leansphincs(n: usize) -> Workload {
    let run = leansphincs_host::batch(n);
    Workload {
        title: format!("leanSPHINCS verification, {n} signatures"),
        elf: leansphincs_host::ELF,
        advice: run.advice,
        expected: run.expected,
        items: n,
        item: "signature",
    }
}

/// Verify `n` Falcon-512 signatures, one key each.
pub fn falcon(n: usize) -> Workload {
    let run = falcon_host::batch(n);
    Workload {
        title: format!("Falcon-512 verification, {n} signatures"),
        elf: falcon_host::ELF,
        advice: run.advice,
        expected: run.expected,
        items: n,
        item: "signature",
    }
}

/// Verify `n` L1 state reads at one mainnet block, each an account and one of its storage slots.
pub fn stateproof(n: usize) -> Workload {
    let run = stateproof_host::reads(n);
    Workload {
        title: format!("L1 state proofs, {n} reads"),
        elf: stateproof_host::ELF,
        advice: run.advice,
        expected: run.expected,
        items: n,
        item: "read",
    }
}

/// Check `n` leanDA blobs and compute their commitment.
pub fn leanda(n: usize) -> Workload {
    let run = leanda_host::blobs(n);
    Workload {
        title: format!("leanDA check, {n} blobs of 128 KiB"),
        elf: leanda_host::ELF,
        advice: run.advice,
        expected: run.expected,
        items: n,
        item: "blob",
    }
}

/// Prove and verify a workload, and print the report.
///
/// Proving runs one discarded warmup pass, then `plan.repeat` measured passes.
pub fn run(workload: &Workload, prover: &Prover, plan: Plan) {
    let program = workload.program();
    // Only the final measured pass is traced.
    let (
        ProvenRun {
            proof, output, stats, ..
        },
        prove_time,
    ) = plan.warm_then_measure(|last| {
        let _quiet = (!last).then(bench::suppress_tracing);
        // More items than one proof or the advice region holds is the user's mistake, not a bug.
        prover
            .prove(&program, &workload.advice)
            .unwrap_or_else(|e| refuse(format_args!("{} {}s have no proof: {e}", workload.items, workload.item)))
    });
    assert_eq!(
        output, workload.expected,
        "the guest's output is the native reference's"
    );
    let (_, verify_time) = Plan::new(plan.repeat, 0).measure_quiet(|last| {
        let _quiet = (!last).then(bench::suppress_tracing);
        program.verify(output, &proof).expect("the proof verifies");
    });

    let cycles = stats.cycles();
    println!("{}", workload.title);
    println!(
        "  cycles (RISC-V)             : {}   {} per {}",
        pretty_integer(&cycles),
        pretty_f64(cycles as f64 / workload.items as f64),
        workload.item
    );
    // Rows per table, then the committed witness: what the prover pays for.
    println!("    details                   : {}", stats.details());
    let proof_bytes = proof.to_bytes().len();
    println!("  proof size                  : {:.1} KiB", proof_bytes as f64 / 1024.0);
    println!(
        "  proving                     : {} s{}   {} {}s/s      peak memory {} GiB",
        pretty_f64(prove_time.mean()),
        prove_time.spread(),
        pretty_f64(workload.items as f64 / prove_time.mean()),
        workload.item,
        pretty_f64(bench::peak_rss_bytes() as f64 / (1u64 << 30) as f64)
    );
    println!(
        "  verifying                   : {} ms",
        pretty_f64(verify_time.mean() * 1000.0)
    );
}

#[cfg(test)]
mod tests {
    use bench::Plan;
    use leanvm::{Prover, Rate};

    #[test]
    fn the_signature_workloads_prove() {
        // End to end: proven, verified, and the output the native digest.
        let prover = Prover::new(Rate::MIN);
        for workload in [super::leanxmss(2), super::leansphincs(1), super::falcon(1)] {
            super::run(&workload, &prover, Plan::default());
        }
    }

    #[test]
    fn counting_a_run_agrees_with_its_trace() {
        // Measuring counts rows without recording them, which must match the rows the trace records.
        for workload in [super::leanxmss(2), super::leansphincs(1), super::leanda(1)] {
            let program = workload.program();
            let exec = program.execute(&workload.advice).expect("the run halts");
            let stats = program.measure(&workload.advice).expect("the run halts");
            assert_eq!(stats.base_counts, exec.base_counts, "{}", workload.title);
            assert_eq!(stats.proven_rows, exec.proven_rows, "{}", workload.title);
        }
    }
}
