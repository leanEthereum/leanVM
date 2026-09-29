//! A guest workload, proven and verified the way the benchmarks report it.

use leanvm::{Program, prove, verify};
use primitives::{bench::Plan, pretty_f64, pretty_integer};

use crate::guest::refuse;

/// One run of a guest (`guests/`): what it is given and what it must output.
pub struct Workload {
    /// What the report calls the run.
    pub title: String,
    /// The guest's ELF file.
    pub elf: &'static [u8],
    /// The public input: the item count, then zeros.
    pub input: [u64; 4],
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

    /// Run the guest on the interpreter, with no proof: its output, or the trap.
    #[cfg(test)]
    pub fn run(&self) -> Result<[u64; 4], lean_vm::rv::Trap> {
        lean_vm::rv::Machine::new(&self.program().rv, self.input, &self.advice).run(1 << 30)
    }
}

/// Prove and verify a workload, and print the report.
///
/// Proving runs one discarded warmup pass, then `plan.repeat` measured passes.
pub fn run(workload: &Workload, log_inv_rate: usize, plan: Plan) {
    let program = workload.program();
    // More items than the guest's advice region holds is the user's mistake, not a bug.
    let region = 1usize << program.rv.log_advice;
    if workload.advice.len() > region {
        refuse(format_args!(
            "{} {}s take {} advice words, and the guest's region holds {region}",
            workload.items,
            workload.item,
            workload.advice.len()
        ));
    }
    // Only the final measured pass is traced.
    let (result, prove_time) = plan.warm_then_measure(|last| {
        let _quiet = (!last).then(primitives::suppress_tracing);
        prove(&program, workload.input, &workload.advice, log_inv_rate)
    });
    // A run too long for one proof has none: continuations are not implemented.
    let (proof, output, stats) = result.unwrap_or_else(|trap| refuse(format_args!("the run has no proof: {trap}")));
    assert_eq!(
        output, workload.expected,
        "the guest's output is the native reference's"
    );
    let (_, verify_time) = Plan::new(plan.repeat, 0).measure_quiet(|last| {
        let _quiet = (!last).then(primitives::suppress_tracing);
        verify(&program, &workload.input, &output, &proof).expect("the proof verifies")
    });

    // The proven rows include padding: the guest's own cycles are the per-table base counts.
    let cycles: usize = stats.base_counts.iter().sum();
    println!("{}", workload.title);
    println!(
        "  cycles (RISC-V)             : {}   {} per {}",
        pretty_integer(cycles),
        pretty_f64(cycles as f64 / workload.items as f64),
        workload.item
    );
    // Rows per table, then the committed witness: what the prover pays for.
    println!("    details                   : {}", stats.details());
    let proof_bytes = bincode::serialized_size(&proof).expect("proof is serializable");
    println!("  proof size                  : {:.1} KiB", proof_bytes as f64 / 1024.0);
    println!(
        "  proving                     : {} s{}   {} {}s/s      peak memory {} GiB",
        pretty_f64(prove_time.mean()),
        prove_time.spread(),
        pretty_f64(workload.items as f64 / prove_time.mean()),
        workload.item,
        pretty_f64(primitives::bench::peak_rss_bytes() as f64 / (1u64 << 30) as f64)
    );
    println!(
        "  verifying                   : {} ms",
        pretty_f64(verify_time.mean() * 1000.0)
    );
}
