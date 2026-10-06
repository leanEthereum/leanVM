//! A program run on its advice, proven and verified the way the benchmarks report it.

use crate::{chain, refuse};
use bench::Plan;
use leanvm::asm::{Add, Addi, Asm, Bne, Reg};
use leanvm::{Output, Program, ProvenRun, Prover, Region, Stats};
use leanvm_guest::{PublicValues, Run};
use primitives::hash::{digest_words, hash};
use primitives::{pretty_f64, pretty_integer};
use std::path::Path;

/// One run of a program: what it is given and what it must output.
pub struct Workload {
    /// What the report calls the run.
    pub title: String,
    /// What runs.
    pub program: Program,
    /// The advice, which the statement does not cover.
    pub advice: Vec<u64>,
    /// The output a native reference computed, so a proof of anything else fails.
    pub expected: Option<Output>,
    /// What the run covers, if it counts in items.
    pub items: Option<Items>,
}

/// How many items a run covers, and what one is called.
#[derive(Clone, Copy)]
pub struct Items {
    /// How many.
    pub count: usize,
    /// What one is called.
    pub name: &'static str,
}

impl Workload {
    /// A guest's run whose output a host computed natively.
    fn hosted(title: String, elf: &[u8], run: Run, count: usize, name: &'static str) -> Self {
        Self {
            title,
            program: Program::from_elf(elf).expect("a guest's ELF file"),
            advice: run.advice,
            expected: Some(Output::new(run.expected)),
            items: Some(Items { count, name }),
        }
    }

    /// Fibonacci modulo 2^64 in hand-written RISC-V, `n` steps, outputting `F(n)`.
    ///
    /// A loop's body is `UNROLL` steps in place, `a <- a + b` then `b <- a + b`.
    /// So a step is one instruction, and the loop's own two are paid once per `UNROLL`.
    pub fn fibonacci(n: usize) -> Self {
        const UNROLL: usize = 1000;
        assert!(
            n >= UNROLL && n.is_multiple_of(UNROLL),
            "n must be a positive multiple of {UNROLL}"
        );
        let mut text = Asm::new();
        text.li(Reg::A0, 0)
            .li(Reg::A1, 1)
            .li(Reg::T0, (n / UNROLL) as u64)
            .label("loop");
        for _ in 0..UNROLL / 2 {
            text.r(Add, Reg::A0, Reg::A0, Reg::A1).r(Add, Reg::A1, Reg::A0, Reg::A1);
        }
        text.i(Addi, Reg::T0, Reg::T0, -1)
            .branch(Bne, Reg::T0, Reg::ZERO, "loop")
            .li(Reg::A1, 0)
            .exit();

        let (mut a, mut b) = (0u64, 1u64);
        for _ in 0..n / 2 {
            a = a.wrapping_add(b);
            b = b.wrapping_add(a);
        }
        Self {
            title: format!("Fibonacci modulo 2^64, {} steps", pretty_integer(&n)),
            program: Program::new(&text.finish(), Region::TEXT.base(), vec![], 2, 0).expect("a valid program"),
            advice: vec![],
            expected: Some(Output::new([a, 0, 0, 0])),
            items: Some(Items { count: n, name: "step" }),
        }
    }

    /// The `hash` guest: BLAKE2s of the bytes `0, 1, 2, ...` (mod 251) through the precompile.
    pub fn hash(length: usize) -> Self {
        let message: Vec<u8> = (0..length).map(|i| (i % 251) as u8).collect();
        let digest = digest_words(&hash(&message));
        // What the guest commits: the length, then the digest.
        let mut public = PublicValues::new();
        public.commit(&(length as u64)).commit(&digest);
        let run = Run {
            advice: vec![length as u64],
            expected: public.digest(),
        };
        let title = format!("BLAKE2s of {} bytes", pretty_integer(&length));
        Self::hosted(
            title,
            include_bytes!("../../../programs/hash/hash.elf"),
            run,
            length,
            "byte",
        )
    }

    /// Verify `n` leanXMSS signatures, one key each.
    pub fn leanxmss(n: usize) -> Self {
        let title = format!("leanXMSS verification, {n} signatures");
        Self::hosted(title, leanxmss_host::ELF, leanxmss_host::batch(n), n, "signature")
    }

    /// Verify `n` leanSPHINCS signatures, one key each.
    pub fn leansphincs(n: usize) -> Self {
        let title = format!("leanSPHINCS verification, {n} signatures");
        Self::hosted(title, leansphincs_host::ELF, leansphincs_host::batch(n), n, "signature")
    }

    /// Verify `n` Falcon-512 signatures, one key each.
    pub fn falcon(n: usize) -> Self {
        let title = format!("Falcon-512 verification, {n} signatures");
        Self::hosted(title, falcon_host::ELF, falcon_host::batch(n), n, "signature")
    }

    /// Verify `n` L1 state reads at one mainnet block, each an account and one of its storage slots.
    pub fn stateproof(n: usize) -> Self {
        let title = format!("L1 state proofs, {n} reads");
        Self::hosted(title, stateproof_host::ELF, stateproof_host::reads(n), n, "read")
    }

    /// Check `n` leanDA blobs and compute their commitment.
    pub fn leanda(n: usize) -> Self {
        let title = format!("leanDA check, {n} blobs of 128 KiB");
        Self::hosted(title, leanda_host::ELF, leanda_host::blobs(n), n, "blob")
    }

    /// A guest's ELF file run on this advice, with no reference output.
    ///
    /// A file that cannot be read or is no guest is the user's mistake, refused plainly.
    pub fn guest(elf: &Path, advice: Vec<u64>) -> Self {
        let bytes = std::fs::read(elf).unwrap_or_else(|e| refuse(format_args!("{}: {e}", elf.display())));
        let program =
            Program::from_elf(&bytes).unwrap_or_else(|e| refuse(format_args!("{}: {}", elf.display(), chain(&e))));
        Self {
            title: elf.display().to_string(),
            program,
            advice,
            expected: None,
            items: None,
        }
    }

    /// The run's exact counts, without a proof.
    pub fn measure(&self) -> Stats {
        (self.program.measure(&self.advice))
            .unwrap_or_else(|e| refuse(format_args!("{} has no proof: {e}", self.title)))
    }

    /// Prove the run, and check its output against the reference.
    ///
    /// A run with no proof is the user's mistake (too many items for one proof, a trap), refused plainly.
    pub fn prove(&self, prover: &Prover) -> ProvenRun {
        let run = (prover.prove(&self.program, &self.advice))
            .unwrap_or_else(|e| refuse(format_args!("{} has no proof: {e}", self.title)));
        if let Some(expected) = self.expected {
            assert_eq!(
                run.output, expected,
                "{}: the output is the native reference's",
                self.title
            );
        }
        run
    }

    /// Prove and verify the run, and print the report.
    ///
    /// Proving runs one discarded warmup pass, then `plan.repeat` measured passes, the last one traced.
    pub fn run(&self, prover: &Prover, plan: Plan) {
        let (
            ProvenRun {
                proof, output, stats, ..
            },
            prove_time,
        ) = plan.warm_then_measure(|last| {
            let _quiet = (!last).then(bench::suppress_tracing);
            self.prove(prover)
        });
        let (_, verify_time) = Plan::new(plan.repeat, 0).measure_quiet(|last| {
            let _quiet = (!last).then(bench::suppress_tracing);
            self.program.verify(output, &proof).expect("the proof verifies");
        });

        let cycles = stats.cycles();
        let seconds = prove_time.mean();
        println!("{}", self.title);
        println!(
            "  advice                      : {} words",
            pretty_integer(&self.advice.len())
        );
        println!("  output                      : {output}");
        print!("  cycles (RISC-V)             : {}", pretty_integer(&cycles));
        if let Some(Items { count, name }) = self.items {
            print!("   {} per {name}", pretty_f64(cycles as f64 / count as f64));
        }
        println!();
        // Rows per table, then the committed witness: what the prover pays for.
        println!("    details                   : {}", stats.details());
        let proof_bytes = proof.to_bytes().len();
        println!("  proof size                  : {:.1} KiB", proof_bytes as f64 / 1024.0);
        print!(
            "  proving                     : {} s{}   {} cycles/s",
            pretty_f64(seconds),
            prove_time.spread(),
            pretty_integer(&((cycles as f64 / seconds).round() as u64))
        );
        if let Some(Items { count, name }) = self.items {
            print!("   {} {name}s/s", pretty_f64(count as f64 / seconds));
        }
        println!(
            "      peak memory {} GiB",
            pretty_f64(bench::peak_rss_bytes() as f64 / (1u64 << 30) as f64)
        );
        println!(
            "  verifying                   : {} ms",
            pretty_f64(verify_time.mean() * 1000.0)
        );
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use leanvm::Rate;

    #[test]
    fn the_workloads_prove() {
        // End to end: proven, verified, and the output the native reference's.
        let prover = Prover::new(Rate::MIN);
        for workload in [
            Workload::fibonacci(200_000),
            Workload::leanxmss(2),
            Workload::leansphincs(1),
            Workload::falcon(1),
        ] {
            workload.run(&prover, Plan::default());
        }
    }

    #[test]
    fn counting_a_run_agrees_with_its_trace() {
        // Measuring counts rows without recording them, which must match the rows the trace records.
        for workload in [Workload::leanxmss(2), Workload::leansphincs(1), Workload::leanda(1)] {
            let exec = workload.program.execute(&workload.advice).expect("the run halts");
            let stats = workload.program.measure(&workload.advice).expect("the run halts");
            assert_eq!(stats.base_counts, exec.base_counts, "{}", workload.title);
            assert_eq!(stats.proven_rows, exec.proven_rows, "{}", workload.title);
        }
    }
}
