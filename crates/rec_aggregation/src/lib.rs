//! Recursive aggregation of XMSS and SPHINCS signatures ([`aggregation`]) and
//! the harnesses that measure it ([`benchmark`]), plus the Fibonacci demo. One
//! zkDSL guest (`guests/lean_ethereum.py`) serves every node of an aggregation tree,
//! and knows both schemes.

pub mod aggregation;
pub mod benchmark;
pub mod fibonacci;
/// The BLAKE2s hash chain, proven end to end. A `src` module rather than its own
/// test binary so it shares the process, and so the slow flock circuit build,
/// with the other workloads.
#[cfg(test)]
mod hash_chain;
pub mod signers_cache;

pub use aggregation::{
    AggregateSignature, AggregateVerifyError, AggregationError, MAX_EPOCHS, MAX_KEYS, MAX_RECURSIONS, SphincsSigner,
    WireKeys, XmssGroup, aggregate, warm_up,
};
pub use benchmark::{run_aggregation, run_recursion};
pub use fibonacci::run_fibonacci;

/// The pieces every workload's benchmark report ends with.
///
/// Each caller drops its root tracing span before printing: tracing-forest
/// renders its tree only when that span closes, so the complete trace has to be
/// flushed above the report.
mod report {
    use primitives::pretty_f64;

    /// A count as a power of two, or a dash when the opcode never ran.
    pub fn pow(x: usize) -> String {
        if x == 0 {
            "     -".into()
        } else {
            format!("2^{}", pretty_f64((x as f64).log2()))
        }
    }

    /// Peak resident set size, in GiB.
    pub fn peak_gib() -> String {
        pretty_f64(primitives::bench::peak_rss_bytes() as f64 / (1u64 << 30) as f64)
    }

    pub fn print_proof_size<T: serde::Serialize>(proof: &T) {
        let bytes = bincode::serialized_size(proof).expect("proof is serializable");
        println!("  proof size                  : {:.1} KiB", bytes as f64 / 1024.0);
    }
}
