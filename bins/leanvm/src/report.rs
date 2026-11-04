//! The pieces every workload's benchmark report ends with.
//!
//! Each caller drops its root tracing span before printing: tracing-forest
//! renders its tree only when that span closes, so the complete trace has to be
//! flushed above the report.

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
    pretty_f64(bench::peak_rss_bytes() as f64 / (1u64 << 30) as f64)
}

pub fn print_proof_size(bytes: usize) {
    println!("  proof size                  : {:.1} KiB", bytes as f64 / 1024.0);
}
