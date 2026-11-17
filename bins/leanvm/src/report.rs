//! The pieces every workload's benchmark report ends with.
//!
//! Each caller drops its root tracing span before printing: tracing-forest
//! renders its tree only when that span closes, so the complete trace has to be
//! flushed above the report.

use isa::pretty_f64;

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

/// One line of per-table instruction counts and shares, largest first, followed by memory, bytecode (`code_len`
/// instructions) and committed-witness sizes. Zero-count tables are omitted.
pub fn details(stats: &isa::Stats, code_len: usize) -> String {
    if stats.cycles == 0 {
        return "-".to_string();
    }
    let mut shares: Vec<(&str, usize)> = isa::Stats::TABLES
        .iter()
        .zip(&stats.table_heights)
        .filter(|&(_, &c)| c > 0)
        .map(|(&name, &c)| (name, c))
        .collect();
    shares.sort_unstable_by_key(|&(_, c)| std::cmp::Reverse(c));
    let log2 = |n: usize| pretty_f64((n.max(1) as f64).log2());
    let mut parts: Vec<String> = shares
        .iter()
        .map(|&(name, c)| format!("{name} 2^{} ({:.1}%)", log2(c), 100.0 * c as f64 / stats.cycles as f64))
        .collect();
    parts.push(format!("MEMORY 2^{}", log2(stats.memory_used)));
    parts.push(format!("BYTECODE 2^{}", log2(code_len)));
    parts.push(format!("TOTAL_COMMITTED 2^{}", log2(stats.total_committed)));
    parts.join("  ")
}

pub fn print_proof_size(bytes: usize) {
    println!("  proof size                  : {:.1} KiB", bytes as f64 / 1024.0);
}
