//! The pieces every workload's benchmark report ends with.
//!
//! Each caller drops its root tracing span before printing: tracing-forest
//! renders its tree only when that span closes, so the complete trace has to be
//! flushed above the report.

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

/// One line of per-table instruction counts and shares, largest first, followed by memory, bytecode and
/// committed-witness sizes. Zero-count tables are omitted.
pub fn details(stats: &isa::Stats) -> String {
    if stats.cycles == 0 {
        return "-".to_string();
    }
    let mut shares: Vec<(&str, usize)> = isa::Stats::TABLES
        .iter()
        .zip(&stats.rows)
        .filter(|&(_, &c)| c > 0)
        .map(|(&name, &c)| (name, c))
        .collect();
    shares.sort_unstable_by_key(|&(_, c)| std::cmp::Reverse(c));
    let log2 = |n: usize| pretty_f64((n.max(1) as f64).log2());
    let mut parts: Vec<String> = shares
        .iter()
        .map(|&(name, c)| format!("{name} 2^{} ({:.1}%)", log2(c), 100.0 * c as f64 / stats.cycles as f64))
        .collect();
    parts.push(format!("MEMORY 2^{}", log2(stats.mem_used)));
    parts.push(format!("BYTECODE 2^{}", log2(stats.bytecode)));
    parts.push(format!("TOTAL_COMMITTED 2^{}", log2(stats.committed)));
    parts.join("  ")
}

pub fn print_proof_size(bytes: usize) {
    println!("  proof size                  : {:.1} KiB", bytes as f64 / 1024.0);
}

/// An integer with comma-separated groups of three digits.
pub fn pretty_integer(value: impl ToString) -> String {
    let raw = value.to_string();
    let (sign, digits) = raw.split_at(usize::from(raw.starts_with('-')));
    let mut out = String::from(sign);
    for (i, c) in digits.chars().enumerate() {
        if i != 0 && (digits.len() - i).is_multiple_of(3) {
            out.push(',');
        }
        out.push(c);
    }
    out
}

/// A float with a grouped integer part and at most three meaningful fractional digits, leading zeroes after the
/// point not counted; trailing zeroes are trimmed.
pub fn pretty_f64(value: f64) -> String {
    if !value.is_finite() {
        return value.to_string();
    }
    let magnitude = value.abs();
    let precision = if magnitude == 0.0 || magnitude >= 1.0 {
        3
    } else {
        ((-magnitude.log10().floor()) as usize).saturating_add(2)
    };
    let raw = format!("{value:.precision$}");
    let raw = if raw.contains('.') {
        raw.trim_end_matches('0').trim_end_matches('.')
    } else {
        &raw
    };
    if raw == "-0" {
        return "0".into();
    }
    match raw.split_once('.') {
        Some((integer, fraction)) => format!("{}.{fraction}", pretty_integer(integer)),
        None => pretty_integer(raw),
    }
}
