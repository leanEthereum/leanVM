//! Numbers for people to read: the compiler's listings, a run's debug prints and profile, the benchmarks' reports.

/// An integer with its decimal digits in comma-separated groups of three, a leading `-` kept.
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
/// point not counted, so tiny nonzero values stay visible; rounded, trailing zeroes trimmed, non-finite values in
/// Rust's spelling.
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

#[cfg(test)]
mod tests {
    use super::{pretty_f64, pretty_integer};

    #[test]
    fn pretty_integer_groups_decimal_digits() {
        assert_eq!(pretty_integer(0), "0");
        assert_eq!(pretty_integer(12), "12");
        assert_eq!(pretty_integer(999), "999");
        assert_eq!(pretty_integer(1_000), "1,000");
        assert_eq!(pretty_integer(16_769_432), "16,769,432");
        assert_eq!(
            pretty_integer(u128::MAX),
            "340,282,366,920,938,463,463,374,607,431,768,211,455"
        );
        assert_eq!(pretty_integer(-12_345), "-12,345");
    }

    #[test]
    fn pretty_f64_rounds_groups_and_trims() {
        assert_eq!(pretty_f64(2.186_834_667), "2.187");
        assert_eq!(pretty_f64(12_345.678_9), "12,345.679");
        assert_eq!(pretty_f64(12_345.0), "12,345");
        assert_eq!(pretty_f64(-12_345.6), "-12,345.6");
        assert_eq!(pretty_f64(-0.0), "0");
        assert_eq!(pretty_f64(0.000_000_000_012_345), "0.0000000000123");
        assert_eq!(pretty_f64(f64::INFINITY), "inf");
        assert_eq!(pretty_f64(f64::NEG_INFINITY), "-inf");
        assert_eq!(pretty_f64(f64::NAN), "NaN");
    }
}
