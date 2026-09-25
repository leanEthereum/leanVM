//! Shared primitives: field kernels, bit transposes, multilinear helpers,
//! benchmark timing, and small integer utilities.

pub mod bench;
pub mod bits;
pub mod field;
pub mod hash;
pub mod keccak;
pub mod multilinear;
pub mod stream;

#[cfg(feature = "test-util")]
pub mod test_rng;

fn format_trace_tree(tree: &tracing_forest::tree::Tree) -> Result<String, std::fmt::Error> {
    use tracing_forest::Formatter;

    let rendered = tracing_forest::printer::Pretty.fmt(tree)?;
    let mut percentages = Vec::new();
    collect_parent_percentages(tree, None, &mut percentages);
    Ok(rewrite_trace_percentages(&rendered, &percentages))
}

fn collect_parent_percentages(
    tree: &tracing_forest::tree::Tree,
    parent_duration: Option<std::time::Duration>,
    percentages: &mut Vec<f64>,
) {
    let tracing_forest::tree::Tree::Span(span) = tree else {
        return;
    };

    let percentage = match parent_duration {
        None => 100.0,
        Some(duration) if duration.is_zero() => 0.0,
        Some(duration) => 100.0 * span.total_duration().as_nanos() as f64 / duration.as_nanos() as f64,
    };
    percentages.push(percentage);

    for node in span.nodes() {
        collect_parent_percentages(node, Some(span.total_duration()), percentages);
    }
}

/// Replace tracing-forest's root-relative percentages (and its optional self
/// percentage) with one percentage relative to the span's direct parent.
fn rewrite_trace_percentages(rendered: &str, percentages: &[f64]) -> String {
    let mut output = String::with_capacity(rendered.len());
    let mut percentages = percentages.iter();

    for segment in rendered.split_inclusive('\n') {
        let (line, newline) = segment.strip_suffix('\n').map_or((segment, ""), |line| (line, "\n"));

        let timing = line.find(" | ").and_then(|separator| {
            let value_start = separator + " | ".len();
            let values = &line[value_start..];
            let percent_end = values.find("% ]")?;
            let displayed = &values[..percent_end];
            let displayed_total = displayed.rsplit("% / ").next()?;

            displayed_total
                .parse::<f64>()
                .ok()
                .map(|_| (value_start, value_start + percent_end))
        });

        if let Some((value_start, percent_end)) = timing {
            let percentage = percentages
                .next()
                .expect("trace formatter found more spans than trace-tree timings");
            output.push_str(&line[..value_start]);
            output.push_str(&pretty_f64(*percentage));
            output.push_str(&line[percent_end..]);
        } else {
            output.push_str(line);
        }
        output.push_str(newline);
    }

    assert!(
        percentages.next().is_none(),
        "trace formatter found fewer spans than trace-tree timings"
    );
    output
}

/// Set while [`suppress_tracing`]'s guard is alive; read by the trace tree's
/// filter on every span and event.
static TRACE_SUPPRESSED: std::sync::atomic::AtomicBool = std::sync::atomic::AtomicBool::new(false);

/// Suppress trace-tree output until the returned guard is dropped.
///
/// A benchmark pass is run several times ([`bench::Plan`]: one warmup plus
/// `repeat` measured passes), so with `--tracing` the tree would carry one
/// subtree per pass and say nothing extra. Wrapping every pass but the final
/// measured one in this guard leaves exactly one tree, for the proof the report's
/// timings are about. A span created while suppressed is never recorded, so it
/// cannot reappear inside the surviving tree either.
///
/// Only that pass then pays the tree's recording cost, which is immaterial against
/// a multi-second proof and is anyway why `--tracing` is a diagnostic mode rather
/// than the one to quote timings from.
#[must_use = "tracing resumes as soon as the guard is dropped"]
pub fn suppress_tracing() -> TraceSuppressed {
    TRACE_SUPPRESSED.store(true, std::sync::atomic::Ordering::Relaxed);
    TraceSuppressed
}

/// Guard returned by [`suppress_tracing`].
pub struct TraceSuppressed;

impl Drop for TraceSuppressed {
    fn drop(&mut self) {
        TRACE_SUPPRESSED.store(false, std::sync::atomic::Ordering::Relaxed);
    }
}

/// Install the hierarchical tracing subscriber used by benchmark binaries.
///
/// The default level is `INFO`; `RUST_LOG` can override it. Repeated calls are
/// harmless: if another global subscriber is already installed, this leaves it
/// unchanged. Output pauses while a [`suppress_tracing`] guard is alive; the
/// filter is dynamic (never cached per callsite) so the same callsite can be
/// recorded on one pass and skipped on the next.
pub fn init_tracing() {
    use tracing_forest::{ForestLayer, PrettyPrinter, util::LevelFilter};
    use tracing_subscriber::{
        EnvFilter, Layer, Registry, filter::dynamic_filter_fn, layer::SubscriberExt, util::SubscriberInitExt,
    };

    let env_filter = EnvFilter::builder()
        .with_default_directive(LevelFilter::INFO.into())
        .from_env_lossy();

    let forest =
        ForestLayer::from(PrettyPrinter::new().formatter(format_trace_tree)).with_filter(dynamic_filter_fn(|_, _| {
            !TRACE_SUPPRESSED.load(std::sync::atomic::Ordering::Relaxed)
        }));

    let _ = Registry::default().with(env_filter).with(forest).try_init();
}

/// Format an integer with comma-separated groups of three decimal digits.
///
/// This accepts every standard signed and unsigned integer type through its
/// [`ToString`] representation. A leading sign is preserved.
///
/// ```
/// use primitives::pretty_integer;
///
/// assert_eq!(pretty_integer(16_769_432), "16,769,432");
/// assert_eq!(pretty_integer(-12_345), "-12,345");
/// ```
pub fn pretty_integer(value: impl ToString) -> String {
    let raw = value.to_string();
    let (sign, digits) = match raw.as_bytes().first() {
        Some(b'+' | b'-') => raw.split_at(1),
        _ => ("", raw.as_str()),
    };

    // Keep misuse benign: callers are expected to pass integers, but returning
    // the original representation is more useful than mangling another type.
    if !digits.bytes().all(|b| b.is_ascii_digit()) {
        return raw;
    }

    let separators = digits.len().saturating_sub(1) / 3;
    let mut out = String::with_capacity(raw.len() + separators);
    out.push_str(sign);
    for (i, byte) in digits.bytes().enumerate() {
        if i != 0 && (digits.len() - i).is_multiple_of(3) {
            out.push(',');
        }
        out.push(byte as char);
    }
    out
}

/// Format a finite floating-point value with a grouped integer part and at
/// most three meaningful fractional digits. Leading zeroes after the decimal
/// point do not consume that budget, so tiny nonzero values remain visible.
/// The fractional part is rounded and trailing zeroes are omitted; non-finite
/// values retain Rust's standard spelling.
///
/// ```
/// use primitives::pretty_f64;
///
/// assert_eq!(pretty_f64(2.186_834_667), "2.187");
/// assert_eq!(pretty_f64(12_345.6), "12,345.6");
/// ```
pub fn pretty_f64(value: f64) -> String {
    if !value.is_finite() {
        return value.to_string();
    }

    let magnitude = value.abs();
    let precision = if magnitude == 0.0 || magnitude >= 1.0 {
        3
    } else {
        // Keep the first three nonzero-place digits: 0.001234 needs five
        // decimal places, while 0.000000000012345 needs thirteen.
        ((-magnitude.log10().floor()) as usize).saturating_add(2)
    };
    let mut raw = format!("{value:.precision$}");
    while raw.contains('.') && raw.ends_with('0') {
        raw.pop();
    }
    if raw.ends_with('.') {
        raw.pop();
    }
    if raw == "-0" {
        return "0".to_string();
    }

    let (integer, fraction) = raw
        .split_once('.')
        .map_or((raw.as_str(), None), |(integer, fraction)| (integer, Some(fraction)));
    let mut out = pretty_integer(integer);
    if let Some(fraction) = fraction {
        out.push('.');
        out.push_str(fraction);
    }
    out
}

#[cfg(test)]
mod tracing_tests {
    use super::rewrite_trace_percentages;

    #[test]
    fn trace_output_uses_parent_relative_percentage() {
        let trace = concat!(
            "INFO     Prove [ 3.38s | 73.12% ]\n",
            "INFO     ┕━ PCS open [ 1.14s | 11.35% / 33.74% ]\n",
            "INFO        ┕━ Sumcheck round [ 17.6ms | 0.53% ] round: 0\n",
        );

        assert_eq!(
            rewrite_trace_percentages(trace, &[100.0, 33.727_810, 1.543_860]),
            concat!(
                "INFO     Prove [ 3.38s | 100% ]\n",
                "INFO     ┕━ PCS open [ 1.14s | 33.728% ]\n",
                "INFO        ┕━ Sumcheck round [ 17.6ms | 1.544% ] round: 0\n",
            )
        );
    }
}

#[cfg(test)]
mod formatting_tests {
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
        assert_eq!(pretty_integer("+123456"), "+123,456");
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

/// `log2` of a power of two (panics otherwise).
pub fn log2_strict_usize(n: usize) -> usize {
    assert!(n.is_power_of_two(), "not a power of two: {n}");
    n.trailing_zeros() as usize
}

/// `ceil(log2(n))`, defined as 0 for `n <= 1`.
pub fn log2_ceil_usize(n: usize) -> usize {
    if n <= 1 { 0 } else { (n - 1).ilog2() as usize + 1 }
}

/// Arena-backed parallel `(0..n).map(build).collect()`: one allocation on the
/// calling thread, filled in place by the workers: no per-worker intermediate
/// vectors to allocate and copy out of. This lives here rather than in
/// `zk_alloc` so the allocator itself stays free of a thread-pool dependency.
pub fn par_collect_arena<T: Send>(n: usize, build: impl Fn(usize) -> T + Sync) -> zk_alloc::ArenaVec<T> {
    // SAFETY: the fill below writes every slot in `0..n` exactly once, and
    // the dispatch joins before the buffer is observable.
    let mut out = unsafe { zk_alloc::ArenaVec::uninitialized(n) };
    parallel::fill(&mut out, build);
    out
}
