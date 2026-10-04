//! The hierarchical trace tree the benchmark binaries print with `--tracing`.

use crate::stages::Stages;
use primitives::pretty_f64;
use std::fmt::Error;
use std::sync::atomic::{AtomicBool, Ordering};
use std::time::Duration;
use tracing_forest::printer::Pretty;
use tracing_forest::tree::Tree;
use tracing_forest::util::LevelFilter;
use tracing_forest::{ForestLayer, Formatter, PrettyPrinter};
use tracing_subscriber::filter::dynamic_filter_fn;
use tracing_subscriber::layer::SubscriberExt;
use tracing_subscriber::util::SubscriberInitExt;
use tracing_subscriber::{EnvFilter, Layer, Registry};

fn format_trace_tree(tree: &Tree) -> Result<String, Error> {
    let rendered = Pretty.fmt(tree)?;
    let mut percentages = Vec::new();
    collect_parent_percentages(tree, None, &mut percentages);
    Ok(rewrite_trace_percentages(&rendered, &percentages))
}

fn collect_parent_percentages(tree: &Tree, parent_duration: Option<Duration>, percentages: &mut Vec<f64>) {
    let Tree::Span(span) = tree else {
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
static TRACE_SUPPRESSED: AtomicBool = AtomicBool::new(false);

/// Suppress trace-tree output until the returned guard is dropped.
///
/// A benchmark pass is run several times ([`crate::Plan`]: one warmup plus
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
    TRACE_SUPPRESSED.store(true, Ordering::Relaxed);
    TraceSuppressed
}

/// Guard returned by [`suppress_tracing`].
pub struct TraceSuppressed;

impl Drop for TraceSuppressed {
    fn drop(&mut self) {
        TRACE_SUPPRESSED.store(false, Ordering::Relaxed);
    }
}

/// Install the hierarchical tracing subscriber used by benchmark binaries.
///
/// The default level is `INFO`; `RUST_LOG` can override it. Repeated calls are
/// harmless: if another global subscriber is already installed, this leaves it
/// unchanged. Output pauses while a [`suppress_tracing`] guard is alive; the
/// filter is dynamic (never cached per callsite) so the same callsite can be
/// recorded on one pass and skipped on the next. It also times the stages
/// [`crate::time_stages`] names, on every pass.
pub fn init_tracing() {
    let env_filter = EnvFilter::builder()
        .with_default_directive(LevelFilter::INFO.into())
        .from_env_lossy();

    let forest = ForestLayer::from(PrettyPrinter::new().formatter(format_trace_tree))
        .with_filter(dynamic_filter_fn(|_, _| !TRACE_SUPPRESSED.load(Ordering::Relaxed)));

    let _ = Registry::default()
        .with(env_filter)
        .with(forest)
        .with(Stages)
        .try_init();
}

/// [`init_tracing`] when `BENCH_TRACING` is set: the `benches/` targets'
/// counterpart of the CLI's `--tracing`.
pub fn init_tracing_from_env() {
    if std::env::var_os("BENCH_TRACING").is_some() {
        init_tracing();
    }
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
