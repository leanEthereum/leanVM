//! The hierarchical trace tree the benchmark binaries print with `--tracing`.

use crate::heap::{self, HeapWindow};
use crate::stages::Stages;
use primitives::{pretty_f64, pretty_integer};
use std::cell::RefCell;
use std::fmt::Error;
use std::sync::atomic::{AtomicBool, Ordering};
use std::time::Duration;
use tracing::Subscriber;
use tracing::span::{Attributes, Id};
use tracing_forest::printer::Pretty;
use tracing_forest::tree::Tree;
use tracing_forest::util::LevelFilter;
use tracing_forest::{ForestLayer, Formatter, PrettyPrinter};
use tracing_subscriber::filter::dynamic_filter_fn;
use tracing_subscriber::layer::{Context, Filter, SubscriberExt};
use tracing_subscriber::registry::LookupSpan;
use tracing_subscriber::util::SubscriberInitExt;
use tracing_subscriber::{EnvFilter, Layer, Registry};

/// A closed span's heap: the forest's tree again, spans only, built by [`HeapSpans`].
struct HeapNode {
    /// The live bytes when the span opened, and the most while it was open.
    opened: isize,
    peak: isize,
    allocations: u64,
    children: Vec<Self>,
}

/// An open span's window, and its children that closed.
struct OpenSpan {
    window: HeapWindow,
    children: Vec<HeapNode>,
}

thread_local! {
    /// The root span that closed last on this thread, which the forest prints next.
    static CLOSED_ROOT: RefCell<Option<HeapNode>> = const { RefCell::new(None) };
}

/// Keeps each span's heap window, from when it is created to when it closes. Installed before the forest, so a root's heap is
/// in [`CLOSED_ROOT`] when the forest prints it, and with the forest's filter, so it sees the spans the forest sees.
struct HeapSpans;

impl<S: Subscriber + for<'a> LookupSpan<'a>> Layer<S> for HeapSpans {
    fn on_new_span(&self, _: &Attributes<'_>, id: &Id, ctx: Context<'_, S>) {
        let span = ctx.span(id).expect("a new span is registered");
        span.extensions_mut().insert(OpenSpan {
            window: HeapWindow::open(),
            children: Vec::new(),
        });
    }

    fn on_close(&self, id: Id, ctx: Context<'_, S>) {
        let span = ctx.span(&id).expect("a closing span is registered");
        let Some(open) = span.extensions_mut().remove::<OpenSpan>() else {
            return;
        };
        let opened = open.window.opened_at();
        let (heap, peak) = open.window.close_at();
        let node = HeapNode {
            opened,
            peak,
            allocations: heap.allocations,
            children: open.children,
        };
        match span.parent() {
            Some(parent) => {
                if let Some(parent) = parent.extensions_mut().get_mut::<OpenSpan>() {
                    parent.children.push(node);
                }
            }
            None => CLOSED_ROOT.with_borrow_mut(|root| *root = Some(node)),
        }
    }
}

/// What a span's line shows after its time: its share of its parent's, and, when [`heap::Counting`] is the global allocator,
/// the most bytes live in it above those live when the root opened and the allocations made in it.
#[derive(Clone, Copy, Debug)]
struct Line {
    percentage: f64,
    heap: Option<(u64, u64)>,
}

fn format_trace_tree(tree: &Tree) -> Result<String, Error> {
    let rendered = Pretty.fmt(tree)?;
    let heap = CLOSED_ROOT.take().filter(|_| heap::counting());
    let mut lines = Vec::new();
    collect_lines(
        tree,
        heap.as_ref(),
        heap.as_ref().map_or(0, |root| root.opened),
        None,
        &mut lines,
    );
    Ok(rewrite_trace_lines(&rendered, &lines))
}

fn collect_lines(
    tree: &Tree,
    heap: Option<&HeapNode>,
    root_opened: isize,
    parent_duration: Option<Duration>,
    lines: &mut Vec<Line>,
) {
    let Tree::Span(span) = tree else {
        return;
    };

    let percentage = match parent_duration {
        None => 100.0,
        Some(duration) if duration.is_zero() => 0.0,
        Some(duration) => 100.0 * span.total_duration().as_nanos() as f64 / duration.as_nanos() as f64,
    };
    lines.push(Line {
        percentage,
        heap: heap.map(|node| ((node.peak - root_opened).max(0) as u64, node.allocations)),
    });

    let mut children = heap.map(|node| node.children.iter());
    for node in span.nodes() {
        let child = match node {
            Tree::Span(_) => children.as_mut().and_then(Iterator::next),
            Tree::Event(_) => None,
        };
        collect_lines(node, child, root_opened, Some(span.total_duration()), lines);
    }
}

/// `bytes` in the largest binary unit that leaves at least one of it.
fn pretty_bytes(bytes: u64) -> String {
    let (unit, scale) = [("GiB", 1 << 30), ("MiB", 1 << 20), ("KiB", 1 << 10)]
        .into_iter()
        .find(|&(_, scale)| bytes >= scale)
        .unwrap_or(("B", 1));
    format!("{} {unit}", pretty_f64(bytes as f64 / scale as f64))
}

/// Replace tracing-forest's root-relative percentages (and its optional self
/// percentage) with one percentage relative to the span's direct parent, followed by the span's heap.
fn rewrite_trace_lines(rendered: &str, lines: &[Line]) -> String {
    let mut output = String::with_capacity(rendered.len());
    let mut lines = lines.iter();

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
            let shown = lines
                .next()
                .expect("trace formatter found more spans than trace-tree timings");
            output.push_str(&line[..value_start]);
            output.push_str(&pretty_f64(shown.percentage));
            output.push('%');
            if let Some((peak, allocations)) = shown.heap {
                output.push_str(&format!(
                    " | heap {} | {} allocs",
                    pretty_bytes(peak),
                    pretty_integer(&allocations)
                ));
            }
            output.push_str(&line[percent_end + 1..]);
        } else {
            output.push_str(line);
        }
        output.push_str(newline);
    }

    assert!(
        lines.next().is_none(),
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

/// The trace tree's filter: everything but what a [`suppress_tracing`] guard covers.
fn recorded<S: Subscriber>() -> impl Filter<S> {
    dynamic_filter_fn(|_, _| !TRACE_SUPPRESSED.load(Ordering::Relaxed))
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

    let forest = ForestLayer::from(PrettyPrinter::new().formatter(format_trace_tree)).with_filter(recorded());

    let _ = Registry::default()
        .with(env_filter)
        .with(HeapSpans.with_filter(recorded()))
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
    use super::{Line, rewrite_trace_lines};

    #[test]
    fn trace_output_uses_parent_relative_percentage() {
        let trace = concat!(
            "INFO     Prove [ 3.38s | 73.12% ]\n",
            "INFO     ┕━ PCS open [ 1.14s | 11.35% / 33.74% ]\n",
            "INFO        ┕━ Sumcheck round [ 17.6ms | 0.53% ] round: 0\n",
        );
        let line = |percentage| Line { percentage, heap: None };

        assert_eq!(
            rewrite_trace_lines(trace, &[line(100.0), line(33.727_810), line(1.543_860)]),
            concat!(
                "INFO     Prove [ 3.38s | 100% ]\n",
                "INFO     ┕━ PCS open [ 1.14s | 33.728% ]\n",
                "INFO        ┕━ Sumcheck round [ 17.6ms | 1.544% ] round: 0\n",
            )
        );
    }

    #[test]
    fn trace_output_shows_each_span_heap_after_its_percentage() {
        let trace = concat!(
            "INFO     Prove [ 3.38s | 73.12% ]\n",
            "INFO     ┕━ PCS open [ 1.14s | 11.35% / 33.74% ] round: 0\n",
        );
        let lines = [
            Line {
                percentage: 100.0,
                heap: Some((3 << 29, 12_345)),
            },
            Line {
                percentage: 33.727_810,
                heap: Some((1536, 7)),
            },
        ];

        assert_eq!(
            rewrite_trace_lines(trace, &lines),
            concat!(
                "INFO     Prove [ 3.38s | 100% | heap 1.5 GiB | 12,345 allocs ]\n",
                "INFO     ┕━ PCS open [ 1.14s | 33.728% | heap 1.5 KiB | 7 allocs ] round: 0\n",
            )
        );
    }
}
