//! The prover's stage times: how long each direct child of a root span ran, recorded by a
//! `tracing` layer that sees spans only, never events.

use std::sync::{Mutex, OnceLock};
use std::time::{Duration, Instant};
use tracing::span::{Attributes, Id};
use tracing::{Level, Subscriber};
use tracing_subscriber::filter::filter_fn;
use tracing_subscriber::layer::{Context, SubscriberExt};
use tracing_subscriber::registry::LookupSpan;
use tracing_subscriber::util::SubscriberInitExt;
use tracing_subscriber::{Layer, Registry};

/// The root span's name, set by [`time_stages`].
static ROOT: OnceLock<&'static str> = OnceLock::new();

/// The stages that closed since the last [`take_stages`].
static STAGES: Mutex<Vec<(&'static str, Duration)>> = Mutex::new(Vec::new());

/// When a stage opened, kept in its span's extensions.
struct Opened(Instant);

/// Times every span whose parent is named [`ROOT`].
pub(crate) struct Stages;

impl<S: Subscriber + for<'a> LookupSpan<'a>> Layer<S> for Stages {
    fn on_new_span(&self, _: &Attributes<'_>, id: &Id, ctx: Context<'_, S>) {
        let Some(&root) = ROOT.get() else { return };
        let span = ctx.span(id).expect("a new span is registered");
        if span.parent().is_some_and(|parent| parent.name() == root) {
            span.extensions_mut().insert(Opened(Instant::now()));
        }
    }

    fn on_close(&self, id: Id, ctx: Context<'_, S>) {
        let span = ctx.span(&id).expect("a closing span is registered");
        if let Some(Opened(opened)) = span.extensions().get::<Opened>() {
            STAGES.lock().unwrap().push((span.name(), opened.elapsed()));
        }
    }
}

/// Time the stages of every span named `root`: its direct children, by name, from when each
/// is created to when it closes, collected by [`take_stages`].
///
/// Installs a subscriber enabling `INFO` spans and no events, unless one is installed
/// already: [`crate::init_tracing`]'s times the stages too.
pub fn time_stages(root: &'static str) {
    ROOT.set(root).expect("one root span per process");
    let spans = filter_fn(|metadata| metadata.is_span() && *metadata.level() <= Level::INFO);
    let _ = Registry::default().with(Stages.with_filter(spans)).try_init();
}

/// The stages that closed since the last call, in the order they closed.
pub fn take_stages() -> Vec<(&'static str, Duration)> {
    std::mem::take(&mut STAGES.lock().unwrap())
}
