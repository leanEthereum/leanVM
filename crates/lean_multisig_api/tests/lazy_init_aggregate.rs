//! `aggregate` must initialize the aggregation bytecode itself, before `codec::classify` runs.
//!
//! In its own file so that it owns its process; see `lazy_init_verify.rs` for why that is the
//! only arrangement that can observe a `OnceLock`.
//!
//! The ordering matters here as much as the call: `classify` parses supplied aggregates, and
//! with the lock empty every one of them decodes as `None` and is reported as
//! `Error::MalformedEntry`. Initializing after `classify` would therefore look perfectly correct
//! to every test that supplies no aggregate.

#[test]
fn aggregate_initializes_the_bytecode() {
    // Empty input, so this returns `Error::Empty` from inside `classify` — before the planner
    // and before any proving. That early return is exactly what makes this discriminating: an
    // `init` placed after `classify` would never run here.
    let _ = lean_multisig_api::aggregate(vec![], vec![], [0u8; 32], 0);

    // Panics if the lock is still empty.
    let _ = rec_aggregation::get_aggregation_bytecode();
}
