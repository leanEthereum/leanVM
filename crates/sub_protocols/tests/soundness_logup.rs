use backend::{Field, log2_ceil_usize};
use lean_prover::SECURITY_BITS;
use lean_vm::{
    EF, MAX_BYTECODE_LOG_SIZE, MAX_LOG_MEMORY_SIZE, MAX_LOG_N_ROWS_PER_TABLE, max_bus_width_including_bytecode,
    sort_tables_by_height,
};
use std::collections::BTreeMap;
use sub_protocols::compute_total_logup_log_size;

#[test]
fn ensure_logup_soundness_is_suffisant() {
    let max_logup_n_vars = compute_total_logup_log_size(
        MAX_LOG_MEMORY_SIZE,
        MAX_BYTECODE_LOG_SIZE,
        &sort_tables_by_height(&BTreeMap::from(MAX_LOG_N_ROWS_PER_TABLE)),
    );
    dbg!(max_logup_n_vars, EF::bits());
    // TODO explain formula
    let logup_error_bits = max_logup_n_vars + log2_ceil_usize(log2_ceil_usize(max_bus_width_including_bytecode()));
    assert!(SECURITY_BITS + logup_error_bits <= EF::bits());
}
