use tracing::instrument;

use super::*;

// Recompute per-round witness columns from the input columns, 8 rows per
// packed call, parallel over disjoint row ranges.
#[instrument(name = "generate Poseidon8 AIR trace", skip_all)]
pub fn fill_trace_poseidon_8(trace: &mut [ArenaVec<F>]) {
    let n = trace.iter().map(|col| col.len()).max().unwrap_or(0);
    parallel::par_for_each_mut(trace, |_, col| {
        if col.len() != n {
            col.resize(n, F::ZERO);
        }
    });
    if n == 0 {
        return;
    }

    let (head, tail) = trace.split_at_mut(POSEIDON_8_COL_ROUND_START);
    let inputs: [&[F]; WIDTH] = std::array::from_fn(|j| &head[POSEIDON_8_COL_INPUT_START + j][..n]);
    // Disjoint-row-range writes into the aux columns, partitioned by task
    // (same pattern as the segment replay in runner.rs).
    let aux: Vec<parallel::SendPtr<F>> = tail[..AUX_COLS_PER_ROW]
        .iter_mut()
        .map(|col| parallel::SendPtr(col.as_mut_ptr()))
        .collect();

    #[cfg(all(target_arch = "x86_64", target_feature = "avx512f"))]
    {
        use backend::PackedGoldilocksAVX512 as P;
        let n_blocks = n / WITNESS_LANES;
        parallel::for_each_chunk(n_blocks, |start, end| {
            for blk in start..end {
                let i = blk * WITNESS_LANES;
                let state: [P; WIDTH] = std::array::from_fn(|j| P(inputs[j][i..i + WITNESS_LANES].try_into().unwrap()));
                let (vals, _) = compute_poseidon8_witness_packed(state);
                for (k, v) in vals.iter().enumerate() {
                    // SAFETY: row range [i, i+WITNESS_LANES) belongs to this
                    // task alone; every aux column has length n.
                    unsafe { std::ptr::copy_nonoverlapping(v.0.as_ptr(), aux[k].0.add(i), WITNESS_LANES) };
                }
            }
        });
        fill_aux_scalar(&inputs, &aux, n_blocks * WITNESS_LANES, n);
    }

    #[cfg(not(all(target_arch = "x86_64", target_feature = "avx512f")))]
    parallel::for_each_chunk(n, |start, end| fill_aux_scalar(&inputs, &aux, start, end));
}

// Rows are addressed by index across 8 input columns and 86 raw column
// pointers at once — iterator forms don't apply.
#[allow(clippy::needless_range_loop)]
fn fill_aux_scalar(inputs: &[&[F]; WIDTH], aux: &[parallel::SendPtr<F>], start: usize, end: usize) {
    for i in start..end {
        let input: [F; WIDTH] = std::array::from_fn(|j| inputs[j][i]);
        let (vals, _) = compute_poseidon8_witness(input);
        for (k, v) in vals.iter().enumerate() {
            // SAFETY: row `i` is written by exactly one task; columns have length >= end.
            unsafe { *aux[k].0.add(i) = *v };
        }
    }
}
