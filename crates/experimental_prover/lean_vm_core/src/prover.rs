//! This tree as the [`isa::Prover`] the shared crates (`aggregation`, `lean_vm`) run on.

use crate::cpu::{self, from_scalar, to_scalar};
use primitives::cast_slice;
use primitives::field::{F64, F64x8, F128, F128x8, Prod8, Weights8, dot_base};
use verifier::E;

/// The experimental prover.
pub struct ExperimentalProver;

/// Rows [`ExperimentalProver::combine_rows`] adds into its accumulators between two reads of them.
const GROUP: usize = 8;

impl isa::Prover for ExperimentalProver {
    fn init() {
        parallel::init();
    }

    fn prove(
        program: &isa::Program,
        witness: &[(String, Vec<Vec<E>>)],
        public_input: [E; 2],
        log_inv_rate: usize,
    ) -> Result<(verifier::Proof, isa::Stats), String> {
        let witness: Vec<(String, Vec<Vec<F128>>)> = witness
            .iter()
            .map(|(name, entries)| {
                let entries = entries
                    .iter()
                    .map(|entry| entry.iter().copied().map(from_scalar).collect());
                (name.clone(), entries.collect())
            })
            .collect();
        cpu::prove(program, &witness, public_input.map(from_scalar), log_inv_rate).map_err(|e| e.to_string())
    }

    fn map_collect<T: Send>(n: usize, f: impl Fn(usize) -> T + Sync) -> Vec<T> {
        parallel::map_collect(n, f)
    }

    fn combine_rows(rows: &[u64], weights: &[E]) -> Vec<E> {
        let width = rows.len() / weights.len();
        assert!(
            width.is_multiple_of(8) && weights.len().is_multiple_of(GROUP),
            "whole groups of whole lanes"
        );
        let rows: &[F64] = cast_slice(rows);
        let weights: Vec<F128> = weights.iter().copied().map(from_scalar).collect();
        let (groups, weights) = (
            rows.chunks(GROUP * width).collect::<Vec<_>>(),
            weights.as_chunks::<GROUP>().0,
        );
        let partial = parallel::fold_reduce(
            groups.len(),
            || vec![Prod8::ZERO; width / 8],
            |acc: &mut Vec<Prod8>, g| {
                let splats = weights[g].map(F128x8::splat);
                for (x, acc) in acc.iter_mut().enumerate() {
                    for (splat, row) in splats.iter().zip(groups[g].chunks(width)) {
                        *acc ^= splat.mul_base_unreduced(F64x8::from_array(&row.as_chunks::<8>().0[x]));
                    }
                }
            },
            |mut a, b| {
                a.iter_mut().zip(b).for_each(|(a, b)| *a ^= b);
                a
            },
        );
        partial
            .into_iter()
            .flat_map(|p| p.reduce_lanes().to_array())
            .map(|x| to_scalar(&x))
            .collect()
    }

    fn dot_rows(rows: &[u64], weights: &[E]) -> Vec<E> {
        let weights: Vec<F128> = weights.iter().copied().map(from_scalar).collect();
        let packed: Vec<Weights8> = weights.as_chunks::<8>().0.iter().map(Weights8::new).collect();
        let rows: &[F64] = cast_slice(rows);
        let rows: Vec<&[F64]> = rows.chunks(weights.len()).collect();
        parallel::map_collect(rows.len(), |i| to_scalar(&dot_base(&packed, rows[i]).reduce()))
    }
}
