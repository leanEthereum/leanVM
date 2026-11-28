//! This tree as the [`isa::Prover`] the shared crates (`aggregation`, `lean_vm`) run on.

use crate::cpu::{self, from_scalar, to_scalar};
use primitives::field::{F64, F128, F128Unreduced};
use verifier::E;

/// The stable prover.
pub struct StableProver;

impl isa::Prover for StableProver {
    const NAME: &'static str = "stable";
    type Error = cpu::ProveError;

    fn init() {
        parallel::init();
    }

    fn set_num_threads(n: usize) {
        parallel::set_num_threads(n)
    }

    fn prove(
        program: &isa::Program,
        witness: &[(String, Vec<Vec<E>>)],
        public_input: [E; 2],
        log_inv_rate: usize,
    ) -> Result<(verifier::Proof, isa::Stats), cpu::ProveError> {
        cpu::prove_scalars(program, witness, public_input.map(from_scalar), log_inv_rate)
    }

    fn map_collect<T: Send>(n: usize, f: impl Fn(usize) -> T + Sync) -> Vec<T> {
        parallel::map_collect(n, f)
    }

    fn combine_rows(rows: &[u64], weights: &[E]) -> Vec<E> {
        let width = rows.len() / weights.len();
        let weights: Vec<F128> = weights.iter().copied().map(from_scalar).collect();
        let partial = parallel::fold_reduce(
            weights.len(),
            || vec![F128Unreduced::ZERO; width],
            |acc: &mut Vec<F128Unreduced>, r| {
                for (acc, &word) in acc.iter_mut().zip(&rows[r * width..][..width]) {
                    *acc ^= weights[r].mul_base_unreduced(F64(word));
                }
            },
            |mut a, b| {
                a.iter_mut().zip(b).for_each(|(a, b)| *a ^= b);
                a
            },
        );
        partial.into_iter().map(|sum| to_scalar(&sum.reduce())).collect()
    }

    fn dot_rows(rows: &[u64], weights: &[E]) -> Vec<E> {
        let weights: Vec<F128> = weights.iter().copied().map(from_scalar).collect();
        let width = weights.len();
        parallel::map_collect(rows.len() / width, |i| {
            let dot = rows[i * width..][..width]
                .iter()
                .zip(&weights)
                .fold(F128Unreduced::ZERO, |sum, (&word, &weight)| {
                    sum ^ weight.mul_base_unreduced(F64(word))
                });
            to_scalar(&dot.reduce())
        })
    }
}
