//! This tree as the [`isa::Prover`] the shared crates (`rec_aggregation`, `lean_da`, `leanvm`) run on.

use crate::cpu::{self, from_scalar, to_scalar};
use ::pcs::ntt::AdditiveNttF64;
use primitives::cast_slice_mut;
use primitives::field::{F64, F128, F128Unreduced};
use verifier::E;

/// The stable prover.
pub struct Stable;

/// Rows [`Stable::combine_rows`] adds into its accumulators between two reads of them.
const GROUP: usize = 8;

impl isa::Prover for Stable {
    type Program = cpu::Program;

    fn init() {
        parallel::init();
    }

    fn assemble(program: isa::CompiledProgram) -> cpu::Program {
        cpu::Program::from(program)
    }

    fn set_witness(program: &mut cpu::Program, name: &str, entries: Vec<Vec<E>>) {
        let entries = entries
            .into_iter()
            .map(|entry| entry.into_iter().map(from_scalar).collect());
        program.set_witness(name, entries.collect());
    }

    fn prove(
        program: &cpu::Program,
        public_input: [E; 2],
        log_inv_rate: usize,
    ) -> Result<(verifier::Proof, isa::Stats), String> {
        let (proof, stats) =
            cpu::prove(program, public_input.map(from_scalar), log_inv_rate).map_err(|e| e.to_string())?;
        let stats = isa::Stats {
            cycles: stats.cycles,
            rows: stats.rows,
            committed: stats.committed,
            log_mem: stats.log_mem,
            mem_used: stats.mem_used,
            bytecode: stats.bytecode,
        };
        Ok((cpu::scalar_proof(&proof), stats))
    }

    fn map_collect<T: Send>(n: usize, f: impl Fn(usize) -> T + Sync) -> Vec<T> {
        parallel::map_collect(n, f)
    }

    fn mul(a: E, b: E) -> E {
        to_scalar(&(from_scalar(a) * from_scalar(b)))
    }

    fn combine_rows(rows: &[u64], weights: &[E]) -> Vec<E> {
        let width = rows.len() / weights.len();
        let weights: Vec<F128> = weights.iter().copied().map(from_scalar).collect();
        let (groups, weights) = (rows.chunks(GROUP * width), weights.chunks(GROUP));
        let (groups, weights): (Vec<_>, Vec<_>) = (groups.collect(), weights.collect());
        let partial = parallel::fold_reduce(
            groups.len(),
            || vec![F128Unreduced::ZERO; width],
            |acc: &mut Vec<F128Unreduced>, g| {
                for (&weight, row) in weights[g].iter().zip(groups[g].chunks(width)) {
                    for (acc, &word) in acc.iter_mut().zip(row) {
                        *acc ^= weight.mul_base_unreduced(F64(word));
                    }
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
        let rows: Vec<&[u64]> = rows.chunks(weights.len()).collect();
        parallel::map_collect(rows.len(), |i| {
            let dot = rows[i]
                .iter()
                .zip(&weights)
                .fold(F128Unreduced::ZERO, |sum, (&word, &weight)| {
                    sum ^ weight.mul_base_unreduced(F64(word))
                });
            to_scalar(&dot.reduce())
        })
    }

    fn encode_rows(symbols: &[u128], log_k: usize) -> Vec<u128> {
        let (k, n) = (1 << log_k, symbols.len() >> log_k);
        if n == 0 {
            return Vec::new();
        }
        // Row `i` holds symbol `i` of every input row: a symbol's words in memory are its limbs, low first, so each
        // limb of each input row is one lane of the transforms.
        let mut table: Vec<u128> = parallel::map_collect(2 * k * n, |j| {
            let (i, row) = (j / n, j % n);
            if i < k { symbols[row * k + i] } else { 0 }
        });
        let words = cast_slice_mut::<u128, F64>(&mut table);
        AdditiveNttF64::standard(log_k).inverse_transform(&mut words[..2 * k * n], 2 * n);
        AdditiveNttF64::standard(log_k + 1).encode_interleaved_in_place(words, 2 * n, 1);
        parallel::map_collect(2 * k * n, |j| table[(j % (2 * k)) * n + j / (2 * k)])
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use isa::Prover;

    /// The payload is the codeword's first half, and each limb is a codeword of its own: its novel-basis coefficients
    /// vanish from `k` on.
    #[test]
    fn encoding_preserves_payload_and_degree_bound() {
        Stable::init();
        let log_k = 13;
        let payload: Vec<u128> = (0..3u128 << log_k)
            .map(|i| 0x9E37_79B9_7F4A_7C15_F39C_C060_5CED_C835u128.wrapping_mul(i + 1))
            .collect();
        let codewords = Stable::encode_rows(&payload, log_k);
        let ntt = AdditiveNttF64::standard(log_k + 1);
        for (row, codeword) in payload.chunks(1 << log_k).zip(codewords.chunks(2 << log_k)) {
            assert_eq!(&codeword[..1 << log_k], row);
            for shift in [0, 64] {
                let mut limb: Vec<F64> = codeword.iter().map(|&s| F64((s >> shift) as u64)).collect();
                ntt.inverse_transform(&mut limb, 1);
                assert!(limb[1 << log_k..].iter().all(|&x| x == F64::ZERO));
            }
        }
    }
}
