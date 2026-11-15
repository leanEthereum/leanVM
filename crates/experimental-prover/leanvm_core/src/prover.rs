//! This tree as the [`isa::Prover`] the shared crates (`rec_aggregation`, `lean_da`, `leanvm`) run on.

use crate::cpu::{self, from_scalar, to_scalar};
use ::pcs::ntt::AdditiveNttF64;
use primitives::field::{F64, F64x8, F128, F128x8, Prod8, Weights8, dot_base};
use primitives::{cast_slice, cast_slice_mut, filled_vec};
use verifier::E;

/// The experimental prover.
pub struct Experimental;

/// Rows [`Experimental::combine_rows`] adds into its accumulators between two reads of them.
const GROUP: usize = 8;

impl isa::Prover for Experimental {
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

    #[inline(always)]
    fn mul(a: E, b: E) -> E {
        to_scalar(&(from_scalar(a) * from_scalar(b)))
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

    fn encode_rows(symbols: &[u128], log_k: usize) -> Vec<u128> {
        let k = 1 << log_k;
        let interpolation = AdditiveNttF64::standard(log_k);
        let ntt = AdditiveNttF64::standard(log_k + 1);
        let mut limbs = vec![F64::ZERO; 2 * k];
        // One row at a time: the transform dispatches internally at any row worth encoding, and the pool panics on a
        // nested dispatch, so the row loop must stay sequential and let the NTT own the parallelism.
        // SAFETY: each codeword is written in full, the coefficients then zeros, before the transform reads it.
        unsafe {
            filled_vec(2 * symbols.len(), |codewords: &mut [u128]| {
                for (row, codeword) in symbols.chunks(k).zip(codewords.chunks_mut(2 * k)) {
                    let (c0, c1) = limbs.split_at_mut(k);
                    for ((&symbol, l0), l1) in row.iter().zip(&mut *c0).zip(&mut *c1) {
                        (*l0, *l1) = (F64(symbol as u64), F64((symbol >> 64) as u64));
                    }
                    interpolation.inverse_transform(c0);
                    interpolation.inverse_transform(c1);
                    // A symbol's words in memory are its limbs, low first.
                    let words = cast_slice_mut::<u128, F64>(codeword);
                    let (low, high) = words.split_at_mut(2 * k);
                    for ((pair, &l0), &l1) in low.as_chunks_mut::<2>().0.iter_mut().zip(&*c0).zip(&*c1) {
                        *pair = [l0, l1];
                    }
                    high.fill(F64::ZERO);
                    ntt.encode_interleaved_in_place(words, 2, 1);
                }
            })
        }
    }
}
