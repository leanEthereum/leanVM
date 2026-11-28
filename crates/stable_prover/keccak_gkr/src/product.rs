//! Step 1, the product polynomial: the coefficients of
//!
//! ```text
//!     U = sum over packs y, segments m and positions j of eq(point, (y, m)) * weights[j] * chi(y, j)
//!     chi(y, j) = ones * (u[j] + u[j + 2]) + u[j + 1] * u[j + 2]
//! ```
//!
//! on pack `y`'s embeddings, the unprojected `chi`. Nothing knows yet where `U` will be evaluated, so its products
//! meet their weights bit by bit: per block and pack, coefficient `c` of `sum over j of weights[j] * chi(y, j)` is
//! the sum of the weights of the positions whose `chi` has bit `c` set. A run of eight positions' products,
//! transposed to bytes, gives per coefficient a byte of the run's eight bits, which a [`FieldMap`] of the run's
//! weights sends to that sum ([`map_sums`]). A block's sums meet its `eq` weight, and the packs' weights come last.

use primitives::field::lanes::transpose_bits;
use primitives::field::{Acc8, F128, F128x8, clmul8_low, mul};
use primitives::hash::positions::row_positions;
use primitives::multilinear::eq_table;
use verifier::keccak::{BITS, PRODUCT_BITS};

use crate::kernels::{FieldMap, ONES, PACKS, PACKS_LOG, Run, embed_run, field_map, map_sums, xor};
use crate::layer::Layer;
use crate::protocol::Claim;

/// Bytes of a product of two embeddings.
const PRODUCT_BYTES: usize = PRODUCT_BITS.div_ceil(8);
/// A run's product bits: word `PRODUCT_BYTES q + m` holds byte `m` of pack `q`'s products, transposed.
const RUN_WORDS: usize = PACKS * PRODUCT_BYTES;
/// A block's sums: per pack, one per bit of a product.
const SUMS: usize = 8 * RUN_WORDS;

/// `U`, and the 32 packs' parts of it before their weights `eq(point[..5], pack)`, which the skip's binary points
/// read, pack `q`'s from `PRODUCT_BITS q`. `tasks` are the tasks' weights in `eq(point[5..])`.
pub(crate) fn polynomial(layer: &Layer, claim: &Claim, tasks: &[F128]) -> ([F128; PRODUCT_BITS], Vec<F128>) {
    let maps: Vec<FieldMap> = claim.weights.as_chunks::<8>().0.iter().map(field_map).collect();
    // Each worker's scratch rides beside its sums, allocated at its first task.
    let (_, sums) = parallel::fold_reduce(
        layer.n_tasks(),
        || (Vec::new(), vec![Acc8::ZERO; SUMS / 8]),
        |(bits, sums), task| {
            if bits.is_empty() {
                *bits = vec![0; BITS / 8 * RUN_WORDS];
            }
            let mut block = [F128::ZERO; SUMS];
            block_sums(&maps, layer.task(task), bits.as_chunks_mut().0, &mut block);
            let weight = F128x8::splat(tasks[task]);
            for (sum, block) in sums.iter_mut().zip(block.as_chunks::<8>().0) {
                *sum += F128x8::from_array(block).mul_unreduced(weight);
            }
        },
        |(kept, mut a), (_, b)| {
            for (a, b) in a.iter_mut().zip(b) {
                *a += b;
            }
            (kept, a)
        },
    );
    let mut reduced = [F128::ZERO; SUMS];
    for (out, sum) in reduced.as_chunks_mut::<8>().0.iter_mut().zip(sums) {
        *out = sum.reduce().to_array();
    }
    let packs = eq_table(&claim.point[..PACKS_LOG]);
    let mut per_pack = vec![F128::ZERO; PACKS * PRODUCT_BITS];
    let mut total = [F128::ZERO; PRODUCT_BITS];
    // Pack `q`'s coefficients, its last byte's spare bit past them.
    for (q, (out, sums)) in per_pack
        .as_chunks_mut::<PRODUCT_BITS>()
        .0
        .iter_mut()
        .zip(reduced.as_chunks::<{ 8 * PRODUCT_BYTES }>().0)
        .enumerate()
    {
        out.copy_from_slice(&sums[..PRODUCT_BITS]);
        for (total, &sum) in total.iter_mut().zip(out.iter()) {
            *total += mul(packs[q], sum);
        }
    }
    (total, per_pack)
}

/// A block's sums: entry `8 PRODUCT_BYTES q + c` of `out` is the sum over positions `j` of `maps`' weights times
/// coefficient `c` of `chi(q, j)`. `bits` holds each run's product bits.
fn block_sums(maps: &[FieldMap], block: &[u64], bits: &mut [[u64; RUN_WORDS]], out: &mut [F128; SUMS]) {
    let mut e = [[[0; 8]; PACKS]; 5];
    for r in 0..5 {
        for z in (0..64).step_by(8) {
            // A row of five runs, which `chi` mixes.
            let js = row_positions(r, z);
            for (e, &j) in e.iter_mut().zip(&js) {
                embed_run(block, j, e);
            }
            for x in 0..5 {
                let bits = bits[js[x] / 8].as_chunks_mut::<PRODUCT_BYTES>().0;
                for (q, bits) in bits.iter_mut().enumerate() {
                    let product = chi(e[x][q], e[(x + 1) % 5][q], e[(x + 2) % 5][q]);
                    *bits = transpose_bits(product)[..PRODUCT_BYTES]
                        .try_into()
                        .expect("a product's bytes");
                }
            }
        }
    }
    for (v, out) in out.as_chunks_mut::<64>().0.iter_mut().enumerate() {
        map_sums(maps, &bits.as_flattened()[8 * v..], RUN_WORDS, out);
    }
}

/// The unprojected `chi` of eight packs' embeddings: `ones * (a + c) + b * c`.
fn chi(a: Run, b: Run, c: Run) -> Run {
    xor(clmul8_low(ONES, xor(a, c)), clmul8_low(b, c))
}
