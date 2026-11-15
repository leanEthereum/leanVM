//! Step 3's rounds after the skip, over the half, the block and the segment, on a table of field elements.
//!
//! At the skip's challenges, a group's packs fold to one field element per position: at `s` a pack is the sum of
//! the instance weights of its set bits, so the group's value is a linear map of its 32 bytes at that position
//! ([`PackFold`]). The table holds a row of positions per group, block and segment, and each round folds it in
//! half while summing the next round's values over the rows it writes ([`Summand::pair`]).

use fiat_shamir::transcript::ProverState;
use primitives::field::lanes::transpose_bytes;
use primitives::field::{Acc8, F128, F128Unreduced, F128x8};
use primitives::multilinear::eq_table;
use verifier::PACK;

use crate::keccak::{BITS, along};
use crate::kernels::{FieldMap, field_map, map_sums};
use crate::layer::{Layer, Sumcheck};
use crate::protocol::Claim;
use crate::skip::SKIP;
use crate::witness::{BLOCK_WORDS, Shape};

/// The table and the half it folds into, allocated once for every layer: row `half + 2 (g + n_blocks segment)` is
/// group `half` of block `g` of segment `segment`.
pub(crate) struct Tables([Vec<F128>; 2]);

impl Tables {
    pub fn new(shape: Shape) -> Self {
        let len = (2 * BITS * shape.n_blocks()) << shape.seg_log();
        Self([len, len / 2].map(|len| parallel::filled(len, F128::ZERO)))
    }
}

/// What the rounds over the half, block and segment sum over positions: `weights[j] * (kappa T[j] + (kappa +
/// T[j + 1]) T[j + 2])`. Moving each `kappa T[j]` two columns along, the sum is that of `B[j] * T[j + 2]` with
/// `B[j] = weights[j] (kappa + T[j + 1]) + constant[j]` and `constant[j] = kappa * weights[j + 2]`.
pub(crate) struct Summand {
    weights: Vec<F128>,
    constant: Vec<F128>,
    kappa: F128,
}

impl Summand {
    pub fn new(claim: &Claim, kappa: F128) -> Self {
        Self {
            weights: claim.weights.clone(),
            constant: (0..BITS).map(|j| kappa * claim.weights[along(j, 2)]).collect(),
            kappa,
        }
    }

    /// The round's values at `0` and infinity over one pair of rows, the variable being bound `0` on `low` and `1`
    /// on `high`.
    fn pair(&self, low: &[F128], high: &[F128]) -> (F128, F128) {
        let kappa = F128x8::splat(self.kappa);
        let (mut zero, mut infinity) = (Acc8::ZERO, Acc8::ZERO);
        for lane in 0..BITS / 64 {
            let (a, b, c) = (64 * lane, along(64 * lane, 1), along(64 * lane, 2));
            for z in (0..64).step_by(8) {
                let at = |v: &[F128], j: usize| F128x8::load(&v[j + z..][..8]);
                let (w, lb, lc) = (at(&self.weights, a), at(low, b), at(low, c));
                zero += (w * (kappa + lb) + at(&self.constant, a)).mul_unreduced(lc);
                infinity += (w * (lb + at(high, b))).mul_unreduced(lc + at(high, c));
            }
        }
        (zero.sum(), infinity.sum())
    }
}

/// A group's packs at one position, folded at the skip's challenges, as a [`FieldMap`] per byte of the group.
struct PackFold([FieldMap; 32]);

impl PackFold {
    /// Byte `t` of a group's position is the low or high byte of pack `t / 2`, which weighs `eq(challenges, t / 2)`
    /// times the instance weights of its bits.
    fn new(mu: &[F128; PACK], challenges: &[F128]) -> Self {
        let eq = eq_table(challenges);
        Self(std::array::from_fn(|t| {
            field_map(&std::array::from_fn(|c| eq[t / 2] * mu[8 * (t % 2) + c]))
        }))
    }

    /// Both groups of a block, folded: entry `BITS * half + j` of `out` is group `half` at position `j`.
    fn rows(&self, block: &[u64], out: &mut [F128]) {
        for j in (0..BITS).step_by(64) {
            // Byte `t` of a position's 64 bytes, for each of the 64 positions from `j`, in `bytes[t]`.
            let mut bytes = [[0u64; 8]; 64];
            let positions = block[j * BLOCK_WORDS..][..64 * BLOCK_WORDS]
                .as_chunks::<BLOCK_WORDS>()
                .0;
            for (k, positions) in positions.as_chunks::<16>().0.iter().enumerate() {
                for (bytes, t) in bytes.iter_mut().zip(transpose_bytes(positions)) {
                    bytes[2 * k..][..2].copy_from_slice(&[t as u64, (t >> 64) as u64]);
                }
            }
            for half in 0..2 {
                let values = map_sums(&self.0, |t| bytes[32 * half + t]);
                for (out, v) in out[BITS * half + j..][..64].iter_mut().zip(values) {
                    *out = F128::from(v);
                }
            }
        }
    }
}

/// Fill `tables` at the skip's challenges and return the first round's values, each pair of rows `p` weighted by
/// `eq(point[SKIP + 1..], p)`. The rows of segments that do not exist are zero, and the padding blocks' rows are
/// the padding block's, folded once.
pub(crate) fn fill(
    layer: &Layer,
    claim: &Claim,
    summand: &Summand,
    mu: &[F128; PACK],
    challenges: &[F128],
    tables: &mut Tables,
) -> (F128, F128) {
    let fold = PackFold::new(mu, challenges);
    let eq = eq_table(&claim.point[SKIP + 1..]);
    let (n_blocks, written) = (layer.n_blocks(), layer.written());
    let rows = |block: &[u64], out: &mut [F128]| {
        fold.rows(block, out);
        summand.pair(&out[..BITS], &out[BITS..])
    };
    let padding = |segment: usize| {
        let mut out = vec![F128::ZERO; 2 * BITS];
        let values = rows(layer.state(segment, written), &mut out);
        (out, values)
    };
    let padding: Vec<(Vec<F128>, (F128, F128))> = match written < n_blocks {
        true => (0..layer.segments()).map(padding).collect(),
        false => Vec::new(),
    };
    let values = parallel::map_reduce_chunks_mut(
        [&mut tables.0[0][..]],
        [2 * BITS],
        || (F128Unreduced::ZERO, F128Unreduced::ZERO),
        |acc, p, [out]| {
            let (segment, g) = (p / n_blocks, p % n_blocks);
            if segment >= layer.segments() {
                out.fill(F128::ZERO);
                return;
            }
            let (zero, infinity) = if g < written {
                rows(layer.state(segment, g), out)
            } else {
                out.copy_from_slice(&padding[segment].0);
                padding[segment].1
            };
            acc.0 ^= zero.mul_unreduced(eq[p]);
            acc.1 ^= infinity.mul_unreduced(eq[p]);
        },
        |a, b| (a.0 ^ b.0, a.1 ^ b.1),
    );
    (values.0.reduce(), values.1.reduce())
}

/// Send the rounds after the skip, the first one's values being `values`, and return the table's last row: `T`, the
/// state at the bound pack and segment. Each round folds one table into the other.
pub(crate) fn prove_rounds(
    ps: &mut ProverState,
    claim: &Claim,
    summand: &Summand,
    mut values: (F128, F128),
    tables: &mut Tables,
    sumcheck: &mut Sumcheck,
) -> Vec<F128> {
    let [table, half] = &mut tables.0;
    let (mut src, mut dst) = (&mut table[..], &mut half[..]);
    for i in SKIP..claim.point.len() {
        let challenge = sumcheck.round(ps, values.0, None, values.1, claim.point[i]);
        let eq = eq_table(claim.point.get(i + 2..).unwrap_or(&[]));
        let len = src.len() / 2;
        values = fold_rows(summand, src, &mut dst[..len], challenge, &eq);
        (src, dst) = (&mut dst[..len], src);
    }
    src.to_vec()
}

/// Tables of at most this many rows fold on the calling thread: waking the pool would cost more than the work.
const SERIAL_ROWS: usize = 64;

/// Bind the leading variable of `table`, rows of positions, at `challenge` into `out`, and sum the next round's
/// values over the rows written while they are at hand, each pair of rows `p` weighted by `eq[p]`: zero once a
/// single row is left.
fn fold_rows(summand: &Summand, table: &[F128], out: &mut [F128], challenge: F128, eq: &[F128]) -> (F128, F128) {
    let challenge = F128x8::splat(challenge);
    // Pair `p` of the rows written, from four rows of `table`.
    let pair = |acc: &mut (F128Unreduced, F128Unreduced), p: usize, rows: &mut [F128]| {
        let src = &table[4 * BITS * p..][..2 * rows.len()];
        for (row, src) in rows
            .as_chunks_mut::<BITS>()
            .0
            .iter_mut()
            .zip(src.as_chunks::<{ 2 * BITS }>().0)
        {
            let (low, high) = src.split_at(BITS);
            for (i, out) in row.as_chunks_mut::<8>().0.iter_mut().enumerate() {
                let (l, h) = (F128x8::load(&low[8 * i..][..8]), F128x8::load(&high[8 * i..][..8]));
                (l + challenge * (l + h)).store(out);
            }
        }
        if rows.len() == 2 * BITS {
            let (zero, infinity) = summand.pair(&rows[..BITS], &rows[BITS..]);
            acc.0 ^= zero.mul_unreduced(eq[p]);
            acc.1 ^= infinity.mul_unreduced(eq[p]);
        }
    };
    let zero = (F128Unreduced::ZERO, F128Unreduced::ZERO);
    let values = if table.len() <= SERIAL_ROWS * BITS {
        let mut values = zero;
        for (p, rows) in out.chunks_mut(2 * BITS).enumerate() {
            pair(&mut values, p, rows);
        }
        values
    } else {
        parallel::map_reduce_chunks_mut(
            [out],
            [2 * BITS],
            || zero,
            |acc, p, [rows]| pair(acc, p, rows),
            |a, b| (a.0 ^ b.0, a.1 ^ b.1),
        )
    };
    (values.0.reduce(), values.1.reduce())
}
