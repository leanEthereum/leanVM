//! Step 3's rounds after the skip, over the half, the block and the segment, on a table of field elements.
//!
//! At the skip's challenges, a group's packs fold to one field element per position: at `s` a pack is the sum of
//! the instance weights of its set bits, so the group's value is a linear map of its 32 bytes at that position
//! ([`PackFold`]). The table holds a row of positions per group, block and segment, and each round folds it in
//! half while summing the next round's values over the rows it writes ([`Summand::pair`]).

use primitives::field::{Acc8, F128, F128Unreduced, F128x8, mul};
use primitives::transcript::ProverState;
use verifier::keccak::{BITS, PACK};

use crate::kernels::{FieldMap, along, field_map, map_sums};
use crate::layer::{Layer, Sumcheck};
use crate::protocol::Claim;
use crate::skip::SKIP;
use crate::witness::{BLOCK_WORDS, Shape};
use primitives::field::lanes::transpose_bytes;
use primitives::multilinear::eq_table;

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
/// `B[j] = weights[j] T[j + 1] + constant[j]` and `constant[j] = kappa (weights[j] + weights[j + 2])`.
pub(crate) struct Summand<'a> {
    weights: &'a [F128],
    constant: [F128; BITS],
}

impl<'a> Summand<'a> {
    pub fn new(claim: &'a Claim, kappa: F128) -> Self {
        let w = &claim.weights;
        Self {
            weights: w,
            constant: std::array::from_fn(|j| mul(kappa, w[j] + w[along(j, 2)])),
        }
    }

    /// The round's values at `0` and infinity over one pair of rows, the variable being bound `0` on `low` and `1`
    /// on `high`.
    fn pair(&self, low: &[F128], high: &[F128]) -> [F128; 2] {
        // At `0` the rows `low` with the constant, at infinity `low + high` without: one product site for both.
        let mut acc = [Acc8::ZERO; 2];
        for lane in 0..BITS / 64 {
            let (a, b, c) = (64 * lane, along(64 * lane, 1), along(64 * lane, 2));
            for z in (0..64).step_by(8) {
                let at = |v: &[F128], j: usize| F128x8::load(&v[j + z..][..8]);
                let (w, lb, lc) = (at(self.weights, a), at(low, b), at(low, c));
                let x = [lb, lb + at(high, b)];
                let y = [lc, lc + at(high, c)];
                let constant = [at(&self.constant, a), F128x8::splat(F128::ZERO)];
                for k in 0..2 {
                    acc[k] += (w * x[k] + constant[k]).mul_unreduced(y[k]);
                }
            }
        }
        acc.map(Acc8::sum)
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
            field_map(&std::array::from_fn(|c| mul(eq[t / 2], mu[8 * (t % 2) + c])))
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
                let out = (&mut out[BITS * half + j..][..64]).try_into().expect("64 positions");
                map_sums(&self.0, bytes[32 * half..].as_flattened(), 8, out);
            }
        }
    }
}

/// Fill `tables` at the skip's challenges and return the first round's values, each pair of rows `p` weighted by
/// `eq(point[SKIP + 1..], p)`. The rows of segments that do not exist are zero, and the padding blocks' rows are
/// the padding block's, folded once.
pub(crate) fn fill(
    layer: &Layer,
    summand: &Summand,
    mu: &[F128; PACK],
    challenges: &[F128],
    eq: &[F128],
    tables: &mut Tables,
) -> [F128; 2] {
    let fold = PackFold::new(mu, challenges);
    let (n_blocks, written) = (layer.n_blocks(), layer.written());
    let padding = |segment: usize| {
        let mut out = vec![F128::ZERO; 2 * BITS];
        fold.rows(layer.state(segment, written), &mut out);
        let values = summand.pair(&out[..BITS], &out[BITS..]);
        (out, values)
    };
    let padding = match written < n_blocks {
        true => (0..layer.segments()).map(padding).collect(),
        false => Vec::new(),
    };
    let source = Source::Witness {
        layer,
        fold: &fold,
        padding,
    };
    write_pairs(summand, &source, &mut tables.0[0], eq)
}

/// Send the rounds after the skip, the first one's values being `values`, and return the table's last row: `T`, the
/// state at the bound pack and segment. Each round folds one table into the other.
pub(crate) fn prove_rounds(
    ps: &mut ProverState,
    claim: &Claim,
    summand: &Summand,
    mut values: [F128; 2],
    tables: &mut Tables,
    sumcheck: &mut Sumcheck,
) -> Vec<F128> {
    let [table, half] = &mut tables.0;
    let (mut src, mut dst) = (&mut table[..], &mut half[..]);
    for i in SKIP..claim.point.len() {
        let challenge = sumcheck.round(ps, values[0], None, values[1], claim.point[i]);
        let eq = eq_table(claim.point.get(i + 2..).unwrap_or(&[]));
        let len = src.len() / 2;
        // Bind the leading variable into `dst`, summing the next round's values over the rows written, zero once a
        // single row is left.
        let source = Source::Table {
            table: src,
            challenge: F128x8::splat(challenge),
        };
        values = write_pairs(summand, &source, &mut dst[..len], &eq);
        (src, dst) = (&mut dst[..len], src);
    }
    src.to_vec()
}

/// What a table's rows are written from.
enum Source<'a> {
    /// The witness, folded at the skip's challenges, and per segment the padding block's rows and their values.
    Witness {
        layer: &'a Layer<'a>,
        fold: &'a PackFold,
        padding: Vec<(Vec<F128>, [F128; 2])>,
    },
    /// The previous table, its leading variable bound at `challenge`.
    Table { table: &'a [F128], challenge: F128x8 },
}

impl Source<'_> {
    /// Write pair of rows `p` into `rows`. Returns the pair's values where they are known without the rows.
    fn write(&self, p: usize, rows: &mut [F128]) -> Option<[F128; 2]> {
        match self {
            Self::Witness { layer, fold, padding } => {
                let (segment, g) = (p / layer.n_blocks(), p % layer.n_blocks());
                if segment >= layer.segments() {
                    rows.fill(F128::ZERO);
                    Some([F128::ZERO; 2])
                } else if g < layer.written() {
                    fold.rows(layer.state(segment, g), rows);
                    None
                } else {
                    rows.copy_from_slice(&padding[segment].0);
                    Some(padding[segment].1)
                }
            }
            Self::Table { table, challenge } => {
                // From four rows of `table`.
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
                        (l + *challenge * (l + h)).store(out);
                    }
                }
                // A single row is left: the rounds are over.
                (rows.len() < 2 * BITS).then_some([F128::ZERO; 2])
            }
        }
    }
}

/// Write each pair of rows `p` of `out` from `source`, and sum the next round's values over the pairs while they are
/// at hand, each weighted by `eq[p]`.
fn write_pairs(summand: &Summand, source: &Source, out: &mut [F128], eq: &[F128]) -> [F128; 2] {
    let values = parallel::map_reduce_chunks_mut(
        [out],
        [2 * BITS],
        || [F128Unreduced::ZERO; 2],
        |acc, p, [rows]| {
            let [zero, infinity] = pair_values(summand, source, p, rows, eq[p]);
            acc[0] ^= zero;
            acc[1] ^= infinity;
        },
        |a, b| [a[0] ^ b[0], a[1] ^ b[1]],
    );
    values.map(F128Unreduced::reduce)
}

/// Write pair `p` and return its values times `eq`. Out of line, apart from the pool's machinery.
#[inline(never)]
fn pair_values(summand: &Summand, source: &Source, p: usize, rows: &mut [F128], eq: F128) -> [F128Unreduced; 2] {
    let values = source
        .write(p, rows)
        .unwrap_or_else(|| summand.pair(&rows[..BITS], &rows[BITS..]));
    values.map(|v| v.mul_unreduced(eq))
}
