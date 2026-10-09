use super::{BLOCK, F192};

/// The fold of one row through the byte tables: one lookup and one XOR per byte.
#[inline(always)]
fn fold_row_lookup<const CHUNKS: usize>(tables: &[[F192; 256]], row: &[u8; CHUNKS]) -> F192 {
    let tables: &[[F192; 256]; CHUNKS] = tables.try_into().expect("one table per byte");
    row.iter()
        .zip(tables)
        .fold(F192::ZERO, |acc, (&v, sums)| acc + sums[usize::from(v)])
}

/// One 256-entry subset-sum table per byte of a row: entry `[j][v]` sums the weights of the set bits of `v` at byte `j`.
fn lookup_tables(weights: &[F192]) -> Vec<[F192; 256]> {
    weights
        .as_chunks::<8>()
        .0
        .iter()
        .map(|w| {
            let mut sums = [F192::ZERO; 256];
            // Each entry adds its lowest set bit's weight to an entry already built.
            for v in 1..256usize {
                let low = v.isolate_lowest_one();
                sums[v] = sums[v ^ low] + w[low.trailing_zeros() as usize];
            }
            sums
        })
        .collect()
}

/// The byte tables.
#[derive(Clone, Debug)]
pub(super) struct Imp {
    /// One subset-sum table per byte of a row.
    tables: Vec<[F192; 256]>,
}

impl Imp {
    pub(super) fn new(weights: &[F192]) -> Self {
        Self {
            tables: lookup_tables(weights),
        }
    }

    pub(super) fn new_f192(weights: &[F192]) -> Self {
        Self::new(weights)
    }

    #[inline]
    pub(super) fn fold_block<const CHUNKS: usize>(&self, rows: &[[u8; CHUNKS]], out: &mut [F192; BLOCK]) {
        for (o, row) in out.iter_mut().zip(rows) {
            *o = fold_row_lookup(&self.tables, row);
        }
    }

    pub(super) const fn slice(xs: &[F192; BLOCK]) -> Sliced {
        *xs
    }

    #[inline]
    pub(super) fn apply_sliced_add(&self, xs: &Sliced, out: &mut [F192]) {
        self.apply_add_f192(xs, out);
    }

    #[inline]
    pub(super) fn apply_add_f192(&self, xs: &[F192; BLOCK], out: &mut [F192]) {
        for (o, x) in out.iter_mut().zip(xs) {
            let mut row = [0u8; 24];
            row[..8].copy_from_slice(&x.c0.to_le_bytes());
            row[8..16].copy_from_slice(&x.c1.to_le_bytes());
            row[16..].copy_from_slice(&x.c2.to_le_bytes());
            *o += fold_row_lookup(&self.tables, &row);
        }
    }
}

/// A block of values, as they are.
pub(super) type Sliced = [F192; BLOCK];
