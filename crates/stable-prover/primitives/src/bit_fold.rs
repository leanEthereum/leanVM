//! Weighted sums of packed bit rows, the fold that turns witness bits into F128 values.
//!
//! A row is `8 * CHUNKS` bits and every bit carries a fixed F128 weight:
//!
//! ```text
//!     fold(row) = sum_{s : bit s of row is set} w_s
//! ```
//!
//! The map is GF(2)-linear in the row's bits, so it splits into one 8-bit piece per byte: a 256-entry
//! subset-sum table per byte, one lookup per byte.

use crate::field::F128;

/// Rows per [`BitFold::fold_columns`].
pub const BLOCK: usize = 64;

/// The weights of every bit of a row, prepared for folding.
#[derive(Clone, Debug)]
pub struct BitFold {
    /// One subset-sum table per byte of a row: entry `[j][v]` sums the weights of the set bits of `v` at byte `j`, as
    /// the `u128` of its limbs, low first: one load per lookup, which LLVM keeps scalar where it would turn a block's
    /// lookups of two limbs into gathers that lose to them on AVX-512.
    tables: Vec<[u128; 256]>,
}

impl BitFold {
    /// Prepare `weights`, one per bit of a row.
    ///
    /// # Panics
    ///
    /// Panics unless a row is a whole number of bytes.
    pub fn new(weights: &[F128]) -> Self {
        let (bytes, rest) = weights.as_chunks::<8>();
        assert!(rest.is_empty(), "a row is a whole number of bytes");
        let tables = bytes
            .iter()
            .map(|w| {
                let mut sums = [0u128; 256];
                // Each entry adds its lowest set bit's weight to an entry already built.
                for v in 1..256usize {
                    let low = v.isolate_lowest_one();
                    sums[v] = sums[v ^ low] ^ u128::from(w[low.trailing_zeros() as usize]);
                }
                sums
            })
            .collect();
        Self { tables }
    }

    /// The fold of one row: one lookup per byte.
    #[inline]
    pub fn fold_row(&self, row: &[u8]) -> F128 {
        debug_assert_eq!(row.len(), self.tables.len(), "a row's width");
        let sum = row
            .iter()
            .zip(&self.tables)
            .fold(0, |sum, (&v, sums)| sum ^ sums[usize::from(v)]);
        F128::from(sum)
    }

    /// Fold 64 rows given as byte columns: `cols[j][p]` is byte `j` of row `p`.
    #[inline]
    pub fn fold_columns<const CHUNKS: usize>(&self, cols: &[[u8; BLOCK]; CHUNKS], out: &mut [F128; BLOCK]) {
        assert_eq!(CHUNKS, self.tables.len());
        for (p, o) in out.iter_mut().enumerate() {
            let sum = cols
                .iter()
                .zip(&self.tables)
                .fold(0, |sum, (col, sums)| sum ^ sums[usize::from(col[p])]);
            *o = F128::from(sum);
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::test_rng::Rng;

    /// The definition: the sum of the weights of the set bits, bit `s` being bit `s % 8` of byte `s / 8`.
    fn direct(weights: &[F128], row: &[u8]) -> F128 {
        (0..weights.len())
            .filter(|s| (row[s / 8] >> (s % 8)) & 1 == 1)
            .map(|s| weights[s])
            .sum()
    }

    /// Every row width, the rows given whole and as byte columns.
    #[test]
    fn folds_match_definition() {
        fn check<const CHUNKS: usize>(rng: &mut Rng) {
            let weights: Vec<F128> = (0..8 * CHUNKS).map(|_| rng.ext()).collect();
            let fold = BitFold::new(&weights);
            let rows: Vec<[u8; CHUNKS]> = (0..BLOCK)
                .map(|_| std::array::from_fn(|_| rng.next_u64() as u8))
                .collect();
            let cols: [[u8; BLOCK]; CHUNKS] = std::array::from_fn(|j| std::array::from_fn(|p| rows[p][j]));
            let mut out = [F128::ZERO; BLOCK];
            fold.fold_columns(&cols, &mut out);
            for (p, row) in rows.iter().enumerate() {
                assert_eq!(out[p], direct(&weights, row), "CHUNKS={CHUNKS}, column row {p}");
                assert_eq!(fold.fold_row(row), out[p], "CHUNKS={CHUNKS}, row {p}");
            }
        }
        let mut rng = Rng::new(0xB17_F01D);
        check::<8>(&mut rng);
        check::<16>(&mut rng);
        check::<32>(&mut rng);
        check::<64>(&mut rng);
        check::<128>(&mut rng);
    }
}
