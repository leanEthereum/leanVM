//! Weighted sums of packed bit rows: the fold that turns witness bits into values of `E = GF(2^192)`.
//!
//! A row is `CHUNKS` bytes, so `8 * CHUNKS` bits, and every bit carries a fixed weight `w_s` in `E`:
//!
//! ```text
//!     fold(row) = sum_{s : bit s of row is set} w_s
//! ```
//!
//! The fold is `F_2`-linear in the row's bits, so it splits into one 8-bit piece per byte.
//!
//! - Portable: a 256-entry subset-sum table per byte, one lookup per byte.
//! - ARM with SHA3: the same byte tables, stored as three 64-bit limbs, with pairs of lookups summed by NEON EOR3.
//! - AVX-512 with GFNI: an 8x8 bit matrix per (input byte, output byte), applied to 64 rows by one instruction.
//! - AVX2: the same byte-sliced shape 32 rows wide, each map one affine instruction with GFNI, else two nibble lookups.

use crate::field::F192;

use crate::multilinear::eq_table;

#[cfg(all(
    target_arch = "x86_64",
    target_feature = "gfni",
    target_feature = "avx512bw",
    target_feature = "avx512vbmi"
))]
use core::arch::x86_64::__m512i;

#[cfg(all(target_arch = "aarch64", target_feature = "sha3"))]
use arm::{self as imp, Imp};

#[cfg(not(any(
    all(target_arch = "x86_64", target_feature = "avx2"),
    all(target_arch = "aarch64", target_feature = "sha3")
)))]
use portable::{self as imp, Imp};

#[cfg(all(
    target_arch = "x86_64",
    target_feature = "gfni",
    target_feature = "avx512bw",
    target_feature = "avx512vbmi"
))]
use gfni::{self as imp, Imp};

#[cfg(all(
    target_arch = "x86_64",
    target_feature = "avx2",
    not(all(target_feature = "gfni", target_feature = "avx512bw", target_feature = "avx512vbmi"))
))]
use avx2::{self as imp, Imp};

/// Rows folded, or values mapped, per call.
pub const BLOCK: usize = 64;

/// The weights of every bit of a row, prepared for folding.
#[derive(Clone, Debug)]
pub struct BitFold {
    /// Bytes per row.
    n_chunks: usize,
    /// The target's fold kernel data.
    imp: Imp,
}

impl BitFold {
    /// Prepares `weights`, one per bit of a row, bit `s` being bit `s % 8` of byte `s / 8`.
    ///
    /// # Panics
    ///
    /// Panics unless a row is 8, 16, 32, 64 or 128 bytes, that is 64 to 1024 weights.
    pub fn new(weights: &[F192]) -> Self {
        let n_chunks = weights.len() / 8;
        assert!(
            weights.len() == 8 * n_chunks && n_chunks.is_power_of_two() && (8..=128).contains(&n_chunks),
            "a row is 8 to 128 bytes, a power of two"
        );
        Self {
            n_chunks,
            imp: Imp::new(weights),
        }
    }

    /// The fold of a position at multilinear level `t`, once the `t` challenges `rho` are bound.
    ///
    /// Position `q` covers the `2^t` consecutive rows `q * 2^t + u`, so its weights are a tensor:
    ///
    /// ```text
    ///     w[n u + s] = eq(rho, u) * lagrange[s]        u in 0..2^t, s in 0..n, n = lagrange.len()
    /// ```
    ///
    /// # Panics
    ///
    /// Panics unless the `2^t * n` weights make a row of 8 to 128 bytes, a power of two.
    pub fn at_level(lagrange: &[F192], rho: &[F192]) -> Self {
        let weights: Vec<F192> = eq_table(rho)
            .iter()
            .flat_map(|&e| lagrange.iter().map(move |&l| e * l))
            .collect();
        Self::new(&weights)
    }

    /// Bytes per row.
    pub const fn n_chunks(&self) -> usize {
        self.n_chunks
    }

    /// Folds up to 64 consecutive rows into `out[..rows.len()]`.
    ///
    /// # Panics
    ///
    /// Panics if there are more than 64 rows.
    #[inline]
    pub fn fold_block<const CHUNKS: usize>(&self, rows: &[[u8; CHUNKS]], out: &mut [F192; BLOCK]) {
        debug_assert_eq!(CHUNKS, self.n_chunks);
        assert!(rows.len() <= BLOCK);
        self.imp.fold_block(rows, out);
    }

    /// Folds 64 consecutive rows into coefficient planes, grouped by quad.
    ///
    /// Plane `k`, register `u + 2v + 4g`, qword `l` is coefficient `k` of row `4 (8g + l) + u + 2v`.
    #[cfg(all(
        target_arch = "x86_64",
        target_feature = "gfni",
        target_feature = "avx512bw",
        target_feature = "avx512vbmi"
    ))]
    ///
    /// # Safety
    ///
    /// Requires AVX-512F, BW and VBMI and GFNI, which the target enables wherever this is compiled.
    #[inline]
    #[target_feature(enable = "avx512f", enable = "avx512bw", enable = "avx512vbmi", enable = "gfni")]
    pub fn fold_quads<const CHUNKS: usize>(&self, rows: &[[u8; CHUNKS]; BLOCK]) -> [[__m512i; 8]; 3] {
        debug_assert_eq!(CHUNKS, self.n_chunks);
        self.imp.fold_quads(rows)
    }
}

/// An `F_2`-linear map `E -> E`, given by the image of each of the 192 coordinate bits.
///
/// It is the row fold on a value's 24 bytes taken as one row.
/// Input and output are both 24-byte values, so the byte-sliced backends' input transpose is their output's inverse.
#[derive(Clone, Debug)]
pub struct F192Map {
    imp: Imp,
}

impl F192Map {
    /// The map sending coordinate bit `b` (bit `b % 64` of coefficient `b / 64`) to `weights[b]`.
    ///
    /// # Panics
    ///
    /// Panics unless there are 192 weights.
    pub fn new(weights: &[F192]) -> Self {
        assert_eq!(weights.len(), 192, "one weight per coordinate bit");
        Self {
            imp: Imp::new_f192(weights),
        }
    }

    /// Adds the images of the first `out.len()` values of `xs` into `out`.
    ///
    /// # Panics
    ///
    /// Panics if `out` is longer than 64.
    #[inline]
    pub fn apply_add(&self, xs: &[F192; BLOCK], out: &mut [F192]) {
        assert!(out.len() <= BLOCK);
        self.imp.apply_add_f192(xs, out);
    }

    /// The map `x -> self(x * c)`, itself `F_2`-linear.
    pub fn after_mul(&self, c: F192) -> Self {
        self.sum_after_mul(&[(F192::ONE, c)])
    }

    /// The map `x -> sum_j post_j * self(x * pre_j)` over the pairs `(post_j, pre_j)`, itself `F_2`-linear.
    pub fn sum_after_mul(&self, terms: &[(F192, F192)]) -> Self {
        let mut weights = [F192::ZERO; 192];
        for &(post, pre) in terms {
            for (chunk, w) in weights.chunks_mut(BLOCK).enumerate() {
                // The image of each coordinate bit `b`: `self(b * pre)`, then scaled by `post`.
                let xs: [F192; BLOCK] = std::array::from_fn(|i| coordinate(BLOCK * chunk + i) * pre);
                let mut images = [F192::ZERO; BLOCK];
                self.apply_add(&xs, &mut images);
                for (w, image) in w.iter_mut().zip(images) {
                    *w += post * image;
                }
            }
        }
        Self::new(&weights)
    }

    /// Adds the images of the first `out.len()` values of the block `xs` into `out`.
    ///
    /// # Panics
    ///
    /// Panics if `out` is longer than 64.
    #[inline]
    pub fn apply_sliced_add(&self, xs: &Sliced, out: &mut [F192]) {
        assert!(out.len() <= BLOCK);
        self.imp.apply_sliced_add(&xs.0, out);
    }
}

/// The element whose only set coordinate bit is `bit`: bit `bit % 64` of coefficient `bit / 64`.
const fn coordinate(bit: usize) -> F192 {
    let mut words = [0u64; 3];
    words[bit / 64] = 1 << (bit % 64);
    F192::new(words[0], words[1], words[2])
}

/// A block of values in the layout the map reads, so that a block mapped many times is transposed once.
#[derive(Clone, Debug)]
pub struct Sliced(imp::Sliced);

impl Sliced {
    /// The block `xs`, transposed into the map's layout on the backends that have one.
    #[cfg_attr(
        not(all(target_arch = "x86_64", target_feature = "avx2")),
        expect(clippy::missing_const_for_fn, reason = "The SIMD layouts transpose the block.")
    )]
    pub fn new(xs: &[F192; BLOCK]) -> Self {
        Self(Imp::slice(xs))
    }
}

#[cfg(all(target_arch = "aarch64", target_feature = "sha3"))]
mod arm;

#[cfg(not(any(
    all(target_arch = "x86_64", target_feature = "avx2"),
    all(target_arch = "aarch64", target_feature = "sha3")
)))]
mod portable;

#[cfg(all(
    target_arch = "x86_64",
    target_feature = "gfni",
    target_feature = "avx512bw",
    target_feature = "avx512vbmi"
))]
pub mod gfni;

#[cfg(all(target_arch = "x86_64", target_feature = "avx2"))]
#[cfg_attr(
    all(target_feature = "gfni", target_feature = "avx512bw", target_feature = "avx512vbmi"),
    allow(dead_code)
)]
pub mod avx2;

#[cfg(test)]
mod tests {
    use super::*;
    use crate::test_util::Rng;

    #[test]
    fn fold_block_matches_definition() {
        fn check<const CHUNKS: usize>(rng: &mut Rng) {
            // Random weights, one per bit of a CHUNKS-byte row.
            let weights: Vec<F192> = (0..8 * CHUNKS).map(|_| rng.ext()).collect();
            let fold = BitFold::new(&weights);

            // Full blocks of random rows, then a short block that exercises the zero padding.
            for len in [BLOCK, BLOCK, 5] {
                let rows: Vec<[u8; CHUNKS]> = (0..len)
                    .map(|_| std::array::from_fn(|_| rng.next_u64() as u8))
                    .collect();
                let mut out = [F192::ZERO; BLOCK];
                fold.fold_block(&rows, &mut out);
                for (p, row) in rows.iter().enumerate() {
                    // Each set bit contributes its own field weight, independently of the backend's layout.
                    let expected = weights
                        .iter()
                        .enumerate()
                        .filter(|(bit, _)| row[bit / 8] >> (bit % 8) & 1 == 1)
                        .fold(F192::ZERO, |acc, (_, &weight)| acc + weight);
                    assert_eq!(out[p], expected, "CHUNKS={CHUNKS}, len={len}, row {p}");
                }
            }
        }
        let mut rng = Rng::new(0xB17_F01D);
        check::<8>(&mut rng);
        check::<16>(&mut rng);
        check::<32>(&mut rng);
        check::<64>(&mut rng);
        check::<128>(&mut rng);
    }

    #[test]
    fn f192_map_matches_definition() {
        let mut rng = Rng::new(0x0F19_23A9);
        let weights: Vec<F192> = (0..192).map(|_| rng.ext()).collect();
        let map = F192Map::new(&weights);
        for len in [BLOCK, 7] {
            let xs: [F192; BLOCK] = std::array::from_fn(|_| rng.ext());
            let before: Vec<F192> = (0..len).map(|_| rng.ext()).collect();
            let mut out = before.clone();
            map.apply_add(&xs, &mut out);
            for p in 0..len {
                let words = [xs[p].c0, xs[p].c1, xs[p].c2];
                let image = (0..192)
                    .filter(|&b| words[b / 64] >> (b % 64) & 1 == 1)
                    .fold(F192::ZERO, |acc, b| acc + weights[b]);
                assert_eq!(out[p], before[p] + image, "len={len}, value {p}");
            }
        }
    }

    #[test]
    fn composed_map_is_the_map_after_the_product() {
        let mut rng = Rng::new(0xC0_4405E);
        let weights: Vec<F192> = (0..192).map(|_| rng.ext()).collect();
        let map = F192Map::new(&weights);
        let c = rng.ext();
        let composed = map.after_mul(c);
        let xs: [F192; BLOCK] = std::array::from_fn(|_| rng.ext());
        let mut expected = [F192::ZERO; BLOCK];
        map.apply_add(&xs.map(|x| x * c), &mut expected);
        let mut got = [F192::ZERO; BLOCK];
        composed.apply_sliced_add(&Sliced::new(&xs), &mut got);
        assert_eq!(got, expected);
    }

    #[cfg(all(target_arch = "x86_64", target_feature = "avx2"))]
    #[test]
    fn avx2_products_match_definition() {
        // Invariant: every AVX2 product this target compiles matches the definition, not only the dispatched one.
        fn check<P: avx2::Product, const CHUNKS: usize>(rng: &mut Rng) {
            let weights: Vec<F192> = (0..8 * CHUNKS).map(|_| rng.ext()).collect();
            let fold = avx2::Fold::<P>::new(&weights);
            for len in [BLOCK, 5] {
                let rows: Vec<[u8; CHUNKS]> = (0..len)
                    .map(|_| std::array::from_fn(|_| rng.next_u64() as u8))
                    .collect();
                let mut out = [F192::ZERO; BLOCK];
                fold.fold_block(&rows, &mut out);
                for (p, row) in rows.iter().enumerate() {
                    let expected = weights
                        .iter()
                        .enumerate()
                        .filter(|(bit, _)| row[bit / 8] >> (bit % 8) & 1 == 1)
                        .fold(F192::ZERO, |acc, (_, &weight)| acc + weight);
                    assert_eq!(out[p], expected, "CHUNKS={CHUNKS}, len={len}, row {p}");
                }
            }
        }
        fn check_map<P: avx2::Product>(rng: &mut Rng) {
            let weights: Vec<F192> = (0..192).map(|_| rng.ext()).collect();
            let map = avx2::Fold::<P>::new_f192(&weights);
            let xs: [F192; BLOCK] = std::array::from_fn(|_| rng.ext());
            let mut out = [F192::ZERO; 7];
            map.apply_add_f192(&xs, &mut out);
            for (p, &o) in out.iter().enumerate() {
                let words = [xs[p].c0, xs[p].c1, xs[p].c2];
                let image = (0..192)
                    .filter(|&b| words[b / 64] >> (b % 64) & 1 == 1)
                    .fold(F192::ZERO, |acc, b| acc + weights[b]);
                assert_eq!(o, image, "value {p}");
            }
        }
        fn check_all<P: avx2::Product>(rng: &mut Rng) {
            check::<P, 8>(rng);
            check::<P, 16>(rng);
            check::<P, 32>(rng);
            check::<P, 64>(rng);
            check::<P, 128>(rng);
            check_map::<P>(rng);
        }
        let mut rng = Rng::new(0xA7_2B17);
        check_all::<avx2::Shuffle>(&mut rng);
        #[cfg(target_feature = "gfni")]
        check_all::<avx2::Gfni>(&mut rng);
    }
}
