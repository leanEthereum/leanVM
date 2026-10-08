//! The convert: a window's medium bytes to F192, summed per lane under their medium and eq weights.
//!
//! ```text
//!     partial[lane] += eq_lo * sum_b gamma^b * phi_8(byte_b[lane])
//! ```
//!
//! The map from a lane's sixteen bytes to F192 is GF(2)-linear, so each target picks its fastest linear map:
//!
//! - AVX-512 with GFNI: one 8x8 bit matrix per (medium position, output byte), the eq weight baked in.
//! - AVX2: the same byte-sliced shape, 32 lanes wide, then one product per lane by the eq weight.
//! - Elsewhere: a 256-entry table per medium position, then one product per lane.

#[cfg(test)]
use primitives::field::{F8, F192, phi8_192};

#[cfg(test)]
use super::{ELL, gamma_powers};

#[cfg(all(
    target_arch = "x86_64",
    target_feature = "gfni",
    target_feature = "avx512bw",
    target_feature = "avx512vbmi"
))]
pub(super) use gfni::Convert;

#[cfg(all(
    target_arch = "x86_64",
    target_feature = "avx2",
    not(all(target_feature = "gfni", target_feature = "avx512bw", target_feature = "avx512vbmi"))
))]
pub(super) use avx2::Convert;

#[cfg(not(all(target_arch = "x86_64", target_feature = "avx2")))]
pub(super) use table::Convert;

/// The definition, lane by lane: `sum_b gamma^b * phi_8(rows[b][lane])`.
#[cfg(test)]
pub(super) fn reference(rows: &[[u8; 64]]) -> [F192; ELL] {
    std::array::from_fn(|lane| {
        (rows.iter().zip(gamma_powers())).fold(F192::ZERO, |acc, (row, &gamma)| acc + gamma * phi8_192(F8(row[lane])))
    })
}

/// 256-entry tables, one per medium position.
#[cfg(not(all(target_arch = "x86_64", target_feature = "avx2")))]
mod table {
    use std::sync::OnceLock;

    use primitives::field::{F192, PHI_8_TABLE_192};

    use super::super::{ELL, N_MEDIUM_VALUES, gamma_powers};

    /// `gamma^b * phi_8(v)` for every medium position `b` and byte `v`.
    ///
    /// Its shape, not a flat run, lets a byte index a row with no bounds check.
    /// The row stride then folds into the address.
    type Table = [[F192; 256]; N_MEDIUM_VALUES];

    /// The table, built once.
    fn table() -> &'static Table {
        static TABLE: OnceLock<Box<Table>> = OnceLock::new();
        TABLE.get_or_init(|| {
            // Row `b` is `phi_8` of every byte, scaled by `gamma^b`.
            let mut table: Box<Table> = Box::new([[F192::ZERO; 256]; N_MEDIUM_VALUES]);
            for (row, &g_b) in table.iter_mut().zip(gamma_powers()) {
                for (entry, &phi) in row.iter_mut().zip(PHI_8_TABLE_192.iter()) {
                    *entry = g_b * phi;
                }
            }
            table
        })
    }

    /// One worker's per-lane sums for `A B` and for `C`.
    pub(in super::super) struct Convert {
        ab: [F192; ELL],
        c: [F192; ELL],
    }

    impl Convert {
        pub(in super::super) const fn new() -> Self {
            Self {
                ab: [F192::ZERO; ELL],
                c: [F192::ZERO; ELL],
            }
        }

        /// Add one window's medium bytes, a 64-lane row per medium position, at weight `eq_lo`.
        #[inline(always)]
        pub(in super::super) fn accumulate(&mut self, ab: &[[u8; 64]], c: &[[u8; 64]], eq_lo: F192) {
            let table = table();
            #[cfg(target_arch = "aarch64")]
            {
                // A bounded group of four medium positions at a time keeps their table rows hot.
                let mut converted_ab = [F192::ZERO; ELL];
                let mut converted_c = [F192::ZERO; ELL];
                for ((rows, ab), c) in table.chunks(4).zip(ab.chunks(4)).zip(c.chunks(4)) {
                    for lane in 0..ELL {
                        let mut cf_ab = F192::ZERO;
                        let mut cf_c = F192::ZERO;
                        for ((row, ab), c) in rows.iter().zip(ab).zip(c) {
                            cf_ab += row[usize::from(ab[lane])];
                            cf_c += row[usize::from(c[lane])];
                        }
                        converted_ab[lane] += cf_ab;
                        converted_c[lane] += cf_c;
                    }
                }
                // The eq weight, once per lane after the whole window.
                for lane in 0..ELL {
                    self.ab[lane] += converted_ab[lane] * eq_lo;
                    self.c[lane] += converted_c[lane] * eq_lo;
                }
            }
            #[cfg(not(target_arch = "aarch64"))]
            for lane in 0..ELL {
                let mut cf_ab = F192::ZERO;
                let mut cf_c = F192::ZERO;
                for ((row, ab), c) in table.iter().zip(ab).zip(c) {
                    cf_ab += row[usize::from(ab[lane])];
                    cf_c += row[usize::from(c[lane])];
                }
                self.ab[lane] += cf_ab * eq_lo;
                self.c[lane] += cf_c * eq_lo;
            }
        }

        /// The `A B` and `C` sums.
        pub(in super::super) const fn values(&self) -> ([F192; ELL], [F192; ELL]) {
            (self.ab, self.c)
        }
    }
}

/// AVX2: byte-sliced against fixed maps, 32 lanes a register, then one product per lane by the eq weight.
#[cfg(all(target_arch = "x86_64", target_feature = "avx2"))]
#[cfg_attr(
    all(target_feature = "gfni", target_feature = "avx512bw", target_feature = "avx512vbmi"),
    allow(dead_code)
)]
pub(super) mod avx2 {
    use core::arch::x86_64::*;
    use std::sync::LazyLock;

    use primitives::bit_fold::avx2::{self, Best, HALF, OUT_BYTES, Product};
    use primitives::field::{F192, PHI_8_TABLE_192, mul4};

    use super::super::{ELL, N_MEDIUM_VALUES, gamma_powers};

    /// The maps of each medium position `b`: the weights `gamma^b * phi_8(2^s)`.
    pub(in super::super) type Maps<P> = [[<P as Product>::Map; OUT_BYTES]; N_MEDIUM_VALUES];

    /// The maps of the product `P`.
    pub(in super::super) fn maps<P: Product>() -> Maps<P> {
        let units: [F192; 8] = std::array::from_fn(|s| PHI_8_TABLE_192[1 << s]);
        gamma_powers().map(|g| P::maps(&units.map(|u| g * u)))
    }

    /// `sum_b gamma^b * phi_8(rows[b][lane])` for every lane, byte-sliced.
    #[target_feature(enable = "avx2")]
    pub(in super::super) fn convert<P: Product>(rows: &[[u8; 64]], maps: &Maps<P>) -> [F192; ELL] {
        let mut out = [F192::ZERO; ELL];
        for (h, out) in out.as_chunks_mut::<HALF>().0.iter_mut().enumerate() {
            let mut acc = [_mm256_setzero_si256(); OUT_BYTES];
            // Eight output bytes at a time keep their accumulators in registers.
            for (o, acc) in acc.as_chunks_mut::<8>().0.iter_mut().enumerate() {
                for (row, m) in rows.iter().zip(maps) {
                    // SAFETY: each half-row is 32 bytes.
                    let x = unsafe { _mm256_loadu_si256(row[HALF * h..].as_ptr().cast()) };
                    avx2::accumulate8::<P>(acc, P::input(x), &m[8 * o..]);
                }
            }
            avx2::store_f192(&acc, out);
        }
        out
    }

    /// One worker's per-lane sums for `A B` and for `C`.
    pub(in super::super) struct Convert {
        ab: [F192; ELL],
        c: [F192; ELL],
    }

    impl Convert {
        pub(in super::super) const fn new() -> Self {
            Self {
                ab: [F192::ZERO; ELL],
                c: [F192::ZERO; ELL],
            }
        }

        /// Add one window's medium bytes, a 64-lane row per medium position, at weight `eq_lo`.
        #[inline(always)]
        pub(in super::super) fn accumulate(&mut self, ab: &[[u8; 64]], c: &[[u8; 64]], eq_lo: F192) {
            static MAPS: LazyLock<Maps<Best>> = LazyLock::new(maps::<Best>);
            for (acc, rows) in [(&mut self.ab, ab), (&mut self.c, c)] {
                // SAFETY: the module is compiled only with AVX2 enabled.
                let cf = unsafe { convert::<Best>(rows, &MAPS) };
                for (acc, cf) in acc.as_chunks_mut::<4>().0.iter_mut().zip(cf.as_chunks::<4>().0) {
                    for (acc, p) in acc.iter_mut().zip(mul4(*cf, [eq_lo; 4])) {
                        *acc += p;
                    }
                }
            }
        }

        /// The `A B` and `C` sums.
        pub(in super::super) const fn values(&self) -> ([F192; ELL], [F192; ELL]) {
            (self.ab, self.c)
        }
    }
}

/// AVX-512 with GFNI: byte-sliced sums, register `o` holding byte `o` of every lane's sum.
///
/// The weight `eq_lo` rides the GFNI matrices, rebuilt for each window:
///
/// ```text
///     w[b][s] = (gamma^b * eq_lo) * phi_8(2^s)        phi_8(2^s) lies in the GF(2^64) base field
/// ```
///
/// So a window costs 16 products and 16 mixed products, not a product per lane.
#[cfg(all(
    target_arch = "x86_64",
    target_feature = "gfni",
    target_feature = "avx512bw",
    target_feature = "avx512vbmi"
))]
mod gfni {
    use core::arch::x86_64::*;
    use std::sync::OnceLock;

    use primitives::bit_fold::gfni::{OUT_BYTES, store_f192, weight_matrices};
    use primitives::field::{F64, F192, PHI_8_TABLE_192, mul_base8, mul4};

    use super::super::{ELL, N_MEDIUM_VALUES, gamma_powers};

    /// One worker's byte-sliced sums for `A B` and for `C`.
    pub(in super::super) struct Convert {
        ab: [__m512i; OUT_BYTES],
        c: [__m512i; OUT_BYTES],
    }

    impl Convert {
        pub(in super::super) const fn new() -> Self {
            // SAFETY: an all-zero bit pattern is a valid register value.
            unsafe { core::mem::zeroed() }
        }

        /// Add one window's medium bytes, a 64-lane row per medium position, at weight `eq_lo`.
        #[inline(always)]
        pub(in super::super) fn accumulate(&mut self, ab: &[[u8; 64]], c: &[[u8; 64]], eq_lo: F192) {
            // SAFETY: the module is compiled only with these target features enabled.
            unsafe { self.accumulate_gfni(ab, c, eq_lo) }
        }

        #[target_feature(enable = "avx512f", enable = "avx512bw", enable = "avx512vbmi", enable = "gfni")]
        fn accumulate_gfni(&mut self, ab: &[[u8; 64]], c: &[[u8; 64]], eq_lo: F192) {
            // phi_8 of the unit bytes, as base-field scalars.
            static UNITS: OnceLock<[F64; 8]> = OnceLock::new();
            let units = UNITS.get_or_init(|| {
                std::array::from_fn(|s| {
                    let phi = PHI_8_TABLE_192[1 << s];
                    assert!(phi.c1 == 0 && phi.c2 == 0, "phi_8 lands in the base field");
                    F64(phi.c0)
                })
            });

            // Medium position b's matrices: the weights (gamma^b eq_lo) phi_8(2^s).
            let mut matrices = [[0u64; OUT_BYTES]; N_MEDIUM_VALUES];
            for (quad, m) in gamma_powers()
                .as_chunks::<4>()
                .0
                .iter()
                .zip(matrices.as_chunks_mut::<4>().0)
            {
                for (t, m) in mul4(*quad, [eq_lo; 4]).iter().zip(m) {
                    *m = weight_matrices(&mul_base8(*t, *units));
                }
            }

            // Eight output bytes at a time keep sixteen accumulators in registers.
            for g in 0..3 {
                let mut acc_ab: [__m512i; 8] = std::array::from_fn(|l| self.ab[8 * g + l]);
                let mut acc_c: [__m512i; 8] = std::array::from_fn(|l| self.c[8 * g + l]);
                for ((ab, c), m) in ab.iter().zip(c).zip(&matrices) {
                    // SAFETY: each row is 64 bytes.
                    let (xa, xc) = unsafe {
                        (
                            _mm512_loadu_si512(ab.as_ptr().cast()),
                            _mm512_loadu_si512(c.as_ptr().cast()),
                        )
                    };
                    for l in 0..8 {
                        let a = _mm512_set1_epi64(m[8 * g + l] as i64);
                        acc_ab[l] = _mm512_xor_si512(acc_ab[l], _mm512_gf2p8affine_epi64_epi8::<0>(xa, a));
                        acc_c[l] = _mm512_xor_si512(acc_c[l], _mm512_gf2p8affine_epi64_epi8::<0>(xc, a));
                    }
                }
                self.ab[8 * g..8 * g + 8].copy_from_slice(&acc_ab);
                self.c[8 * g..8 * g + 8].copy_from_slice(&acc_c);
            }
        }

        /// The `A B` and `C` sums.
        pub(in super::super) fn values(&self) -> ([F192; ELL], [F192; ELL]) {
            let (mut ab, mut c) = ([F192::ZERO; ELL], [F192::ZERO; ELL]);
            // SAFETY: the module is compiled only with these target features enabled.
            unsafe {
                store_f192(&self.ab, &mut ab);
                store_f192(&self.c, &mut c);
            }
            (ab, c)
        }
    }
}

#[cfg(test)]
mod tests {
    #[cfg(all(target_arch = "x86_64", target_feature = "avx2", target_feature = "gfni"))]
    use primitives::bit_fold::avx2::Gfni;
    #[cfg(all(target_arch = "x86_64", target_feature = "avx2"))]
    use primitives::bit_fold::avx2::{Product, Shuffle};
    use primitives::field::F192;
    use primitives::test_util::Rng;

    use super::*;

    /// `n` random rows of 64 bytes.
    fn rows(rng: &mut Rng, n: usize) -> Vec<[u8; 64]> {
        (0..n).map(|_| std::array::from_fn(|_| rng.next_u8())).collect()
    }

    #[test]
    fn the_dispatched_convert_is_the_definition() {
        // Invariant: the target's convert accumulates eq_lo times the definition, per lane.
        //
        // Fixture state: two full windows of 16 medium positions, then every boundary length.
        let mut rng = Rng::new(0xC0_4E27);
        let mut convert = Convert::new();
        let (mut want_ab, mut want_c) = ([F192::ZERO; ELL], [F192::ZERO; ELL]);
        for n in [16, 16].into_iter().chain(0..16) {
            let (ab, c) = (rows(&mut rng, n), rows(&mut rng, n));
            let eq = rng.ext();
            convert.accumulate(&ab, &c, eq);
            for (lane, (w_ab, w_c)) in want_ab.iter_mut().zip(&mut want_c).enumerate() {
                *w_ab += reference(&ab)[lane] * eq;
                *w_c += reference(&c)[lane] * eq;
            }
        }
        assert_eq!(convert.values(), (want_ab, want_c));
    }

    #[cfg(all(target_arch = "x86_64", target_feature = "avx2"))]
    #[test]
    fn every_avx2_product_converts_as_the_definition() {
        // Invariant: each AVX2 product this target compiles, not only the dispatched one, is the definition.
        fn check<P: Product>(rng: &mut Rng) {
            let maps = avx2::maps::<P>();
            for n in [16, 7] {
                let rows = rows(rng, n);
                // SAFETY: the crate is built with AVX2.
                assert_eq!(unsafe { avx2::convert::<P>(&rows, &maps) }, reference(&rows), "n={n}");
            }
        }
        let mut rng = Rng::new(0xA7_C04E);
        check::<Shuffle>(&mut rng);
        #[cfg(target_feature = "gfni")]
        check::<Gfni>(&mut rng);
    }
}
