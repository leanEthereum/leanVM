//! The first lane rounds from one pass, and the fold of all their lane bits at once.
//!
//! Lane round `j`'s message sums products of the witness and the weight, both
//! folded by the `j` challenges before it. In those challenges each product has
//! degree two per variable, so its sums at the points of `{0, 1, inf}^R` (`inf`
//! the leading coefficient), over every group of `2^R` lanes, determine the
//! messages of rounds `0..R`. One pass over the committed witness accumulates
//! them, each of those messages is interpolated once the challenges before it are
//! drawn, and one more pass folds all `R` lane bits at once (the small-value
//! precomputation of Bagad, Dao, Domb and Thaler, <https://eprint.iacr.org/2025/1117>:
//! the witness is in `K`, so every product is a mixed one).
//!
use primitives::PrimeCharacteristicRing;

use super::{
    Basis, BasisFill, FIRST_PASS_PAR_THRESHOLD, INITIAL_BASIS_CHUNK, KEEP_WEIGHT_MAX_THREADS, PRECOMPUTED_ROUNDS,
    SumcheckMessage, window,
};
use parallel::SendPtr;
use primitives::bit_fold;
use primitives::stream::Stream;
use primitives::{ExtensionField, F64, F192, F192MixedAccumulator, Field, PackedFieldExtension, PackedValue};
use std::ops::Range;

/// Lanes per group, and points of `{0, 1, inf}^R`, `R` being [`PRECOMPUTED_ROUNDS`].
const GROUP: usize = 1 << PRECOMPUTED_ROUNDS;
const GRID: usize = 3usize.pow(PRECOMPUTED_ROUNDS as u32);

/// Grid index of each lane of a group: lane bit `i` is ternary digit `i`, and digit 2 is `inf`.
const LANE_IN_GRID: [usize; GROUP] = {
    let mut index = [0; GROUP];
    let mut lane = 0;
    while lane < GROUP {
        let (mut bits, mut weight) = (lane, 1);
        while bits > 0 {
            index[lane] += (bits & 1) * weight;
            bits >>= 1;
            weight *= 3;
        }
        lane += 1;
    }
    index
};

/// Offsets the first pass extends side by side.
const ROW: usize = 8;

/// Extend values at the lanes' grid points to all of `{0, 1, inf}^R`, one digit at a time:
/// a multilinear's `inf` is the sum of its `0` and `1`.
#[inline(always)]
fn extend_grid<T: Copy, const R: usize>(grid: &mut [T; GRID], add: impl Fn(&T, &T) -> T) {
    let mut stride = 1;
    for i in 0..R {
        for &high in &LANE_IN_GRID[..1 << (R - 1 - i)] {
            let base = 3 * stride * high;
            for at in base..base + stride {
                grid[at + 2 * stride] = add(&grid[at], &grid[at + stride]);
            }
        }
        stride *= 3;
    }
}

/// Coefficient values packed by the upstream field backend.
type CoefficientPacking = <F64 as Field>::Packing;
/// Extension values carried in those coefficient lanes.
type WeightPacking = <F192 as ExtensionField<F64>>::ExtensionPacking;
/// Values per upstream packing.
const WEIGHT_LANES: usize = CoefficientPacking::WIDTH;
/// Packings needed for one row.
const WEIGHT_PACKS: usize = ROW / WEIGHT_LANES;
const _: () = assert!(ROW.is_multiple_of(WEIGHT_LANES));

/// One row of multilinear weights in the upstream packing's coordinate layout.
#[derive(Clone, Copy, Default)]
struct WeightRow([WeightPacking; WEIGHT_PACKS]);
impl WeightRow {
    /// Pack a row once, padding its tail with zero.
    fn pack(w: &[F192]) -> Self {
        assert!(w.len() <= ROW);
        Self(std::array::from_fn(|group| {
            <WeightPacking as PackedFieldExtension<F64, F192>>::from_ext_fn(|lane| {
                w.get(group * WEIGHT_LANES + lane).copied().unwrap_or(F192::ZERO)
            })
        }))
    }
    fn add(&self, other: &Self) -> Self {
        Self(std::array::from_fn(|i| self.0[i] + other.0[i]))
    }
}

/// A row's polynomial sums, reduced only when the complete grid is consumed.
#[derive(Clone, Copy, Default)]
struct ProductRow(F192MixedAccumulator);
impl ProductRow {
    fn mul_acc(&mut self, w: &WeightRow, k: &[u64; ROW]) {
        for (group, &values) in w.0.iter().enumerate() {
            let weights = CoefficientPacking::from_fn(|lane| F64::new(k[group * WEIGHT_LANES + lane]));
            self.0.add_packed_dot_product(values, weights);
        }
    }
    fn add(&mut self, other: &Self) {
        self.0.merge(other.0);
    }
    fn sum(&self) -> F192 {
        self.0.finish()
    }
}

/// The sums of the first pass, from which the first `rounds` lane rounds' messages follow.
pub(crate) struct InitialRounds {
    pub(super) rounds: usize,
    /// `sum f(d) * b(d)` at each `d` of `{0, 1, inf}^rounds`, over every lane group and offset.
    grid: Vec<F192>,
}

impl InitialRounds {
    /// Lane round `j`'s message, given the challenges `rs` of the rounds before it.
    pub(super) fn message(&self, j: usize, rs: &[F192]) -> SumcheckMessage {
        assert!(j < self.rounds && rs.len() == j);
        let low = 3usize.pow(j as u32);
        // Lagrange weights of `{0, 1, inf}^j` at `rs`: a quadratic has `q(r) = q(0)(1+r) + q(1)r + q(inf)(r+r^2)`.
        let mut weights = vec![F192::ONE];
        for &r in rs {
            let at = [F192::ONE + r, r, r * r + r];
            weights = at.iter().flat_map(|&l| weights.iter().map(move |&w| w * l)).collect();
        }
        // Digit `j` is the round's variable, at 0 or inf; the lane bits above it are summed over the cube.
        let [u_0, u_2] = [0, 2].map(|x| {
            let mut sums = vec![F192::ZERO; low];
            for &high in &LANE_IN_GRID[..1 << (self.rounds - 1 - j)] {
                let base = low * (x + 3 * high);
                for (s, &g) in sums.iter_mut().zip(&self.grid[base..base + low]) {
                    *s += g;
                }
            }
            sums.iter().zip(&weights).fold(F192::ZERO, |acc, (&s, &w)| acc + s * w)
        });
        SumcheckMessage { u_0, u_2 }
    }
}

/// The first pass: the grid sums of the first `min(PRECOMPUTED_ROUNDS, initial_k)` lane rounds.
pub(crate) fn initial_rounds(f: &[F64], block: usize, initial_k: usize, b: &Basis<'_>) -> InitialRounds {
    first_pass(f, block, initial_k, b, None)
}

/// [`initial_rounds`] over a regenerated weight, and the weight the first fold then reads.
///
/// The byte tables always keep the weight. SIMD backends keep it on small pools and refill it on larger ones.
pub(crate) fn initial_rounds_virtual<'a>(
    f: &[F64],
    block: usize,
    initial_k: usize,
    fill: &'a BasisFill<'a>,
) -> (InitialRounds, Basis<'a>) {
    if bit_fold::PORTABLE || parallel::num_threads() <= KEEP_WEIGHT_MAX_THREADS {
        let (rounds, kept) = initial_rounds_kept(f, block, initial_k, fill);
        (rounds, Basis::Dense(kept))
    } else {
        (
            first_pass(f, block, initial_k, &Basis::Virtual(fill), None),
            Basis::Virtual(fill),
        )
    }
}

/// [`initial_rounds`] over a regenerated weight, which it also writes out whole.
fn initial_rounds_kept(f: &[F64], block: usize, initial_k: usize, fill: &BasisFill<'_>) -> (InitialRounds, Vec<F192>) {
    let mut kept = Box::<[F192]>::new_uninit_slice(f.len());
    let rounds = first_pass(
        f,
        block,
        initial_k,
        &Basis::Virtual(fill),
        Some(SendPtr(kept.as_mut_ptr().cast::<F192>())),
    );
    // SAFETY: the first pass filled every window of every lane of `f` once, and kept each in its slots.
    (rounds, unsafe { kept.assume_init() }.into_vec())
}

/// [`initial_rounds`], writing each window of the weight it reads to `keep` when given.
fn first_pass(f: &[F64], block: usize, initial_k: usize, b: &Basis<'_>, keep: Option<SendPtr<F192>>) -> InitialRounds {
    if let Basis::Dense(b) = b {
        assert_eq!(b.len(), f.len());
    }
    assert!(block.is_power_of_two() && f.len().is_multiple_of(block));
    let rounds = PRECOMPUTED_ROUNDS.min(initial_k);
    assert!(rounds >= 1, "at least one lane round");
    let n_lanes = f.len() / block;
    let whole = n_lanes >> rounds << rounds;
    let mut grid = if whole > 0 {
        grid_pass(rounds, f, block, b, 0..whole, keep)
    } else {
        vec![F192::ZERO; 3usize.pow(rounds as u32)]
    };
    // A partial last group is summed over the digits its lanes reach. Past them every
    // lane bit is clear: at 1 the group has nothing, and at 0 and at inf it has those sums.
    if whole < n_lanes {
        let digits = (n_lanes - whole).next_power_of_two().ilog2() as usize;
        let tail = grid_pass(digits, f, block, b, whole..n_lanes, keep);
        let low = tail.len();
        for &high in &LANE_IN_GRID[..1 << (rounds - digits)] {
            let base = low * 2 * high;
            for (g, &t) in grid[base..base + low].iter_mut().zip(&tail) {
                *g += t;
            }
        }
    }
    InitialRounds { rounds, grid }
}

/// The grid sums over `lanes`, `rounds` digits at a time: whole groups, or one group whose
/// missing lanes are zero.
fn grid_pass(
    rounds: usize,
    f: &[F64],
    block: usize,
    b: &Basis<'_>,
    lanes: Range<usize>,
    keep: Option<SendPtr<F192>>,
) -> Vec<F192> {
    match rounds {
        0 => grid_pass_with::<0>(f, block, b, lanes, keep),
        1 => grid_pass_with::<1>(f, block, b, lanes, keep),
        2 => grid_pass_with::<2>(f, block, b, lanes, keep),
        3 => grid_pass_with::<3>(f, block, b, lanes, keep),
        4 => grid_pass_with::<4>(f, block, b, lanes, keep),
        _ => unreachable!("at most PRECOMPUTED_ROUNDS digits"),
    }
}

fn grid_pass_with<const R: usize>(
    f: &[F64],
    block: usize,
    b: &Basis<'_>,
    lanes: Range<usize>,
    keep: Option<SendPtr<F192>>,
) -> Vec<F192> {
    let group = 1 << R;
    let points = 3usize.pow(R as u32);
    // A regenerated weight is filled one aligned chunk at a time, or one whole block below that.
    let chunk = block.min(INITIAL_BASIS_CHUNK);
    let per = block / chunk;
    static ZERO_WORDS: [F64; INITIAL_BASIS_CHUNK] = [F64::ZERO; INITIAL_BASIS_CHUNK];
    static ZERO_WEIGHTS: [F192; INITIAL_BASIS_CHUNK] = [F192::ZERO; INITIAL_BASIS_CHUNK];

    struct Scratch {
        raw: [[F192; INITIAL_BASIS_CHUNK]; GROUP],
        fg: [[u64; ROW]; GRID],
        bg: [WeightRow; GRID],
    }
    type Acc = [ProductRow; GRID];
    // Below a row's width the tail of every row stays zero, and so do its products.
    let width = chunk.min(ROW);
    let task = |scratch: &mut Scratch, acc: &mut Acc, t: usize| {
        let Scratch { raw, fg, bg } = scratch;
        let (g, x0) = (t / per, (t % per) * chunk);
        // A lane past the range is zero.
        let mut fs: [&[F64]; GROUP] = [&ZERO_WORDS[..chunk]; GROUP];
        let mut bs: [&[F192]; GROUP] = [&ZERO_WEIGHTS[..chunk]; GROUP];
        for (l, raw) in raw.iter_mut().enumerate().take(group) {
            let lane = lanes.start + g * group + l;
            if lane < lanes.end {
                let at = lane * block + x0;
                fs[l] = &f[at..at + chunk];
                bs[l] = window(b, raw, at, chunk);
                if let Some(keep) = keep {
                    // SAFETY: `keep` holds `f.len()` weights, and no other task fills the window at `at`.
                    Stream::new().copy(unsafe { keep.slice(at, chunk) }, bs[l]);
                }
            }
        }
        for x in (0..chunk).step_by(ROW) {
            for l in 0..group {
                for (d, s) in fg[LANE_IN_GRID[l]].iter_mut().zip(&fs[l][x..x + width]) {
                    *d = s.to_bits();
                }
                bg[LANE_IN_GRID[l]] = WeightRow::pack(&bs[l][x..x + width]);
            }
            extend_grid::<_, R>(fg, |a, b| std::array::from_fn(|i| a[i] ^ b[i]));
            extend_grid::<_, R>(bg, WeightRow::add);
            for (a, (k, w)) in acc.iter_mut().zip(fg.iter().zip(bg.iter())).take(points) {
                a.mul_acc(w, k);
            }
        }
    };

    let n_tasks = lanes.len().div_ceil(group) * per;
    let new_scratch = || {
        Box::new(Scratch {
            raw: [[F192::ZERO; INITIAL_BASIS_CHUNK]; GROUP],
            fg: [[0; ROW]; GRID],
            bg: [WeightRow::default(); GRID],
        })
    };
    let new_acc = || Box::new([ProductRow::default(); GRID]);
    let acc = if lanes.len() * block < FIRST_PASS_PAR_THRESHOLD {
        let (mut scratch, mut acc) = (new_scratch(), new_acc());
        for t in 0..n_tasks {
            task(&mut scratch, &mut acc, t);
        }
        acc
    } else {
        parallel::map_reduce_with_state(
            n_tasks,
            new_scratch,
            new_acc,
            |scratch, acc, t| task(scratch, acc, t),
            |mut a, c| {
                for (a, c) in a.iter_mut().zip(c.iter()) {
                    a.add(c);
                }
                a
            },
        )
    };
    acc[..points].iter().map(ProductRow::sum).collect()
}

/// The common multiplier for one lane's contribution.
#[derive(Clone, Copy)]
pub(super) struct LaneWeight(F192);
impl LaneWeight {
    pub(super) const fn new(e: F192) -> Self {
        Self(e)
    }
}

/// Sums of weighted values for one window, using the upstream coefficient layout.
#[derive(Clone, Copy)]
pub(super) struct WeightFold([WeightPacking; INITIAL_BASIS_CHUNK / WEIGHT_LANES]);
impl Default for WeightFold {
    fn default() -> Self {
        Self([WeightPacking::ZERO; INITIAL_BASIS_CHUNK / WEIGHT_LANES])
    }
}
impl WeightFold {
    /// Add one lane of extension values through upstream packed products.
    pub(super) fn add(&mut self, e: &LaneWeight, b: &[F192]) {
        assert!(b.len() <= INITIAL_BASIS_CHUNK);
        let weight = WeightPacking::from(e.0);
        for (group, values) in b.chunks(WEIGHT_LANES).enumerate() {
            let values = <WeightPacking as PackedFieldExtension<F64, F192>>::from_ext_fn(|lane| {
                values.get(lane).copied().unwrap_or(F192::ZERO)
            });
            self.0[group] += weight * values;
        }
    }
    /// Add one lane of coefficient-field values through upstream mixed products.
    pub(super) fn add_base(&mut self, e: &LaneWeight, f: &[F64]) {
        assert!(f.len() <= INITIAL_BASIS_CHUNK);
        let weight = WeightPacking::from(e.0);
        for (group, values) in f.chunks(WEIGHT_LANES).enumerate() {
            let values = CoefficientPacking::from_fn(|lane| values.get(lane).copied().unwrap_or(F64::ZERO));
            self.0[group] += weight * values;
        }
    }
    /// Write every accumulated value, including a short final group.
    pub(super) fn write(&self, dst: &mut [F192]) {
        assert!(dst.len() <= INITIAL_BASIS_CHUNK);
        for (&values, out) in self.0.iter().zip(dst.chunks_mut(WEIGHT_LANES)) {
            if out.len() == WEIGHT_LANES {
                <WeightPacking as PackedFieldExtension<F64, F192>>::to_ext_slice(&values, out);
            } else {
                let mut tail = [F192::ZERO; WEIGHT_LANES];
                <WeightPacking as PackedFieldExtension<F64, F192>>::to_ext_slice(&values, &mut tail);
                out.copy_from_slice(&tail[..out.len()]);
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::whir::INITIAL_FOLDING_FACTOR;
    use primitives::PrimeCharacteristicRing;
    use primitives::test_util::Rng;

    #[test]
    fn grid_extension_products_match_scalar_definition() {
        let mut rng = Rng::new(0x671D);
        for rounds in 1..=PRECOMPUTED_ROUNDS {
            for block in [1, 2, 4, 8, 16] {
                for lanes in [1, (1 << rounds) - 1, 1 << rounds, (1 << rounds) + 3] {
                    let f: Vec<F64> = (0..block * lanes).map(|_| F64::new(rng.next_u64())).collect();
                    let weight = rng.ext_vec(f.len());
                    let got = initial_rounds(&f, block, rounds, &Basis::Dense(weight.clone()));
                    for (point, &sum) in got.grid.iter().enumerate() {
                        let mut want = F192::ZERO;
                        for start in (0..lanes).step_by(1 << rounds) {
                            for x in 0..block {
                                let (mut k, mut e) = (0, F192::ZERO);
                                for lane in 0..(1 << rounds).min(lanes - start) {
                                    let included = (0..rounds).all(|bit| {
                                        let digit = point / 3usize.pow(bit as u32) % 3;
                                        digit == 2 || digit == (lane >> bit) & 1
                                    });
                                    if included {
                                        k ^= f[(start + lane) * block + x].to_bits();
                                        e += weight[(start + lane) * block + x];
                                    }
                                }
                                want += F192::new(e.coefficients().map(|coordinate| coordinate * F64::new(k)));
                            }
                        }
                        assert_eq!(
                            sum, want,
                            "rounds={rounds}, block={block}, lanes={lanes}, point={point}"
                        );
                    }
                }
            }
        }
    }

    #[test]
    fn the_kept_weight_is_the_filled_one() {
        // Invariant: writing the weight out leaves the sums alone and keeps every word of every lane, partial groups
        // and blocks below one fill chunk included.
        let mut rng = Rng::new(0x6EE9);
        for block in [1, 16, INITIAL_BASIS_CHUNK, 4 * INITIAL_BASIS_CHUNK] {
            for lanes in [1, 3, 5, GROUP - 1, GROUP, GROUP + 1, 37] {
                let f: Vec<F64> = (0..block * lanes).map(|_| F64::new(rng.next_u64())).collect();
                let weight = rng.ext_vec(f.len());
                let fill = |start: usize, out: &mut [F192]| out.copy_from_slice(&weight[start..start + out.len()]);
                let (rounds, kept) = initial_rounds_kept(&f, block, INITIAL_FOLDING_FACTOR, &fill);
                let expected = initial_rounds(&f, block, INITIAL_FOLDING_FACTOR, &Basis::Dense(weight.clone()));
                assert_eq!(rounds.grid, expected.grid, "block={block}, lanes={lanes}");
                assert_eq!(kept, weight, "block={block}, lanes={lanes}");
            }
        }
    }
}
