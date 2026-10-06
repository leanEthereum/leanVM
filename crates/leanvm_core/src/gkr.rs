//! The grand product via GKR (§sec:gkr): given leaves `v_0…v_{2^μ-1}`, prove the
//! root `P = ∏ v_k` of the product tree, reducing the root to one leaf evaluation
//! `Ṽ_0(ζ)`. Two binary levels are contracted at a time: a radix-four layer has
//! relation `V_i(x)=∏_{a,b∈{0,1}}V_{i-2}(a,b,x)`. Its normalized eq-trick
//! sumcheck has degree four. An odd-depth tree starts with one binary layer.
//! Leaves and every layer are `E`-valued (the bus fingerprints mix `K`-columns
//! into `E` upstream, [`crate::leaf`]).

use crate::PAR_THRESHOLD;
use fiat_shamir::arith::Verifier;
use fiat_shamir::transcript::{Challenger, ProverState, TranscriptError, Transmitter};
use parallel::SendPtr;
use primitives::field::{F192, F192Unreduced, mul_unreduced4, mul2, mul4};
#[cfg(any(
    all(target_arch = "aarch64", target_feature = "aes"),
    all(
        target_arch = "x86_64",
        target_feature = "pclmulqdq",
        not(target_feature = "vpclmulqdq")
    )
))]
use primitives::field::{F192x1, F192x1Unreduced};
#[cfg(all(target_arch = "x86_64", target_feature = "vpclmulqdq", target_feature = "avx2"))]
use primitives::field::{F192x4, F192x4Unreduced};
use primitives::multilinear::{SplitEq, interp};
use primitives::stream::Stream;
use std::mem::MaybeUninit;
#[cfg(all(target_arch = "x86_64", target_feature = "vpclmulqdq", target_feature = "avx2"))]
use std::ops::Mul;
use thiserror::Error;

/// Why the bus's grand-product GKR rejects.
#[derive(Clone, Debug, PartialEq, Eq, Error)]
pub enum GkrError {
    /// The proof stream is malformed.
    #[error(transparent)]
    Transcript(#[from] TranscriptError),
    /// A layer's sumcheck does not end at the product of the next layer's claims.
    #[error("the GKR layer {layer} does not reduce to the next")]
    LayerMismatch { layer: usize },
}

/// Rows per parallel window: enough tasks to keep every thread fed, but not so few
/// rows per task that dispatch dominates.
fn window_rows(total: usize) -> usize {
    let tasks = parallel::num_threads() * 16;
    total.div_ceil(tasks).clamp(64, 1 << 10)
}

/// The next radix-four level: entry `k` is the product of `current[4k..4k + 4]`, the last
/// four-tuple padded with ones.
///
/// Allocated at its final size in whole four-tuples, since [`QuaternaryLayerState::new`]
/// pads a level to that and growing it would copy it.
pub(crate) fn next_level(current: &[F192]) -> Vec<F192> {
    let rows = current.len().div_ceil(4);
    let full_rows = current.len() / 4;
    let mut next = Vec::with_capacity(rows.next_multiple_of(4));
    let slots = &mut next.spare_capacity_mut()[..rows];
    #[cfg(not(any(
        all(target_arch = "aarch64", target_feature = "aes"),
        all(
            target_arch = "x86_64",
            target_feature = "pclmulqdq",
            not(target_feature = "vpclmulqdq")
        )
    )))]
    let product = |row: usize| {
        let [left, right] = mul2(
            [current[4 * row], current[4 * row + 2]],
            [current[4 * row + 1], current[4 * row + 3]],
        );
        left * right
    };
    // Each value in vector registers from its load to the product's.
    #[cfg(any(
        all(target_arch = "aarch64", target_feature = "aes"),
        all(
            target_arch = "x86_64",
            target_feature = "pclmulqdq",
            not(target_feature = "vpclmulqdq")
        )
    ))]
    let product = |row: usize| {
        let child = |c: usize| F192x1::load(&current[4 * row + c]);
        F192::from((child(0) * child(1)) * (child(2) * child(3)))
    };
    if full_rows >= PAR_THRESHOLD {
        parallel::fill(&mut slots[..full_rows], |row| MaybeUninit::new(product(row)));
    } else {
        for (row, slot) in slots[..full_rows].iter_mut().enumerate() {
            slot.write(product(row));
        }
    }
    if full_rows < rows {
        slots[full_rows].write(padded_product(current, full_rows));
    }
    // SAFETY: the fill wrote `next[..full_rows]`, and the tail the one row after.
    unsafe { next.set_len(rows) };
    next
}

/// Entry `row` of [`next_level`]: the product of `current[4 * row..]`'s first four, ones past its end.
pub(crate) fn padded_product(current: &[F192], row: usize) -> F192 {
    let child = |index| current.get(4 * row + index).copied().unwrap_or(F192::ONE);
    let [left, right] = mul2([child(0), child(2)], [child(1), child(3)]);
    left * right
}

/// Build only the levels consumed by radix four: `0,2,4,…`, plus a final
/// binary root when the logical depth is odd. `first` is level 2, [`next_level`]
/// of the leaves, which the caller builds alongside them.
fn build_layers(leaves: Vec<F192>, first: Vec<F192>, mu: usize) -> Vec<Vec<F192>> {
    assert!(!leaves.is_empty());
    assert!(leaves.len() <= 1usize << mu);
    assert_eq!(
        first.len(),
        leaves.len().div_ceil(4),
        "the first level is the leaves' products"
    );
    // At mu = 22 the leaf level alone is hundreds of megabytes, and every level
    // dies with the proof.
    let mut layers: Vec<Vec<F192>> = (0..=mu).map(|_| Vec::new()).collect();
    layers[0] = leaves;
    let mut level = if mu >= 2 {
        layers[2] = first;
        2
    } else {
        0
    };
    while level + 2 <= mu {
        layers[level + 2] = next_level(&layers[level]);
        level += 2;
    }
    if level < mu {
        layers[mu] = match layers[level].as_slice() {
            [root] => vec![*root],
            [left, right] => vec![*left * *right],
            _ => unreachable!("the final binary layer has at most two explicit nodes"),
        };
    }
    layers
}

/// Most low variables of the split eq table.
///
/// The full table would be one E value per row pair of the layer, read every round and shrunk every round.
/// 2^12 entries of E is 96 KiB, which every task reads from L2.
const EQ_LOW_VARS: usize = 12;

#[inline(always)]
fn quartic_summand(lines: [[F192; 2]; 4], equality: F192) -> [F192Unreduced; 4] {
    let [left0, left2, right0, right2] = mul4(
        [lines[0][0], lines[0][1], lines[2][0], lines[2][1]],
        [lines[1][0], lines[1][1], lines[3][0], lines[3][1]],
    );
    let [left_at_one, right_at_one, c0, c4] = mul4(
        [lines[0][0] + lines[0][1], lines[2][0] + lines[2][1], left0, left2],
        [lines[1][0] + lines[1][1], lines[3][0] + lines[3][1], right0, right2],
    );
    let left1 = left_at_one + left0 + left2;
    let right1 = right_at_one + right0 + right2;
    let [middle, at_one, cross_even, cross_high] = mul4(
        [left1, left0 + left1 + left2, left0 + left2, left1 + left2],
        [right1, right0 + right1 + right2, right0 + right2, right1 + right2],
    );
    let c2 = cross_even + c0 + c4 + middle;
    let c3 = cross_high + middle + c4;
    mul_unreduced4([equality; 4], [c0 + at_one, c2, c3, c4])
}

/// [`quartic_summand`] of four row pairs at once, lane `j` for pair `j`: `low[c]` is
/// child `c` of each pair's low row, `high[c]` of its high row.
///
/// The same products, each one lane-wise product for the four pairs.
#[cfg(all(target_arch = "x86_64", target_feature = "vpclmulqdq", target_feature = "avx2"))]
#[inline(always)]
fn quartic_summand4(low: [F192x4; 4], high: [F192x4; 4], equality: F192x4) -> [F192x4Unreduced; 4] {
    let slope: [F192x4; 4] = std::array::from_fn(|c| low[c] + high[c]);
    let (left0, left2) = (low[0].mul(low[1]), slope[0].mul(slope[1]));
    let (right0, right2) = (low[2].mul(low[3]), slope[2].mul(slope[3]));
    // A line at one is the high row, and a product's three coefficients sum to it there.
    let (left_at_one, right_at_one) = (high[0].mul(high[1]), high[2].mul(high[3]));
    let left1 = left_at_one + left0 + left2;
    let right1 = right_at_one + right0 + right2;
    // These six products meet only in the four sums, so each sum is reduced once.
    let c0 = left0.mul_unreduced(right0);
    let c4 = left2.mul_unreduced(right2);
    let middle = left1.mul_unreduced(right1);
    let at_one = left_at_one.mul_unreduced(right_at_one);
    let cross_even = (left0 + left2).mul_unreduced(right0 + right2);
    let cross_high = (left1 + left2).mul_unreduced(right1 + right2);
    let c2 = cross_even ^ c0 ^ c4 ^ middle;
    let c3 = cross_high ^ middle ^ c4;
    [c0 ^ at_one, c2, c3, c4].map(|c| equality.mul_unreduced(c.reduce()))
}

/// A row's four children, or a summand's four coefficients, held in vector registers.
#[cfg(any(
    all(target_arch = "aarch64", target_feature = "aes"),
    all(
        target_arch = "x86_64",
        target_feature = "pclmulqdq",
        not(target_feature = "vpclmulqdq")
    )
))]
type Quad<T> = (T, T, T, T);

/// [`quartic_summand4`]'s products for one row pair held in vector registers: `low` is the
/// low row's four children, `high` the high row's.
#[cfg(any(
    all(target_arch = "aarch64", target_feature = "aes"),
    all(
        target_arch = "x86_64",
        target_feature = "pclmulqdq",
        not(target_feature = "vpclmulqdq")
    )
))]
#[inline(always)]
fn quartic_summand1(low: Quad<F192x1>, high: Quad<F192x1>, equality: F192x1) -> Quad<F192x1Unreduced> {
    let ((l0, l1, l2, l3), (h0, h1, h2, h3)) = (low, high);
    let (left0, left2) = (l0 * l1, (l0 + h0) * (l1 + h1));
    let (right0, right2) = (l2 * l3, (l2 + h2) * (l3 + h3));
    let (left_at_one, right_at_one) = (h0 * h1, h2 * h3);
    let left1 = left_at_one + left0 + left2;
    let right1 = right_at_one + right0 + right2;
    let c0 = left0.mul_unreduced(right0);
    let c4 = left2.mul_unreduced(right2);
    let middle = left1.mul_unreduced(right1);
    let at_one = left_at_one.mul_unreduced(right_at_one);
    let cross_even = (left0 + left2).mul_unreduced(right0 + right2);
    let cross_high = (left1 + left2).mul_unreduced(right1 + right2);
    let scaled = |c: F192x1Unreduced| equality.mul_unreduced(c.reduce());
    (
        scaled(c0 ^ at_one),
        scaled(cross_even ^ c0 ^ c4 ^ middle),
        scaled(cross_high ^ middle ^ c4),
        scaled(c4),
    )
}

/// `slice` as the values it holds.
///
/// # Safety
///
/// Every element of `slice` is initialized.
const unsafe fn assume_init(slice: &[MaybeUninit<F192>]) -> &[F192] {
    // SAFETY: `MaybeUninit<F192>` has `F192`'s layout, and the caller vouches for the values.
    unsafe { std::slice::from_raw_parts(slice.as_ptr().cast(), slice.len()) }
}

/// Row `r` of a level: its four children.
#[cfg(all(target_arch = "x86_64", target_feature = "vpclmulqdq", target_feature = "avx2"))]
#[inline(always)]
fn row(values: &[F192], r: usize) -> &[F192; 4] {
    values[4 * r..4 * r + 4].as_array().unwrap()
}

/// Two binary product levels contracted into one degree-four layer.
struct QuaternaryLayerState {
    /// Four child tables interleaved in their original order. This lets the
    /// prover consume a product-tree level without first transposing it.
    values: Vec<F192>,
    /// Scratch a fold writes into its spare capacity, then swaps with the values.
    next: Vec<F192>,
    /// Logical row count after identity padding. `values` stores an arbitrary
    /// prefix; every omitted row is the constant four-tuple one.
    logical_rows: usize,
}

impl QuaternaryLayerState {
    fn new(mut values: Vec<F192>, width: usize) -> Self {
        // Materialize only the incomplete final four-tuple. Every complete
        // all-one row after the arbitrary explicit prefix remains implicit.
        values.resize(4 * values.len().max(1).div_ceil(4), F192::ONE);
        debug_assert_eq!(values.len() % 4, 0);
        debug_assert!(values.len() <= 4 * width);
        let rows = (values.len() / 4).div_ceil(2);
        Self {
            values,
            next: Vec::with_capacity(4 * rows),
            logical_rows: width,
        }
    }

    /// `(q(0)+q(1), [X²]q, [X³]q, [X⁴]q)`.
    fn round_message(&self, equality: &SplitEq) -> [F192; 4] {
        let stored_rows = self.values.len() / 4;
        let full_pairs = stored_rows / 2;
        #[cfg(not(any(
            all(target_arch = "aarch64", target_feature = "aes"),
            all(
                target_arch = "x86_64",
                target_feature = "pclmulqdq",
                not(target_feature = "vpclmulqdq")
            )
        )))]
        let summand = |row: usize, weight: F192| -> [F192Unreduced; 4] {
            let (lo, hi) = (8 * row, 8 * row + 4);
            let lines = [0, 1, 2, 3].map(|child| {
                let at_zero = self.values[lo + child];
                [at_zero, at_zero + self.values[hi + child]]
            });
            quartic_summand(lines, weight)
        };
        let xor = |mut left: [F192Unreduced; 4], right: [F192Unreduced; 4]| {
            for coefficient in 0..4 {
                left[coefficient] ^= right[coefficient];
            }
            left
        };
        let rows = window_rows(full_pairs);
        #[cfg(all(target_arch = "x86_64", target_feature = "vpclmulqdq", target_feature = "avx2"))]
        let summand4 = |_: &mut (), pair: usize, weights: F192x4| -> [F192x4Unreduced; 4] {
            // Each row as its four children in lanes, turned to put the four pairs in lanes.
            let rows = |half: usize| {
                F192x4::transpose(std::array::from_fn(|j| {
                    F192x4::load(row(&self.values, 2 * (pair + j) + half))
                }))
            };
            quartic_summand4(rows(0), rows(1), weights)
        };
        #[cfg(any(
            all(target_arch = "aarch64", target_feature = "aes"),
            all(
                target_arch = "x86_64",
                target_feature = "pclmulqdq",
                not(target_feature = "vpclmulqdq")
            )
        ))]
        let summand1 = |row: usize, weight: F192x1| {
            let v = &self.values[8 * row..8 * row + 8];
            let child = |c: usize| F192x1::load(&v[c]);
            let low = (child(0), child(1), child(2), child(3));
            quartic_summand1(low, (child(4), child(5), child(6), child(7)), weight)
        };
        let window = |index: usize| -> [F192Unreduced; 4] {
            let base = index * rows;
            let range = base..(base + rows).min(full_pairs);
            #[cfg(all(target_arch = "x86_64", target_feature = "vpclmulqdq", target_feature = "avx2"))]
            return equality.weighted_sum_lanes(range, full_pairs, &mut (), |_, row, w| summand(row, w), summand4);
            #[cfg(any(
                all(target_arch = "aarch64", target_feature = "aes"),
                all(
                    target_arch = "x86_64",
                    target_feature = "pclmulqdq",
                    not(target_feature = "vpclmulqdq")
                )
            ))]
            return equality.weighted_sum_x1(range, summand1);
            #[cfg(not(any(
                all(target_arch = "x86_64", target_feature = "vpclmulqdq", target_feature = "avx2"),
                all(target_arch = "aarch64", target_feature = "aes"),
                all(
                    target_arch = "x86_64",
                    target_feature = "pclmulqdq",
                    not(target_feature = "vpclmulqdq")
                )
            )))]
            equality.weighted_sum(range, summand)
        };
        let windows = full_pairs.div_ceil(rows);
        let mut message = if full_pairs >= PAR_THRESHOLD {
            parallel::map_reduce(windows, || [F192Unreduced::ZERO; 4], window, xor)
        } else {
            (0..windows).map(window).fold([F192Unreduced::ZERO; 4], xor)
        };
        if !stored_rows.is_multiple_of(2) {
            let lo = 8 * full_pairs;
            let lines = [0, 1, 2, 3].map(|child| {
                let at_zero = self.values[lo + child];
                [at_zero, at_zero + F192::ONE]
            });
            message = xor(message, quartic_summand(lines, equality.at(full_pairs)));
        }
        message.map(F192Unreduced::reduce)
    }

    fn fold(&mut self, challenge: F192) {
        let stored_rows = self.values.len() / 4;
        let full_rows = stored_rows / 2;
        let rows = stored_rows.div_ceil(2);
        self.next.clear();
        let values = &self.values;
        let next = &mut self.next.spare_capacity_mut()[..4 * rows];
        #[cfg(not(all(target_arch = "aarch64", target_feature = "aes")))]
        let fold_row = |row: usize| -> [F192; 4] {
            // One slice, not eight indexes: the bounds checks and the
            // index-by-24 multiplies fall out.
            let v = &values[8 * row..8 * row + 8];
            let folds = mul4(std::array::from_fn(|child| v[child] + v[4 + child]), [challenge; 4]);
            std::array::from_fn(|child| v[child] + folds[child])
        };
        // The next round is what reads the output, and a layer this size is long
        // evicted by then, so where an ordinary store fetches the line it
        // overwrites the pair is staged and published with streaming stores.
        // Where it does not, the stage buys nothing and costs a real call, the
        // `slot.len()` being one the compiler cannot fold away.
        #[cfg(target_arch = "x86_64")]
        let window = |base: usize, destination: &mut [MaybeUninit<F192>]| {
            let stream = Stream::new();
            for (pair, slot) in destination.chunks_mut(8).enumerate() {
                let mut both = [F192::ZERO; 8];
                both[..4].copy_from_slice(&fold_row(base + 2 * pair));
                if slot.len() == 8 {
                    both[4..].copy_from_slice(&fold_row(base + 2 * pair + 1));
                }
                stream.write(slot, &both[..slot.len()]);
            }
        };
        #[cfg(not(any(target_arch = "x86_64", all(target_arch = "aarch64", target_feature = "aes"))))]
        let window = |base: usize, destination: &mut [MaybeUninit<F192>]| {
            for (pair, slot) in destination.chunks_mut(8).enumerate() {
                slot[..4].write_copy_of_slice(&fold_row(base + 2 * pair));
                if slot.len() == 8 {
                    slot[4..].write_copy_of_slice(&fold_row(base + 2 * pair + 1));
                }
            }
        };
        // Each value in vector registers from its load to its store.
        #[cfg(all(target_arch = "aarch64", target_feature = "aes"))]
        let window = |base: usize, destination: &mut [MaybeUninit<F192>]| {
            let challenge = F192x1::new(challenge);
            for (r, slot) in destination.as_chunks_mut::<4>().0.iter_mut().enumerate() {
                let v = &values[8 * (base + r)..8 * (base + r) + 8];
                for (c, slot) in slot.iter_mut().enumerate() {
                    let (left, right) = (F192x1::load(&v[c]), F192x1::load(&v[4 + c]));
                    (left + (left + right) * challenge).store(slot);
                }
            }
        };
        if full_rows >= PAR_THRESHOLD {
            let rows = window_rows(full_rows);
            parallel::chunks_mut(&mut next[..4 * full_rows], 4 * rows, |index, destination| {
                window(index * rows, destination);
            });
        } else {
            window(0, &mut next[..4 * full_rows]);
        }
        if !stored_rows.is_multiple_of(2) {
            let lo = 8 * full_rows;
            let folds = mul4(
                [0, 1, 2, 3].map(|child| self.values[lo + child] + F192::ONE),
                [challenge; 4],
            );
            for (child, fold) in folds.into_iter().enumerate() {
                next[4 * full_rows + child].write(self.values[lo + child] + fold);
            }
        }
        // SAFETY: the windows wrote the full pairs, and the tail block the odd row.
        unsafe { self.next.set_len(4 * rows) };
        std::mem::swap(&mut self.values, &mut self.next);
        self.logical_rows /= 2;
    }

    fn fold_and_message(&mut self, challenge: F192, equality: &SplitEq) -> [F192; 4] {
        let stored_rows = self.values.len() / 4;
        let rows = stored_rows.div_ceil(2);
        self.next.clear();
        let values = &self.values;
        let dst = SendPtr(self.next.spare_capacity_mut()[..4 * rows].as_mut_ptr());
        const PAIRS: usize = 16;
        let pairs = rows.div_ceil(2);
        // A pair below this has both rows and both their halves stored.
        #[cfg(all(target_arch = "x86_64", target_feature = "vpclmulqdq", target_feature = "avx2"))]
        let full_pairs = stored_rows / 4;
        #[cfg(all(target_arch = "x86_64", target_feature = "vpclmulqdq", target_feature = "avx2"))]
        let lanes = F192x4::splat(challenge);
        #[cfg(any(
            all(target_arch = "aarch64", target_feature = "aes"),
            all(
                target_arch = "x86_64",
                target_feature = "pclmulqdq",
                not(target_feature = "vpclmulqdq")
            )
        ))]
        let challenge1 = F192x1::new(challenge);
        let task = |index: usize| {
            let first = index * PAIRS;
            let end = (first + PAIRS).min(pairs);
            let end_row = (2 * end).min(rows);
            let len = 4 * (end_row - 2 * first);
            // Every slot is written before it is read, so the stage needs no zero fill.
            let mut stage = [MaybeUninit::<F192>::uninit(); 8 * PAIRS];
            #[cfg(not(any(
                all(target_arch = "aarch64", target_feature = "aes"),
                all(
                    target_arch = "x86_64",
                    target_feature = "pclmulqdq",
                    not(target_feature = "vpclmulqdq")
                )
            )))]
            let fold_row = |stage: &mut [MaybeUninit<F192>], row: usize| {
                let lo = 8 * row;
                let left = &values[lo..lo + 4];
                let right = values.get(lo + 4..lo + 8).unwrap_or(&[F192::ONE; 4]);
                let product = mul4(std::array::from_fn(|i| left[i] + right[i]), [challenge; 4]);
                let offset = 4 * (row - 2 * first);
                for i in 0..4 {
                    stage[offset + i].write(left[i] + product[i]);
                }
            };
            #[cfg(any(
                all(target_arch = "aarch64", target_feature = "aes"),
                all(
                    target_arch = "x86_64",
                    target_feature = "pclmulqdq",
                    not(target_feature = "vpclmulqdq")
                )
            ))]
            let fold_row = |stage: &mut [MaybeUninit<F192>], row: usize| {
                let lo = 8 * row;
                let left = &values[lo..lo + 4];
                let right = values.get(lo + 4..lo + 8).unwrap_or(&[F192::ONE; 4]);
                let offset = 4 * (row - 2 * first);
                for (c, slot) in stage[offset..offset + 4].iter_mut().enumerate() {
                    let (left, right) = (F192x1::load(&left[c]), F192x1::load(&right[c]));
                    (left + (left + right) * challenge1).store(slot);
                }
            };
            #[cfg(not(any(
                all(target_arch = "x86_64", target_feature = "vpclmulqdq", target_feature = "avx2"),
                all(target_arch = "aarch64", target_feature = "aes"),
                all(
                    target_arch = "x86_64",
                    target_feature = "pclmulqdq",
                    not(target_feature = "vpclmulqdq")
                )
            )))]
            let message = {
                for row in 2 * first..end_row {
                    fold_row(&mut stage, row);
                }
                // SAFETY: the loop above wrote `stage[..len]`.
                let stage = unsafe { assume_init(&stage[..len]) };
                equality.weighted_sum(first..end, |pair, weight| {
                    let lo = 8 * (pair - first);
                    let left = &stage[lo..lo + 4];
                    let right = if 2 * pair + 1 < rows {
                        &stage[lo + 4..lo + 8]
                    } else {
                        &[F192::ONE; 4]
                    };
                    let lines = std::array::from_fn(|i| [left[i], left[i] + right[i]]);
                    quartic_summand(lines, weight)
                })
            };
            // Each value in vector registers from its load to the summand's sums.
            #[cfg(any(
                all(target_arch = "aarch64", target_feature = "aes"),
                all(
                    target_arch = "x86_64",
                    target_feature = "pclmulqdq",
                    not(target_feature = "vpclmulqdq")
                )
            ))]
            let message = {
                for row in 2 * first..end_row {
                    fold_row(&mut stage, row);
                }
                // SAFETY: the loop above wrote `stage[..len]`.
                let stage = unsafe { assume_init(&stage[..len]) };
                let one = F192x1::new(F192::ONE);
                equality.weighted_sum_x1(first..end, |pair, weight| {
                    let lo = 8 * (pair - first);
                    let child = |c: usize| F192x1::load(&stage[lo + c]);
                    let high = if 2 * pair + 1 < rows {
                        (child(4), child(5), child(6), child(7))
                    } else {
                        (one, one, one, one)
                    };
                    quartic_summand1((child(0), child(1), child(2), child(3)), high, weight)
                })
            };
            // Each pair folded where its summand reads it, four pairs at a time in lanes.
            #[cfg(all(target_arch = "x86_64", target_feature = "vpclmulqdq", target_feature = "avx2"))]
            let message = equality.weighted_sum_lanes(
                first..end,
                full_pairs,
                &mut stage,
                |stage, pair, weight| {
                    let has_right = 2 * pair + 1 < rows;
                    fold_row(stage, 2 * pair);
                    if has_right {
                        fold_row(stage, 2 * pair + 1);
                    }
                    let lo = 8 * (pair - first);
                    // SAFETY: the pair's rows, written just above.
                    let pair_rows = unsafe { assume_init(&stage[lo..lo + if has_right { 8 } else { 4 }]) };
                    let left = &pair_rows[..4];
                    let right = if has_right { &pair_rows[4..8] } else { &[F192::ONE; 4] };
                    let lines = std::array::from_fn(|i| [left[i], left[i] + right[i]]);
                    quartic_summand(lines, weight)
                },
                |stage, pair, weights| {
                    // Each pair's two rows, folded with their children in lanes and staged,
                    // then turned to put the four pairs in lanes.
                    let folded = [0, 1].map(|k| {
                        F192x4::transpose(std::array::from_fn(|j| {
                            let n = 2 * (pair + j) + k;
                            let (left, right) =
                                (F192x4::load(row(values, 2 * n)), F192x4::load(row(values, 2 * n + 1)));
                            let folded = left + (left + right).mul(lanes);
                            let slot = 4 * (n - 2 * first);
                            folded.store(stage[slot..slot + 4].as_mut_array().unwrap());
                            folded
                        }))
                    });
                    quartic_summand4(folded[0], folded[1], weights)
                },
            );
            // SAFETY: every row of the task is folded into `stage[..len]` above.
            let stage = unsafe { assume_init(&stage[..len]) };
            // The next round reads the destination; this round reads only the local stage.
            let stream = Stream::new();
            // SAFETY: tasks own disjoint windows of the output's capacity, covering every row.
            unsafe { stream.write(dst.slice(8 * first, len), stage) };
            message
        };
        let xor = |mut a: [F192Unreduced; 4], b: [F192Unreduced; 4]| {
            for i in 0..4 {
                a[i] ^= b[i];
            }
            a
        };
        let tasks = pairs.div_ceil(PAIRS);
        let message = if rows >= PAR_THRESHOLD {
            parallel::map_reduce(tasks, || [F192Unreduced::ZERO; 4], task, xor)
        } else {
            (0..tasks).map(task).fold([F192Unreduced::ZERO; 4], xor)
        };
        // SAFETY: the tasks wrote every row.
        unsafe { self.next.set_len(4 * rows) };
        std::mem::swap(&mut self.values, &mut self.next);
        self.logical_rows /= 2;
        message.map(F192Unreduced::reduce)
    }

    fn children(&self) -> [F192; 4] {
        debug_assert_eq!(self.values.len(), 4);
        debug_assert_eq!(self.logical_rows, 1);
        self.values[..4].try_into().unwrap()
    }
}

/// The result of a batched grand-product proof: the two trees' leaf evaluations, at one shared point.
pub struct Products<E = F192> {
    pub point: Vec<E>,
    pub values: [E; 2],
}

/// `values[0] + λ·values[1]`, the batch's combination of one coefficient across the two trees.
fn combine([first, second]: [F192; 2], lambda: F192) -> F192 {
    first + lambda * second
}

/// Prove two identity-padded grand products as one RLC-batched radix-four GKR, over the
/// depth of the taller tree.
///
/// The two trees share a product by construction, as the bus's two sides do
/// (`cpu::filler` fills every table to a power of two, so they balance outright). ONE root
/// is sent for both, and no verifier can be handed an unbalanced pair to check.
///
/// Each tree comes as its leaves and their first product level, `gkr::next_level`.
pub fn prove_products(trees: [(Vec<F192>, Vec<F192>); 2], ps: &mut ProverState) -> Products {
    let mu = trees
        .iter()
        .map(|(lane, _)| crate::log2_ceil_usize(lane.len()))
        .max()
        .expect("at least one tree");
    assert!(
        trees.iter().all(|(lane, _)| !lane.is_empty()),
        "batched trees must be nonempty"
    );
    let mut layers = trees.map(|(lane, first)| build_layers(lane, first, mu));
    let roots = [0, 1].map(|tree| layers[tree][mu][0]);
    assert_eq!(roots[0], roots[1], "the bus needs the two products to agree");
    ps.add_scalar(roots[0]);
    let mut lambda = ps.sample();
    let mut point = Vec::new();
    let mut values = roots;

    let mut layer = mu;
    while layer > 0 {
        let round_count = mu - layer;
        if layer % 2 == 1 {
            debug_assert_eq!(round_count, 0, "only the root-most layer may be binary");
            let tails: [[F192; 2]; 2] = std::array::from_fn(|tree| {
                let below = &layers[tree][layer - 1];
                match below.as_slice() {
                    [left, right] => [*left, *right],
                    [left] => [*left, F192::ONE],
                    _ => unreachable!("the root's children have at most two explicit nodes"),
                }
            });
            for tail in &tails {
                ps.add_scalars(tail);
            }
            let challenge = ps.sample();
            for (value, [left, right]) in values.iter_mut().zip(tails) {
                *value = interp(left, right, challenge);
            }
            lambda = ps.sample();
            point = vec![challenge];
            layer -= 1;
            continue;
        }

        let width = 1usize << round_count;
        let mut trees: [QuaternaryLayerState; 2] =
            std::array::from_fn(|tree| QuaternaryLayerState::new(std::mem::take(&mut layers[tree][layer - 2]), width));
        // Round `j` of this layer weighs its rows by `eq(point[1 + j..], .)`.
        let mut equality = SplitEq::with_low_vars(if round_count > 0 { &point[1..] } else { &[] }, EQ_LOW_VARS);
        let mut round_point = Vec::with_capacity(round_count);
        let mut messages = if round_count > 0 {
            trees.each_ref().map(|tree| tree.round_message(&equality))
        } else {
            [[F192::ZERO; 4]; 2]
        };
        for round in 0..round_count {
            let mut coeffs = [0, 1, 2, 3].map(|coefficient| combine(messages.map(|m| m[coefficient]), lambda));
            // The kernel accumulates `q(0) + q(1)`, the wire carries `c1`. This is
            // `Transmitter::add_round_poly(_, true)` bar its dropped `c0`, which the
            // claim fixes and the prover therefore never forms.
            coeffs[0] = coeffs[0] + coeffs[1] + coeffs[2] + coeffs[3];
            ps.add_scalars(&coeffs);
            let challenge = ps.sample();
            round_point.push(challenge);
            if round + 1 < round_count {
                equality = SplitEq::with_low_vars(&point[2 + round..], EQ_LOW_VARS);
                messages = trees.each_mut().map(|tree| tree.fold_and_message(challenge, &equality));
            } else {
                // No variable is left to weigh a message by, so the final round
                // needs the fold alone. Both kernels stay for that reason; `fold`
                // is not dead.
                for tree in &mut trees {
                    tree.fold(challenge);
                }
            }
        }

        for tree in &trees {
            ps.add_scalars(&tree.children());
        }
        let low_challenge = ps.sample();
        let high_challenge = ps.sample();
        for (value, tree) in values.iter_mut().zip(&trees) {
            let tail = tree.children();
            *value = interp(
                interp(tail[0], tail[1], low_challenge),
                interp(tail[2], tail[3], low_challenge),
                high_challenge,
            );
        }
        lambda = ps.sample();
        point = vec![low_challenge, high_challenge];
        point.extend_from_slice(&round_point);
        layer -= 2;
    }

    Products { point, values }
}

/// Verify the RLC-batched radix-four proof of two trees of depth `mu`.
///
/// # Errors
///
/// Returns the first layer whose sumcheck does not end at the next layer's claims, or a malformed stream.
pub fn verify_products<V: Verifier>(v: &mut V, mu: usize) -> Result<Products<V::E>, GkrError> {
    // One root for both balancing trees, so their equality is structural: there is no
    // unbalanced pair a prover could state, and nothing for the caller to check.
    let first = v.next_scalar()?;
    let mut lambda = v.sample();
    let mut point = Vec::new();
    let mut values = [first; 2];

    let mut layer = mu;
    while layer > 0 {
        let round_count = mu - layer;
        let mut claim = v.poly_eval(&values, lambda);
        if layer % 2 == 1 {
            debug_assert_eq!(round_count, 0, "only the root-most layer may be binary");
            let mut tails = [[first; 2]; 2];
            for value in tails.iter_mut().flatten() {
                *value = v.next_scalar()?;
            }
            let products = tails.map(|[left, right]| v.mul(left, right));
            let expected = v.poly_eval(&products, lambda);
            v.ensure_eq(claim, expected, || GkrError::LayerMismatch { layer })?;
            let challenge = v.sample();
            for (value, [left, right]) in values.iter_mut().zip(tails) {
                *value = v.interp(left, right, challenge);
            }
            lambda = v.sample();
            point = vec![challenge];
            layer -= 1;
            continue;
        }

        let mut round_point = Vec::with_capacity(round_count);
        for &equality_point in point.iter().take(round_count) {
            let h = v.next_round_poly(5, claim, Some(equality_point))?;
            let challenge = v.sample();
            round_point.push(challenge);
            claim = v.poly_eval(&h, challenge);
        }
        let mut tails = [[first; 4]; 2];
        for value in tails.iter_mut().flatten() {
            *value = v.next_scalar()?;
        }
        let products = tails.map(|tail| v.product(&tail));
        let expected = v.poly_eval(&products, lambda);
        v.ensure_eq(claim, expected, || GkrError::LayerMismatch { layer })?;
        let low_challenge = v.sample();
        let high_challenge = v.sample();
        for (value, [a, b, c, d]) in values.iter_mut().zip(tails) {
            let low = v.interp(a, b, low_challenge);
            let high = v.interp(c, d, low_challenge);
            *value = v.interp(low, high, high_challenge);
        }
        lambda = v.sample();
        point = vec![low_challenge, high_challenge];
        point.extend_from_slice(&round_point);
        layer -= 2;
    }

    Ok(Products { point, values })
}

#[cfg(test)]
mod tests {
    use super::*;
    use fiat_shamir::transcript::VerifierState;

    fn mle_eval_e(table: &[F192], point: &[F192]) -> F192 {
        assert_eq!(table.len(), 1 << point.len());
        let mut folded = table.to_vec();
        for &challenge in point {
            let half = folded.len() / 2;
            for row in 0..half {
                folded[row] = interp(folded[2 * row], folded[2 * row + 1], challenge);
            }
            folded.truncate(half);
        }
        folded[0]
    }

    #[test]
    fn quartic_round_message_matches_direct_evaluation() {
        for width in [2, 4, 8, 16] {
            let below: Vec<F192> = (0..4 * width)
                .map(|i| F192::new((17 * i + width + 1) as u64, (i * i + 3) as u64, (5 * i + 7) as u64))
                .collect();
            let state = QuaternaryLayerState::new(below, width);
            // Rows weighed by eq at a point of one variable per pair index bit.
            let r: Vec<F192> = (0..(width / 2).ilog2())
                .map(|i| F192::new(u64::from(31 * i + 5), u64::from(7 * i + 1), u64::from(11 * i + 9)))
                .collect();
            let equality = SplitEq::with_low_vars(&r, EQ_LOW_VARS);
            let [difference, c2, c3, c4] = state.round_message(&equality);
            let direct = |point: F192| {
                (0..width / 2).fold(F192::ZERO, |sum, row| {
                    let values = [0, 1, 2, 3]
                        .map(|child| interp(state.values[8 * row + child], state.values[8 * row + 4 + child], point));
                    sum + equality.at(row) * values[0] * values[1] * values[2] * values[3]
                })
            };
            let c0 = direct(F192::ZERO);
            let c1 = difference + c2 + c3 + c4;
            for point in [F192::ZERO, F192::ONE, F192::Y, F192::Y.square()] {
                assert_eq!(
                    c0 + point * (c1 + point * (c2 + point * (c3 + point * c4))),
                    direct(point)
                );
            }
        }
    }

    #[test]
    fn fused_fold_matches_separate_fold_and_message() {
        for width in [4usize, 16, 1 << 14] {
            for len in [1, 4, 5, 7, 8, 9, 31, 32, 33, 4 * width - 5, 4 * width - 1, 4 * width] {
                if len > 4 * width {
                    continue;
                }
                let values: Vec<F192> = (0..len)
                    .map(|i| F192::new((17 * i + 1) as u64, (i * i + 3) as u64, (5 * i + 7) as u64))
                    .collect();
                let mut reference = QuaternaryLayerState::new(values.to_vec(), width);
                let mut fused = QuaternaryLayerState::new(values, width);
                let point: Vec<F192> = (0..width.ilog2() - 1)
                    .map(|i| F192::new(31 + u64::from(i), 7, 11))
                    .collect();
                // Round `k` weighs by eq of the point less its first `k` variables.
                let mut bound = 0;
                while reference.logical_rows > 2 {
                    let challenge = F192::new(reference.logical_rows as u64, 13, 19);
                    reference.fold(challenge);
                    bound += 1;
                    let equality = SplitEq::with_low_vars(&point[bound..], EQ_LOW_VARS);
                    let message = fused.fold_and_message(challenge, &equality);
                    assert_eq!(message, reference.round_message(&equality), "width={width}, len={len}");
                    assert_eq!(&*fused.values, &*reference.values, "width={width}, len={len}");
                }
                reference.fold(F192::Y);
                fused.fold(F192::Y);
                assert_eq!(fused.children(), reference.children());
            }
        }
    }

    #[test]
    fn radix_four_roundtrip_at_even_and_odd_depths() {
        for mu in 0..=10 {
            let first: Vec<F192> = (0..1usize << mu)
                .map(|row| F192::new((1 + row) as u64, row as u64, 0))
                .collect();
            // The two trees share their product.
            let leaves = [first.clone(), first.into_iter().rev().collect()];
            let mut ps = ProverState::from_label(b"radix-four-gkr-test");
            let proved = prove_products(leaves.each_ref().map(|l| (l.to_vec(), next_level(l))), &mut ps);
            for (lane, leaf) in leaves.iter().enumerate() {
                assert_eq!(proved.values[lane], mle_eval_e(leaf, &proved.point));
            }

            let proof = ps.into_proof();
            let mut vs = VerifierState::from_label(b"radix-four-gkr-test", &proof);
            let verified = verify_products(&mut vs, mu).expect("GKR verifies");
            assert_eq!(verified.point, proved.point);
            assert_eq!(verified.values, proved.values);
            vs.finish().expect("proof stream is consumed");
        }
    }

    #[test]
    fn implicit_identity_suffix_matches_dense_padding() {
        for mu in 3..=10 {
            let lengths = [(1usize << mu) - 3, (1usize << (mu - 1)) + 1];
            let mut leaves: [Vec<F192>; 2] = std::array::from_fn(|lane| {
                (0..lengths[lane])
                    .map(|row| F192::new((3 + row + lane * 10_007) as u64, row as u64, lane as u64))
                    .collect()
            });
            // The two trees share their product: the second's last leaf makes up the difference.
            let product = |lane: &[F192]| lane.iter().fold(F192::ONE, |p, &v| p * v);
            let last = leaves[1].len() - 1;
            leaves[1][last] = product(&leaves[0]) * product(&leaves[1][..last]).inv();
            let dense = leaves.each_ref().map(|lane| {
                let mut padded = lane.clone();
                padded.resize(1 << mu, F192::ONE);
                padded
            });
            let mut sparse_ps = ProverState::from_label(b"sparse-radix-four-gkr-test");
            let proved = prove_products(leaves.each_ref().map(|l| (l.to_vec(), next_level(l))), &mut sparse_ps);
            for (lane, values) in dense.iter().enumerate() {
                assert_eq!(proved.values[lane], mle_eval_e(values, &proved.point));
            }
            let proof = sparse_ps.into_proof();
            let mut dense_ps = ProverState::from_label(b"sparse-radix-four-gkr-test");
            let dense_proved = prove_products(dense.each_ref().map(|l| (l.to_vec(), next_level(l))), &mut dense_ps);
            assert_eq!(dense_proved.point, proved.point);
            assert_eq!(dense_proved.values, proved.values);
            assert_eq!(dense_ps.into_proof().stream, proof.stream);
            let mut vs = VerifierState::from_label(b"sparse-radix-four-gkr-test", &proof);
            let verified = verify_products(&mut vs, mu).expect("GKR verifies");
            assert_eq!(verified.point, proved.point);
            assert_eq!(verified.values, proved.values);
            vs.finish().expect("proof stream is consumed");
        }
    }
}
