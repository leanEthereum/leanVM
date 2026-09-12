//! The grand product via GKR (§sec:gkr): given leaves `v_0…v_{2^μ-1}`, prove the
//! root `P = ∏ v_k` of the product tree, reducing the root to one leaf evaluation
//! `Ṽ_0(ζ)`. Two binary levels are contracted at a time: a radix-four layer has
//! relation `V_i(x)=∏_{a,b∈{0,1}}V_{i-2}(a,b,x)`. Its normalized eq-trick
//! sumcheck has degree four. An odd-depth tree starts with one binary layer.
//! Fingerprint trees have `E`-valued layers. The count tree stays in `K` until
//! each layer's first sumcheck fold lifts its inputs into `E`.

use crate::PAR_THRESHOLD;
use crate::colval::ColVal;
use crate::transcript::{Challenger, ProverState, Receiver, Transmitter, VerifierState};
use primitives::field::{F64, F192, F192Unreduced, mul_unreduced4, mul2, mul4};
use primitives::multilinear::{eq_table, interp, poly_eval, shrink_eq_low};
use primitives::stream::Stream;
use zk_alloc::ArenaVec;

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum GkrError {
    Truncated,
    LayerMismatch { layer: usize },
}

/// Rows per parallel window: enough tasks to keep every thread fed, but not so few
/// rows per task that dispatch dominates.
fn window_rows(total: usize) -> usize {
    let tasks = parallel::num_threads() * 16;
    total.div_ceil(tasks).clamp(64, 1 << 10)
}

trait ProductValue: ColVal {
    fn mul_pair(a: [Self; 2], b: [Self; 2]) -> [Self; 2];
    fn mul_quad(a: [Self; 4], b: [Self; 4]) -> [Self; 4];
    fn weighted_quad(values: [Self; 4], weight: F192) -> [Self::Unreduced; 4];
    fn fold_quad(left: &[Self], right: &[Self], challenge: F192) -> [F192; 4];
}

impl ProductValue for F192 {
    #[inline(always)]
    fn mul_pair(a: [Self; 2], b: [Self; 2]) -> [Self; 2] {
        mul2(a, b)
    }

    #[inline(always)]
    fn mul_quad(a: [Self; 4], b: [Self; 4]) -> [Self; 4] {
        mul4(a, b)
    }

    #[inline(always)]
    fn weighted_quad(values: [Self; 4], weight: F192) -> [Self::Unreduced; 4] {
        mul_unreduced4([weight; 4], values)
    }

    #[inline(always)]
    fn fold_quad(left: &[Self], right: &[Self], challenge: F192) -> [F192; 4] {
        let products = mul4(std::array::from_fn(|i| left[i] + right[i]), [challenge; 4]);
        std::array::from_fn(|i| left[i] + products[i])
    }
}

impl ProductValue for F64 {
    #[inline(always)]
    fn mul_pair(a: [Self; 2], b: [Self; 2]) -> [Self; 2] {
        std::array::from_fn(|i| a[i] * b[i])
    }

    #[inline(always)]
    fn mul_quad(a: [Self; 4], b: [Self; 4]) -> [Self; 4] {
        std::array::from_fn(|i| a[i] * b[i])
    }

    #[inline(always)]
    fn weighted_quad(values: [Self; 4], weight: F192) -> [Self::Unreduced; 4] {
        values.map(|value| weight.mul_base_unreduced(value))
    }

    #[inline(always)]
    fn fold_quad(left: &[Self], right: &[Self], challenge: F192) -> [F192; 4] {
        std::array::from_fn(|i| F192::from(left[i]) + challenge.mul_base(left[i] + right[i]))
    }
}

enum LayerValues {
    Base(ArenaVec<F64>),
    Ext(ArenaVec<F192>),
}

impl Default for LayerValues {
    fn default() -> Self {
        Self::Ext(ArenaVec::new())
    }
}

impl From<ArenaVec<F192>> for LayerValues {
    fn from(values: ArenaVec<F192>) -> Self {
        Self::Ext(values)
    }
}

impl From<ArenaVec<F64>> for LayerValues {
    fn from(values: ArenaVec<F64>) -> Self {
        Self::Base(values)
    }
}

impl LayerValues {
    fn len(&self) -> usize {
        match self {
            Self::Base(values) => values.len(),
            Self::Ext(values) => values.len(),
        }
    }

    fn at(&self, index: usize) -> F192 {
        match self {
            Self::Base(values) => F192::from(values[index]),
            Self::Ext(values) => values[index],
        }
    }

    fn pad(&mut self, len: usize) {
        match self {
            Self::Base(values) => values.resize(len, F64::ONE),
            Self::Ext(values) => values.resize(len, F192::ONE),
        }
    }
}

/// Build only the levels consumed by radix four: `0,2,4,…`, plus a final
/// binary root when the logical depth is odd.
fn build_layers<T: ProductValue>(leaves: ArenaVec<T>, mu: usize) -> Vec<ArenaVec<T>> {
    assert!(!leaves.is_empty());
    assert!(leaves.len() <= 1usize << mu);
    // At mu = 22 the leaf level alone is hundreds of megabytes, and every level
    // dies with the proof.
    let mut layers: Vec<ArenaVec<T>> = (0..=mu).map(|_| ArenaVec::new()).collect();
    layers[0] = leaves;
    let mut level = 0;
    while level + 2 <= mu {
        let current = &layers[level];
        let full_rows = current.len() / 4;
        let product = |row: usize| {
            let [left, right] = T::mul_pair(
                [current[4 * row], current[4 * row + 2]],
                [current[4 * row + 1], current[4 * row + 3]],
            );
            left * right
        };
        let mut next: ArenaVec<T> = if current.len() == 1 {
            ArenaVec::from_iter([current[0]])
        } else if current.len() == 2 {
            ArenaVec::from_iter([current[0] * current[1]])
        } else if full_rows >= PAR_THRESHOLD {
            primitives::par_collect_arena(full_rows, product)
        } else {
            (0..full_rows).map(product).collect()
        };
        if !current.len().is_multiple_of(4) && current.len() > 2 {
            let row = full_rows;
            let child = |index| current.get(4 * row + index).copied().unwrap_or(T::ONE);
            let [left, right] = T::mul_pair([child(0), child(2)], [child(1), child(3)]);
            next.push(left * right);
        }
        level += 2;
        layers[level] = next;
    }
    if level < mu {
        layers[mu] = match layers[level].as_slice() {
            [root] => ArenaVec::from_iter([*root]),
            [left, right] => ArenaVec::from_iter([*left * *right]),
            _ => unreachable!("the final binary layer has at most two explicit nodes"),
        };
    }
    layers
}

#[inline(always)]
fn quartic_summand<T: ProductValue>(lines: [[T; 2]; 4], equality: F192) -> [T::Unreduced; 4] {
    let [left0, left2, right0, right2] = T::mul_quad(
        [lines[0][0], lines[0][1], lines[2][0], lines[2][1]],
        [lines[1][0], lines[1][1], lines[3][0], lines[3][1]],
    );
    let [left_at_one, right_at_one, c0, c4] = T::mul_quad(
        [lines[0][0] + lines[0][1], lines[2][0] + lines[2][1], left0, left2],
        [lines[1][0] + lines[1][1], lines[3][0] + lines[3][1], right0, right2],
    );
    let left1 = left_at_one + left0 + left2;
    let right1 = right_at_one + right0 + right2;
    let [middle, at_one, cross_even, cross_high] = T::mul_quad(
        [left1, left0 + left1 + left2, left0 + left2, left1 + left2],
        [right1, right0 + right1 + right2, right0 + right2, right1 + right2],
    );
    let c2 = cross_even + c0 + c4 + middle;
    let c3 = cross_high + middle + c4;
    T::weighted_quad([c0 + at_one, c2, c3, c4], equality)
}

/// Two binary product levels contracted into one degree-four layer.
struct QuaternaryLayerState {
    /// Four child tables interleaved in their original order. This lets the
    /// prover consume a product-tree level without first transposing it.
    values: LayerValues,
    next: ArenaVec<F192>,
    /// Logical row count after identity padding. `values` stores an arbitrary
    /// prefix; every omitted row is the constant four-tuple one.
    logical_rows: usize,
}

impl QuaternaryLayerState {
    fn new(values: impl Into<LayerValues>, width: usize) -> Self {
        let mut values = values.into();
        // Materialize only the incomplete final four-tuple. Every complete
        // all-one row after the arbitrary explicit prefix remains implicit.
        values.pad(4 * values.len().max(1).div_ceil(4));
        debug_assert_eq!(values.len() % 4, 0);
        debug_assert!(values.len() <= 4 * width);
        let rows = (values.len() / 4).div_ceil(2);
        Self {
            values,
            // SAFETY: the first `fold` writes every slot of `next[..4 * rows]` before
            // any read (its windows cover the full pairs, its tail block the odd row),
            // and neither `round_message` nor `children` reads `next`.
            next: unsafe { ArenaVec::uninitialized(4 * rows) },
            logical_rows: width,
        }
    }

    /// `(q(0)+q(1), [X²]q, [X³]q, [X⁴]q)`.
    fn round_message(&self, equality: &[F192]) -> [F192; 4] {
        match &self.values {
            LayerValues::Base(values) => Self::round_message_values(values, equality),
            LayerValues::Ext(values) => Self::round_message_values(values, equality),
        }
    }

    fn round_message_values<T: ProductValue>(values: &[T], equality: &[F192]) -> [F192; 4] {
        let stored_rows = values.len() / 4;
        let full_pairs = stored_rows / 2;
        let summand = |row: usize| -> [T::Unreduced; 4] {
            let (lo, hi) = (8 * row, 8 * row + 4);
            let lines = [0, 1, 2, 3].map(|child| {
                let at_zero = values[lo + child];
                [at_zero, at_zero + values[hi + child]]
            });
            quartic_summand(lines, equality[row])
        };
        let xor = |mut left: [T::Unreduced; 4], right: [T::Unreduced; 4]| {
            for coefficient in 0..4 {
                left[coefficient] ^= right[coefficient];
            }
            left
        };
        let rows = window_rows(full_pairs);
        let zero = [T::lift(F192::ZERO); 4];
        let window = |index: usize| -> [T::Unreduced; 4] {
            let base = index * rows;
            (base..(base + rows).min(full_pairs)).fold(zero, |sum, row| xor(sum, summand(row)))
        };
        let windows = full_pairs.div_ceil(rows);
        let mut message = if full_pairs >= PAR_THRESHOLD {
            parallel::map_reduce(windows, || zero, window, xor)
        } else {
            (0..windows).map(window).fold(zero, xor)
        };
        if !stored_rows.is_multiple_of(2) {
            let lo = 8 * full_pairs;
            let lines = [0, 1, 2, 3].map(|child| {
                let at_zero = values[lo + child];
                [at_zero, at_zero + T::ONE]
            });
            message = xor(message, quartic_summand(lines, equality[full_pairs]));
        }
        message.map(T::reduce)
    }

    fn fold(&mut self, challenge: F192) {
        let rows = (self.values.len() / 4).div_ceil(2);
        self.next.truncate(4 * rows);
        match &self.values {
            LayerValues::Base(values) => Self::fold_values(values, &mut self.next, challenge),
            LayerValues::Ext(values) => Self::fold_values(values, &mut self.next, challenge),
        }
        self.finish_fold();
    }

    fn fold_values<T: ProductValue>(values: &[T], next: &mut [F192], challenge: F192) {
        let stored_rows = values.len() / 4;
        let full_rows = stored_rows / 2;
        let fold_row = |row: usize| -> [F192; 4] {
            // One slice, not eight indexes: the bounds checks and the
            // index-by-24 multiplies fall out.
            let v = &values[8 * row..8 * row + 8];
            T::fold_quad(&v[..4], &v[4..], challenge)
        };
        // The next round is what reads the output, and a layer this size is long
        // evicted by then, so where an ordinary store fetches the line it
        // overwrites the pair is staged and published with streaming stores.
        // Where it does not, the stage buys nothing and costs a real call, the
        // `slot.len()` being one the compiler cannot fold away.
        #[cfg(target_arch = "x86_64")]
        let window = |base: usize, destination: &mut [F192]| {
            let stream = Stream::new();
            for (pair, slot) in destination.chunks_mut(8).enumerate() {
                let mut both = [F192::ZERO; 8];
                both[..4].copy_from_slice(&fold_row(base + 2 * pair));
                if slot.len() == 8 {
                    both[4..].copy_from_slice(&fold_row(base + 2 * pair + 1));
                }
                stream.copy(slot, &both[..slot.len()]);
            }
        };
        #[cfg(not(target_arch = "x86_64"))]
        let window = |base: usize, destination: &mut [F192]| {
            for (pair, slot) in destination.chunks_mut(8).enumerate() {
                slot[..4].copy_from_slice(&fold_row(base + 2 * pair));
                if slot.len() == 8 {
                    slot[4..].copy_from_slice(&fold_row(base + 2 * pair + 1));
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
            next[4 * full_rows..].copy_from_slice(&T::fold_quad(&values[lo..lo + 4], &[T::ONE; 4], challenge));
        }
    }

    fn fold_and_message(&mut self, challenge: F192, equality: &[F192]) -> [F192; 4] {
        let rows = (self.values.len() / 4).div_ceil(2);
        self.next.truncate(4 * rows);
        let message = match &self.values {
            LayerValues::Base(values) => Self::fold_and_message_values(values, &mut self.next, challenge, equality),
            LayerValues::Ext(values) => Self::fold_and_message_values(values, &mut self.next, challenge, equality),
        };
        self.finish_fold();
        message
    }

    fn fold_and_message_values<T: ProductValue>(
        values: &[T],
        next: &mut [F192],
        challenge: F192,
        equality: &[F192],
    ) -> [F192; 4] {
        let stored_rows = values.len() / 4;
        let rows = stored_rows.div_ceil(2);
        let dst = parallel::SendPtr(next.as_mut_ptr());
        const PAIRS: usize = 16;
        let pairs = rows.div_ceil(2);
        let identity = [T::ONE; 4];
        let task = |index: usize| {
            let first = index * PAIRS;
            let end = (first + PAIRS).min(pairs);
            let mut stage = [F192::ZERO; 8 * PAIRS];
            let end_row = (2 * end).min(rows);
            for row in 2 * first..end_row {
                let lo = 8 * row;
                let left = &values[lo..lo + 4];
                let right = values.get(lo + 4..lo + 8).unwrap_or(&identity);
                let offset = 4 * (row - 2 * first);
                stage[offset..offset + 4].copy_from_slice(&T::fold_quad(left, right, challenge));
            }
            let mut message = [F192Unreduced::ZERO; 4];
            for pair in first..end {
                let lo = 8 * (pair - first);
                let left = &stage[lo..lo + 4];
                let right = if 2 * pair + 1 < rows {
                    &stage[lo + 4..lo + 8]
                } else {
                    &[F192::ONE; 4]
                };
                let lines = std::array::from_fn(|i| [left[i], left[i] + right[i]]);
                let terms = quartic_summand(lines, equality[pair]);
                for i in 0..4 {
                    message[i] ^= terms[i];
                }
            }
            // The next round reads the destination; this round reads only the local stage.
            let stream = Stream::new();
            let len = 4 * (end_row - 2 * first);
            // SAFETY: tasks own disjoint initialized prefixes of the output, covering every row.
            unsafe { stream.copy(dst.slice(8 * first, len), &stage[..len]) };
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
        message.map(F192Unreduced::reduce)
    }

    fn finish_fold(&mut self) {
        let folded = std::mem::take(&mut self.next);
        self.next = match std::mem::replace(&mut self.values, LayerValues::Ext(folded)) {
            LayerValues::Ext(values) => values,
            LayerValues::Base(values) => {
                drop(values);
                // SAFETY: the next fold writes every slot before reading it.
                unsafe { ArenaVec::uninitialized(4 * (self.values.len() / 4).div_ceil(2)) }
            }
        };
        self.logical_rows /= 2;
    }

    fn children(&self) -> [F192; 4] {
        debug_assert_eq!(self.values.len(), 4);
        debug_assert_eq!(self.logical_rows, 1);
        std::array::from_fn(|i| self.values.at(i))
    }
}

/// The result of a batched grand-product proof: the three roots and leaf
/// evaluations, all reduced to one shared point. Under [`RootShape::FirstTwoShared`],
/// `roots[0] == roots[1]` by construction rather than by a check.
pub struct ProductTriple {
    pub roots: [F192; 3],
    pub point: Vec<F192>,
    pub values: [F192; 3],
}

/// How many of the three roots ride the stream, which is a property of the statement rather than
/// of the reduction below.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum RootShape {
    /// Three unrelated products: every root is sent.
    Distinct,
    /// The first two trees share a product by construction, as the bus's two sides do
    /// (`cpu::filler` fills every table to a power of two, so they balance outright). ONE root
    /// is then sent for both, and no verifier can be handed an unbalanced pair to check.
    FirstTwoShared,
}

/// Prove three identity-padded grand products as one RLC-batched radix-four GKR.
pub fn prove_product_triple(leaves: [ArenaVec<F192>; 3], ps: &mut ProverState, shape: RootShape) -> ProductTriple {
    prove_product_triple_mixed(leaves.map(LayerValues::Ext), ps, shape)
}

/// The count channel and its product-tree layers stay in K until a sumcheck fold.
pub(crate) fn prove_product_triple_with_base_count(
    leaves: [ArenaVec<F192>; 2],
    count: ArenaVec<F64>,
    ps: &mut ProverState,
    shape: RootShape,
) -> ProductTriple {
    let [push, pull] = leaves;
    prove_product_triple_mixed(
        [LayerValues::Ext(push), LayerValues::Ext(pull), LayerValues::Base(count)],
        ps,
        shape,
    )
}

fn prove_product_triple_mixed(leaves: [LayerValues; 3], ps: &mut ProverState, shape: RootShape) -> ProductTriple {
    let mu = crate::log2_ceil_usize(leaves[0].len());
    assert!(
        leaves.iter().all(|lane| lane.len() > 0 && lane.len() <= 1 << mu),
        "batched trees must be nonempty prefixes of the first tree's logical tree"
    );
    let mut layers = leaves.map(|lane| match lane {
        LayerValues::Ext(values) => build_layers(values, mu)
            .into_iter()
            .map(LayerValues::Ext)
            .collect::<Vec<_>>(),
        LayerValues::Base(values) => build_layers(values, mu).into_iter().map(LayerValues::Base).collect(),
    });
    let roots = [layers[0][mu].at(0), layers[1][mu].at(0), layers[2][mu].at(0)];
    match shape {
        RootShape::Distinct => {
            for root in roots {
                ps.add_scalar(root);
            }
        }
        RootShape::FirstTwoShared => {
            assert_eq!(roots[0], roots[1], "FirstTwoShared needs the two products to agree");
            ps.add_scalar(roots[0]);
            ps.add_scalar(roots[2]);
        }
    }
    let mut lambda = ps.sample();
    let mut point = Vec::new();
    let mut values = roots;

    let mut layer = mu;
    while layer > 0 {
        let round_count = mu - layer;
        if layer % 2 == 1 {
            debug_assert_eq!(round_count, 0, "only the root-most layer may be binary");
            let tails = [0, 1, 2].map(|tree| {
                let below = &layers[tree][layer - 1];
                match below.len() {
                    2 => [below.at(0), below.at(1)],
                    1 => [below.at(0), F192::ONE],
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
        let mut trees =
            [0, 1, 2].map(|tree| QuaternaryLayerState::new(std::mem::take(&mut layers[tree][layer - 2]), width));
        let mut equality = if round_count > 0 {
            eq_table(&point[1..])
        } else {
            Vec::new()
        };
        let mut round_point = Vec::with_capacity(round_count);
        let mut messages = if round_count > 0 {
            trees.each_ref().map(|tree| tree.round_message(&equality))
        } else {
            [[F192::ZERO; 4]; 3]
        };
        for round in 0..round_count {
            let mut coeffs = [0, 1, 2, 3].map(|coefficient| {
                messages[0][coefficient] + lambda * (messages[1][coefficient] + lambda * messages[2][coefficient])
            });
            // The kernel accumulates `q(0) + q(1)`, the wire carries `c1`. This is
            // `Transmitter::add_round_poly(_, true)` bar its dropped `c0`, which the
            // claim fixes and the prover therefore never forms.
            coeffs[0] = coeffs[0] + coeffs[1] + coeffs[2] + coeffs[3];
            ps.add_scalars(&coeffs);
            let challenge = ps.sample();
            round_point.push(challenge);
            shrink_eq_low(&mut equality);
            if round + 1 < round_count {
                messages = trees.each_mut().map(|tree| tree.fold_and_message(challenge, &equality));
            } else {
                // The last shrink exhausts `equality`, so the final round has no
                // table to weight a message by and needs the fold alone. Both
                // kernels stay for that reason; `fold` is not dead.
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

    ProductTriple { roots, point, values }
}

/// Verify the RLC-batched radix-four proof.
pub fn verify_product_triple(mu: usize, vs: &mut VerifierState, shape: RootShape) -> Result<ProductTriple, GkrError> {
    let mut root = || vs.next_scalar().map_err(|_| GkrError::Truncated);
    let roots = match shape {
        RootShape::Distinct => [root()?, root()?, root()?],
        // One root for both balancing trees, so their equality is structural: there is no
        // unbalanced pair a prover could state, and nothing for the caller to check.
        RootShape::FirstTwoShared => {
            let shared = root()?;
            [shared, shared, root()?]
        }
    };
    let mut lambda = vs.sample();
    let mut point = Vec::new();
    let mut values = roots;

    let mut layer = mu;
    while layer > 0 {
        let round_count = mu - layer;
        let mut claim = poly_eval(&values, lambda);
        if layer % 2 == 1 {
            debug_assert_eq!(round_count, 0, "only the root-most layer may be binary");
            let mut tails = [[F192::ZERO; 2]; 3];
            for value in tails.iter_mut().flatten() {
                *value = vs.next_scalar().map_err(|_| GkrError::Truncated)?;
            }
            let products = tails.map(|[left, right]| left * right);
            if claim != poly_eval(&products, lambda) {
                return Err(GkrError::LayerMismatch { layer });
            }
            let challenge = vs.sample();
            for (value, [left, right]) in values.iter_mut().zip(tails) {
                *value = interp(left, right, challenge);
            }
            lambda = vs.sample();
            point = vec![challenge];
            layer -= 1;
            continue;
        }

        let mut round_point = Vec::with_capacity(round_count);
        for &equality_point in point.iter().take(round_count) {
            let h = vs
                .next_round_poly(5, claim, Some(equality_point))
                .map_err(|_| GkrError::Truncated)?;
            let challenge = vs.sample();
            round_point.push(challenge);
            claim = poly_eval(&h, challenge);
        }
        let mut tails = [[F192::ZERO; 4]; 3];
        for value in tails.iter_mut().flatten() {
            *value = vs.next_scalar().map_err(|_| GkrError::Truncated)?;
        }
        let products = tails.map(|tail| tail[0] * tail[1] * tail[2] * tail[3]);
        if claim != poly_eval(&products, lambda) {
            return Err(GkrError::LayerMismatch { layer });
        }
        let low_challenge = vs.sample();
        let high_challenge = vs.sample();
        for (value, tail) in values.iter_mut().zip(tails) {
            *value = interp(
                interp(tail[0], tail[1], low_challenge),
                interp(tail[2], tail[3], low_challenge),
                high_challenge,
            );
        }
        lambda = vs.sample();
        point = vec![low_challenge, high_challenge];
        point.extend_from_slice(&round_point);
        layer -= 2;
    }

    Ok(ProductTriple { roots, point, values })
}

#[cfg(test)]
mod tests {
    use super::*;

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
            let below: ArenaVec<F192> = (0..4 * width)
                .map(|i| F192::new((17 * i + width + 1) as u64, (i * i + 3) as u64, (5 * i + 7) as u64))
                .collect();
            let state = QuaternaryLayerState::new(below, width);
            let equality: Vec<F192> = (0..width / 2)
                .map(|i| F192::new((31 * i + 5) as u64, (7 * i + 1) as u64, (11 * i + 9) as u64))
                .collect();
            let [difference, c2, c3, c4] = state.round_message(&equality);
            let direct = |point: F192| {
                (0..width / 2).fold(F192::ZERO, |sum, row| {
                    let values = [0, 1, 2, 3].map(|child| {
                        interp(
                            state.values.at(8 * row + child),
                            state.values.at(8 * row + 4 + child),
                            point,
                        )
                    });
                    sum + equality[row] * values[0] * values[1] * values[2] * values[3]
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
                let values: ArenaVec<F192> = (0..len)
                    .map(|i| F192::new((17 * i + 1) as u64, (i * i + 3) as u64, (5 * i + 7) as u64))
                    .collect();
                let mut reference = QuaternaryLayerState::new(ArenaVec::from_slice(&values), width);
                let mut fused = QuaternaryLayerState::new(values, width);
                let point: Vec<F192> = (0..width.ilog2() - 1)
                    .map(|i| F192::new(31 + u64::from(i), 7, 11))
                    .collect();
                let mut equality = eq_table(&point);
                while reference.logical_rows > 2 {
                    let challenge = F192::new(reference.logical_rows as u64, 13, 19);
                    reference.fold(challenge);
                    shrink_eq_low(&mut equality);
                    let message = fused.fold_and_message(challenge, &equality);
                    assert_eq!(message, reference.round_message(&equality), "width={width}, len={len}");
                    assert_eq!(fused.values.len(), reference.values.len());
                    for i in 0..fused.values.len() {
                        assert_eq!(fused.values.at(i), reference.values.at(i), "width={width}, len={len}");
                    }
                }
                reference.fold(F192::Y);
                fused.fold(F192::Y);
                assert_eq!(fused.children(), reference.children());
            }
        }
    }

    #[test]
    fn base_count_matches_full_extension_transcript() {
        let mut rng = primitives::test_rng::Rng::new(11427);
        for mu in 0..=15 {
            let len = 1 << mu;
            let leaves = rng.ext_vec(len);
            let count: Vec<_> = (0..len).map(|_| F64(rng.next_u64())).collect();
            for count_len in [1, len.div_ceil(2), (len / 2 + 3).min(len), len] {
                for shape in [RootShape::Distinct, RootShape::FirstTwoShared] {
                    let mut mixed = ProverState::from_label(b"base-count-gkr");
                    let actual = prove_product_triple_with_base_count(
                        [ArenaVec::from_slice(&leaves), ArenaVec::from_slice(&leaves)],
                        ArenaVec::from_slice(&count[..count_len]),
                        &mut mixed,
                        shape,
                    );
                    let mut extension = ProverState::from_label(b"base-count-gkr");
                    let expected = prove_product_triple(
                        [
                            ArenaVec::from_slice(&leaves),
                            ArenaVec::from_slice(&leaves),
                            count[..count_len].iter().copied().map(F192::from).collect(),
                        ],
                        &mut extension,
                        shape,
                    );
                    assert_eq!(actual.roots, expected.roots);
                    assert_eq!(actual.point, expected.point);
                    assert_eq!(actual.values, expected.values);
                    let proof = mixed.into_proof();
                    assert_eq!(
                        proof.stream,
                        extension.into_proof().stream,
                        "mu={mu}, count_len={count_len}"
                    );
                    let mut verifier = VerifierState::from_label(b"base-count-gkr", &proof);
                    let verified = verify_product_triple(mu, &mut verifier, shape).expect("base-count proof verifies");
                    assert_eq!(verified.values, actual.values);
                    verifier.finish().expect("base-count proof consumed");
                }
            }
        }
    }

    #[test]
    fn radix_four_roundtrip_at_even_and_odd_depths() {
        for mu in 0..=10 {
            let leaves: [Vec<F192>; 3] = [0, 1, 2].map(|lane| {
                (0..1usize << mu)
                    .map(|row| F192::new((1 + row + lane * 100_003) as u64, row as u64, lane as u64))
                    .collect()
            });
            let expected_roots = leaves
                .each_ref()
                .map(|lane| lane.iter().copied().fold(F192::ONE, |product, value| product * value));
            let mut ps = ProverState::from_label(b"radix-four-gkr-test");
            let proved = prove_product_triple(
                leaves.each_ref().map(|l| ArenaVec::from_slice(l.as_slice())),
                &mut ps,
                RootShape::Distinct,
            );
            assert_eq!(proved.roots, expected_roots);
            for lane in 0..3 {
                assert_eq!(proved.values[lane], mle_eval_e(&leaves[lane], &proved.point));
            }

            let proof = ps.into_proof();
            let mut vs = VerifierState::from_label(b"radix-four-gkr-test", &proof);
            let verified = verify_product_triple(mu, &mut vs, RootShape::Distinct).expect("GKR verifies");
            assert_eq!(verified.roots, proved.roots);
            assert_eq!(verified.point, proved.point);
            assert_eq!(verified.values, proved.values);
            vs.finish().expect("proof stream is consumed");
        }
    }

    #[test]
    fn implicit_identity_suffix_matches_dense_padding() {
        for mu in 3..=10 {
            let lengths = [(1usize << mu) - 3, (1usize << (mu - 1)) + 1, (1usize << (mu - 2)) + 3];
            let leaves: [Vec<F192>; 3] = std::array::from_fn(|lane| {
                (0..lengths[lane])
                    .map(|row| F192::new((3 + row + lane * 10_007) as u64, row as u64, lane as u64))
                    .collect()
            });
            let dense = leaves.each_ref().map(|lane| {
                let mut padded = lane.clone();
                padded.resize(1 << mu, F192::ONE);
                padded
            });
            let mut sparse_ps = ProverState::from_label(b"sparse-radix-four-gkr-test");
            let proved = prove_product_triple(
                leaves.each_ref().map(|l| ArenaVec::from_slice(l.as_slice())),
                &mut sparse_ps,
                RootShape::Distinct,
            );
            for lane in 0..3 {
                assert_eq!(proved.values[lane], mle_eval_e(&dense[lane], &proved.point));
                assert_eq!(
                    proved.roots[lane],
                    dense[lane]
                        .iter()
                        .copied()
                        .fold(F192::ONE, |product, value| product * value)
                );
            }
            let proof = sparse_ps.into_proof();
            let mut dense_ps = ProverState::from_label(b"sparse-radix-four-gkr-test");
            let dense_proved = prove_product_triple(
                dense.each_ref().map(|l| ArenaVec::from_slice(l.as_slice())),
                &mut dense_ps,
                RootShape::Distinct,
            );
            assert_eq!(dense_proved.roots, proved.roots);
            assert_eq!(dense_proved.point, proved.point);
            assert_eq!(dense_proved.values, proved.values);
            assert_eq!(dense_ps.into_proof().stream, proof.stream);
            let mut vs = VerifierState::from_label(b"sparse-radix-four-gkr-test", &proof);
            let verified = verify_product_triple(mu, &mut vs, RootShape::Distinct).expect("GKR verifies");
            assert_eq!(verified.roots, proved.roots);
            assert_eq!(verified.point, proved.point);
            assert_eq!(verified.values, proved.values);
            vs.finish().expect("proof stream is consumed");
        }
    }
}
