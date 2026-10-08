// CREDIT: https://github.com/succinctlabs/flock (flock-core), MIT OR Apache-2.0.
//
// The rectangular (f = 64, e = 192) generalization described in the ring-switching-generalized note.

//! Ring-switching reduction for the 64-bit transition: F_2 to K = GF(2^64)
//! packing, opened over E = GF(2^192) (the tower [`F192`]).
//!
//! With f = 64 (packing degree over F_2) and e = 192 (opening degree), this
//! converts one evaluation claim on
//! the bit-witness MLE at an E-point into a WHIR sumcheck claim on the
//! packed multilinear (one field element per 64 bits, least significant bit first) against a transparent E-valued weight vector
//! `rs_eq_ind`.
//!
//! ## Rectangular shape
//!
//! - `s_hat_v` has 64 entries (one per packing bit), each an E element; its
//!   tensor-algebra transpose `s_hat_u = (t_i)` has 192 K-entries. A random
//!   `F_2`-linear map batches all coordinates directly, without padding them
//!   to a 256-entry Boolean cube.
//! - **No "7 = 6 + 1" prefix split**: with 64-bit packing the packed prefix
//!   is exactly the 6-bit skip domain, so every coordinate outside it is an
//!   ordinary suffix coordinate of the packed witness (which has `2^(m-6)`
//!   words).
//! - **The 64 slices come in bound**: `s_hat_v[i] = sum_y eq(r_suffix, y) *
//!   bit_i(packed[y])`, the MLE of the i-th bit-slice at the suffix point, is
//!   supplied by the caller on both sides, which is where it was transmitted
//!   and checked (flock sends its family itself and pins it in its lincheck
//!   terminal). This module therefore reads nothing off the stream and only has
//!   to bind the slices to the commitment.
//!
//! ## Protocol (prover)
//!
//! 1. Take the caller's bound `s_hat_v`.
//! 2. Sample six challenges in E and compose the maps
//!    `v <- v + f_t v^(2^d_t)` for `d_t = 32, 16, 8, 4, 2, 1`. For the
//!    coordinate basis `(b_i)`, define `coord_weights[i] = Phi(b_i)`. The
//!    batched target is `sumcheck_claim = sum_i x^i Phi(s_hat_v[i])`, which is
//!    `sum_i Phi(b_i) * t_i` over the transpose `t_i = s_hat_u[i] in K`; both
//!    sides evaluate it in the map's Frobenius form ([`RingMap::target`]).
//! 3. Both sides define the transparent weights
//!    `rs_eq_ind[y] = Phi(eq(r_suffix, y))` where `Phi : E -> E` is the
//!    composed map above. Completeness:
//!    `sum_y rs_eq_ind[y] * packed[y] == sumcheck_claim`, which is exactly
//!    the claim shape [`super::whir::recursive_prover_with_basis`]
//!    proves (with `b_initial = rs_eq_ind`, `target = sumcheck_claim`).
//!    A nonzero discrepancy gives a nonzero polynomial in the six challenges;
//!    its total degree is below `2^32`, hence its failure probability is below
//!    `2^-160` before the WHIR list-size factor.
//!
//! ## Prover vs. verifier paths for `rs_eq_ind`
//!
//! - The stacked opening ring-switches one family per opening: its claims' slices combined by powers of one challenge `gamma_rs` before the map is drawn, each claim's scale sitting inside the map, so the claim at `r_suffix` with scale `c` has the weight `Phi(c·eq(r_suffix, y))` on its region (doc `leanvm` Annex A, `rs:family`).
//! - The prover keeps each claim's equality tensor factored, folds it through a
//!   small byte table, and combines the claims directly into one dense PCS
//!   weight. It never materializes a dense vector per claim.
//! - The verifier never materializes the vector: its MLE at the WHIR final point is the closed form of doc `leanvm` Annex A (`rs:weight`), with the Frobenius moved onto the point every claim shares (`rs:cost`), so a claim costs `64 L` E-multiplications and 63 squarings after one precomputation per opening, and claims at prefixes of one point share their products.

use fiat_shamir::arith::{Arith, Verifier};
use fiat_shamir::transcript::Challenger;
use primitives::bit_fold::{BLOCK, F192Map, Sliced};
use primitives::field::{F64, F192};
use primitives::multilinear::eq_table;
use std::cmp::Reverse;

/// Frobenius shifts in the order in which the two-term maps are composed.
/// Descending order bounds every challenge's exponent by `2^31`.
pub const COMPOSITION_SHIFTS: [usize; 6] = [32, 16, 8, 4, 2, 1];

/// The degree of `E = GF(2^192)` over `F_2`: the coordinates the map weighs.
const DEGREE_E: usize = 192;

/// The coordinate batching weights: `weights[w] = Phi(b_w)`, where `b_w` is the
/// `w`-th `F_2`-coordinate basis element of `E` (the order `transpose_s_hat`
/// produces). Starting from `v`, the map composes
///
/// ```text
/// v <- v + f_t · v^(2^shift_t),    shift_t = 32, 16, 8, 4, 2, 1.
/// ```
///
/// The result is `F_2`-linear, so
/// `sum_w weights[w]·t_w = sum_j x^j·Phi(y_j)` for the row
/// view `y` and the column view `t` of the same tensor-algebra element. That
/// identity is what lets a verifier evaluate the batched claim from `Phi`'s
/// six challenges instead of the 192 weights. Expanding the composition puts a distinct monomial at every Frobenius
/// exponent `0..64`: writing `k = sum_p k_p·2^(5-p)` for the binary digits of
/// `k`, the coefficient is `C_k = prod_{p : k_p = 1} f_p^(2^(k mod 2^(5-p)))`,
/// which is what `python-verifier`'s coefficient table builds. Applying the composed
/// form directly costs only 63 squarings and six multiplications.
///
/// ## Soundness
///
/// Let `delta != 0` be the prover's error on the transposed columns, fixed
/// before the six challenges (`s_hat_v` is bound first). The check misses it iff
/// `sum_w Phi(b_w)·delta_w = sum_{k<64} C_k(f)·V_k = 0` with
/// `V_k = sum_w b_w^(2^k)·delta_w`. Writing `w = 64j + i` and `b_w = x^i·Y^j`,
///
/// ```text
/// V_k = sum_{j<3} (Y^(2^k))^j · R_{j,k},   R_{j,k} = sum_{i<64} x^(i·2^k)·delta_{64j+i} in K.
/// ```
///
/// `Y^(2^k)` is not in `K` (squaring is a bijection of `K`, so `Y^(2^k) in K`
/// would force `Y in K` and `E = K[Y] = K`), and `[E:K] = 3` is prime, so
/// `{1, Y^(2^k), Y^(2·2^k)}` is a `K`-basis: `V_k = 0` forces every
/// `R_{j,k} = 0`. At fixed `j` those 64 equations say that the polynomial
/// `D_j(U) = sum_{i<64} delta_{64j+i}·U^i`, of degree at most 63, vanishes at
/// `x, x^2, x^4, ..., x^(2^63)`. Those are 64 distinct points, since `x` has
/// degree 64 over `F_2`, so `D_j = 0` and `delta = 0`. Hence some `V_k != 0`.
/// The 64 `C_k` are distinct monomials, so the discrepancy is a nonzero
/// polynomial in the challenges. In descending shift order its total degree is
/// `2^31 + 2^15 + 2^7 + 2^3 + 2 + 1`, below `2^32`.
///
/// The 64 terms are also the floor: the weights must separate any nonzero
/// error on the 192 transposed `K`-columns, which is `|S|` `E`-equations, i.e.
/// `3·|S|` `K`-equations, in `192` `K`-unknowns, and with `3·|S| < 192` a
/// nonzero error lies in the kernel for EVERY coefficient choice and passes
/// with probability one.
pub(crate) fn build_coordinate_weights(challenges: &[F192; COMPOSITION_SHIFTS.len()]) -> Vec<F192> {
    // b_w has only bit w set: bits 0..64 are K's power basis, and bits 64/128
    // shift it by Y / Y^2.
    let basis = |w: usize| match w / F64::DEGREE {
        0 => F192::new(1u64 << (w % F64::DEGREE), 0, 0),
        1 => F192::new(0, 1u64 << (w % F64::DEGREE), 0),
        _ => F192::new(0, 0, 1u64 << (w % F64::DEGREE)),
    };
    (0..DEGREE_E)
        .map(|w| apply_composed_map(basis(w), challenges))
        .collect()
}

/// Applies the composed map `Phi` of [`build_coordinate_weights`] to one value.
fn apply_composed_map(mut value: F192, challenges: &[F192; COMPOSITION_SHIFTS.len()]) -> F192 {
    for (&challenge, &shift) in challenges.iter().zip(COMPOSITION_SHIFTS.iter()) {
        let mut frobenius = value;
        for _ in 0..shift {
            frobenius = frobenius.square();
        }
        value += challenge * frobenius;
    }
    value
}

/// Sample the composed map's challenges after every ring-switch message has
/// been bound.
pub(crate) fn sample_map_challenges(ch: &mut impl Challenger) -> [F192; COMPOSITION_SHIFTS.len()] {
    std::array::from_fn(|_| ch.sample())
}

/// A claim's weight `Phi(scale·eq(point, ·))`, kept factored: the split eq
/// tensor, its high half scaled, and `Phi` on the coordinates, so combining
/// claims needs only additions.
pub(crate) struct DeferredWeight {
    eq_lo: Vec<F192>,
    eq_hi: Vec<F192>,
    map: F192Map,
    /// With a low table of whole blocks: those blocks in the map's layout, and `map` after each high entry's product.
    ///
    /// Entry `lo + |eq_lo| hi` is then `Phi(eq_hi[hi] · ·)` of `eq_lo[lo]`, with no product and no input transpose.
    sliced: Option<(Vec<Sliced>, Vec<F192Map>)>,
}

/// High variables of a sliced weight: each costs one composed map, worth it only over long low runs.
fn sliced_hi_bits(n: usize) -> usize {
    n.saturating_sub(14).min(8)
}

/// The weight `Phi(scale·eq(point, ·))` of a claim, without materializing it.
///
/// Composed maps dispatch across the pool; call this outside a parallel dispatch.
pub(crate) fn deferred_weight(point: &[F192], scale: F192, coordinate_weights: &[F192]) -> DeferredWeight {
    let n = point.len();
    let n_lo = if n >= 6 { n - sliced_hi_bits(n) } else { split_n_lo(n) };
    let span = tracing::info_span!(
        "Deferred weight setup",
        variables = n,
        low_elements = 1usize << n_lo,
        high_elements = 1usize << (n - n_lo),
        sliced = n_lo >= 6,
        portable_map = primitives::bit_fold::PORTABLE,
        eq_bytes = ((1usize << n_lo) + (1usize << (n - n_lo))) * size_of::<F192>(),
        sliced_bytes = if n_lo >= 6 { (1usize << n_lo) / BLOCK * size_of::<Sliced>() } else { 0 },
    ).entered();
    let eq_span = tracing::info_span!("Deferred eq tables").entered();
    let (eq_lo, mut eq_hi) = (eq_table(&point[..n_lo]), eq_table(&point[n_lo..]));
    for e in &mut eq_hi {
        *e *= scale;
    }
    drop(eq_span);
    let map_span = tracing::info_span!("Phi map construction").entered();
    let map = F192Map::new(coordinate_weights);
    drop(map_span);
    let sliced = (n_lo >= 6).then(|| {
        let slice_span = tracing::info_span!("Phi input slicing").entered();
        let blocks = eq_lo.as_chunks::<BLOCK>().0.iter().map(Sliced::new).collect();
        drop(slice_span);
        let composed_span = tracing::info_span!("Phi composed maps", maps = eq_hi.len()).entered();
        let maps = parallel::map_collect(eq_hi.len(), |hi| map.after_mul(eq_hi[hi]));
        drop(composed_span);
        (blocks, maps)
    });
    drop(span);
    DeferredWeight {
        eq_lo,
        eq_hi,
        map,
        sliced,
    }
}

/// Fold several deferred weights into `out[start..]` of their combined dense
/// basis, accumulating, so `out` arrives zeroed. No per-claim dense vector is
/// allocated or read back. `start` is an offset into the basis, which lets a
/// caller cover it one cache-resident window at a time.
pub(crate) fn combine_deferred_chunk(outputs: &[DeferredWeight], start: usize, out: &mut [F192]) {
    let mut eq = [F192::ZERO; BLOCK];
    for claim in outputs {
        let block_len = claim.eq_lo.len();
        assert!(start + out.len() <= block_len * claim.eq_hi.len());
        for (b, out) in out.chunks_mut(BLOCK).enumerate() {
            let first = start + b * BLOCK;
            match &claim.sliced {
                Some((blocks, maps)) if first.is_multiple_of(BLOCK) => {
                    maps[first / block_len].apply_sliced_add(&blocks[first % block_len / BLOCK], out);
                }
                _ => {
                    for (i, e) in eq[..out.len()].iter_mut().enumerate() {
                        let index = first + i;
                        *e = claim.eq_lo[index % block_len] * claim.eq_hi[index / block_len];
                    }
                    claim.map.apply_add(&eq, out);
                }
            }
        }
    }
}

/// Split point for the factored eq build: low half sized ~n/2 (min 4, the
/// point where two factor tables beat one full build).
fn split_n_lo(n: usize) -> usize {
    (n / 2).clamp(4.min(n), n)
}

/// The ring-switching map `Phi`, as the coefficients `C_k^(2^-k)` of its Frobenius form `Phi(v) = sum_{k<64} C_k v^(2^k)`.
///
/// Its elements are values, or whatever a verifier holds them as.
pub struct RingMap<E> {
    coefficients: Vec<E>,
}

impl<E: Copy> RingMap<E> {
    /// The map drawn from its six challenges.
    ///
    /// `C_k^(2^-k) = prod_{p : k & d_p} f_p^(2^-(k - k mod d_p))`, and `k - k mod d_p` is the part of `k` at the shifts down to `d_p`.
    /// So the products grow one shift at a time, each prefix `k` extended by `d_p` or not.
    pub fn new<A: Arith<E = E>>(a: &mut A, challenges: &[E]) -> Self {
        let mut prefixes = vec![(0usize, a.one())];
        for (&f, &shift) in challenges.iter().zip(&COMPOSITION_SHIFTS) {
            let ladder = inverse_frobenius_ladder(a, f, shift);
            let extended: Vec<(usize, E)> = prefixes
                .iter()
                .map(|&(k, c)| (k + shift, a.mul(c, ladder[k + shift])))
                .collect();
            prefixes.extend(extended);
        }
        let mut coefficients = vec![a.one(); F64::DEGREE];
        for (k, c) in prefixes {
            coefficients[k] = c;
        }
        Self { coefficients }
    }

    /// `sum_i x^i Phi(s_i)` for the family's slices `s`: `sum_k (C_k^(2^-k) S(x^(2^-k)))^(2^k)` with `S(u) = sum_i s_i u^i`.
    ///
    /// # Panics
    ///
    /// If there are not 64 slices.
    pub fn target<A: Arith<E = E>>(&self, a: &mut A, slices: &[E]) -> E {
        assert_eq!(slices.len(), F64::DEGREE, "a family has 64 slices");
        let terms: Vec<E> = (0..F64::DEGREE)
            .map(|k| {
                // `x^(2^-k) = x^(2^(64 - k))` in `K`.
                let xk = (0..(F64::DEGREE - k) % F64::DEGREE).fold(F64(2), |x, _| x.square());
                let (&last, rest) = slices.split_last().expect("64 slices");
                let s = (rest.iter().rev()).fold(last, |acc, &sj| a.mul_const_add(acc, F192::from(xk), sj));
                a.mul(self.coefficients[k], s)
            })
            .collect();
        Self::close(a, &terms)
    }

    /// The terms `C_k^(2^-k) P_k` of a claim's weight at several prefixes of one suffix point `z`, `P_k = prod_n (1 + z_n + q_n^(2^-k))`: entry `i` is at `z[..lengths[i]]`.
    ///
    /// Doc `leanvm` Annex A (`rs:weight`) gives `MLE(Phi(eq(z, ·)))(q) = sum_k (C_k^(2^-k) P_k)^(2^k)`: every Frobenius power falls on the query.
    /// `ladders[n]` holds the query's `q_n^(2^-k)`.
    /// The products of a prefix extend to the next coordinate by one product each, so one pass over the longest serves every length.
    ///
    /// # Panics
    ///
    /// If a length exceeds the point or the query.
    pub fn prefix_terms<A: Arith<E = E>>(
        &self,
        a: &mut A,
        z: &[E],
        ladders: &[Vec<E>],
        lengths: &[usize],
    ) -> Vec<Vec<E>> {
        let longest = lengths.iter().copied().max().unwrap_or(0);
        assert!(
            longest <= z.len() && longest <= ladders.len(),
            "a claim's point is a prefix of the query"
        );
        let mut out = vec![Vec::new(); lengths.len()];
        let take = |n: usize, terms: &[E], out: &mut [Vec<E>]| {
            for (slot, _) in out.iter_mut().zip(lengths).filter(|&(_, &len)| len == n) {
                *slot = terms.to_vec();
            }
        };
        let mut terms = self.coefficients.clone();
        take(0, &terms, &mut out);
        for (n, (&zn, ladder)) in z.iter().zip(ladders).take(longest).enumerate() {
            for (term, &power) in terms.iter_mut().zip(ladder) {
                let s = a.add(power, zn);
                *term = a.times_one_plus(*term, s);
            }
            take(n + 1, &terms, &mut out);
        }
        out
    }

    /// `sum_k term_k^(2^k)`, by the linearized Horner rule `acc <- acc^2 + term` from the last term down.
    ///
    /// The Frobenius is additive, so the terms of several claims add before one close.
    pub fn close<A: Arith<E = E>>(a: &mut A, terms: &[E]) -> E {
        let (&last, rest) = terms.split_last().expect("the map has 64 terms");
        rest.iter().rev().fold(last, |acc, &term| a.mul_add(acc, acc, term))
    }
}

/// `v^(2^-j)` at each index `j >= lowest` of 64, and `v` below.
///
/// Squaring from `v^(2^128) = v^(2^-64)`, two Frobenius maps, climbs to `v^(2^-lowest)`.
pub fn inverse_frobenius_ladder<A: Arith>(a: &mut A, v: A::E, lowest: usize) -> Vec<A::E> {
    let mut ladder = vec![v; F64::DEGREE];
    let lowest = lowest.max(1);
    let mut power = a.frobenius2(v);
    for slot in ladder[lowest..].iter_mut().rev() {
        power = a.square(power);
        *slot = power;
    }
    ladder
}

/// One ring-switched claim on a packed region: its 64 bit-slice values at a suffix point.
///
/// - The suffix point has one coordinate per variable of the region.
/// - Slice `i` is the multilinear extension of the words' bit `i` at that point.
/// - The caller sends and checks the slices itself, so the opening only binds them to the commitment.
///
/// Its elements are values, or whatever a verifier holds them as.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SliceClaim<E = F192> {
    /// The point, one coordinate per variable of the region.
    pub suffix_point: Vec<E>,
    /// The 64 slice values at the point.
    pub s_hat_v: Vec<E>,
}

impl<E: Copy> SliceClaim<E> {
    /// A claim whose slices past the given ones are zero.
    ///
    /// # Panics
    ///
    /// If more than 64 slices are given.
    pub fn zero_padded(suffix_point: Vec<E>, slices: impl IntoIterator<Item = E>, zero: E) -> Self {
        let mut s_hat_v: Vec<E> = slices.into_iter().collect();
        assert!(s_hat_v.len() <= F64::DEGREE, "a claim has at most 64 slices");
        s_hat_v.resize(F64::DEGREE, zero);
        Self { suffix_point, s_hat_v }
    }
}

/// A ring-switched region of the committed stack and the slice claims on it.
///
/// Prover and verifier describe a region with the same data.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RingSwitch<E = F192> {
    /// The region's first word, a multiple of its length.
    pub offset: usize,
    /// The base-two logarithm of the region's length in words.
    pub qflock_vars: usize,
    /// The claims on the region.
    pub claims: Vec<SliceClaim<E>>,
}

/// The ring switch's one family per opening: claim `j` scaled by `gamma_rs^j`, then one map `Phi` for all.
///
/// Both sides draw `gamma_rs` once every claim's slices are bound, then the map's six challenges.
///
/// Its challenges are values, or whatever a verifier holds them as.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct RingFamily<E = F192> {
    gamma_rs: E,
    map_challenges: [E; COMPOSITION_SHIFTS.len()],
}

impl RingFamily {
    /// Draw the family's challenges on the prover's side: `gamma_rs`, then the map's.
    pub fn sample(ch: &mut impl Challenger) -> Self {
        let gamma_rs = ch.sample();
        Self {
            gamma_rs,
            map_challenges: sample_map_challenges(ch),
        }
    }

    /// The challenge `gamma_rs` whose powers scale the claims.
    pub const fn gamma_rs(&self) -> F192 {
        self.gamma_rs
    }

    /// The map's weight on each of the 192 coordinates.
    pub(crate) fn coordinate_weights(&self) -> Vec<F192> {
        build_coordinate_weights(&self.map_challenges)
    }
}

impl<E: Copy> RingFamily<E> {
    /// Draw the family's challenges on the verifier's side, as the prover does.
    pub fn draw<V: Verifier<E = E>>(v: &mut V) -> Self {
        let gamma_rs = v.sample();
        let map = v.sample_vec(COMPOSITION_SHIFTS.len());
        Self {
            gamma_rs,
            map_challenges: std::array::from_fn(|i| map[i]),
        }
    }

    /// The family of the regions' claims in order, each scaled, under the map.
    pub fn share<'a, A: Arith<E = E>>(&self, a: &mut A, rings: &'a [RingSwitch<E>]) -> RingShare<'a, E> {
        let n_claims = rings.iter().map(|ring| ring.claims.len()).sum();
        let scales = a.powers(self.gamma_rs, n_claims);
        let map = RingMap::new(a, &self.map_challenges);
        RingShare { rings, scales, map }
    }
}

/// Every ring-switched claim of an opening as one family, claim `j` scaled by `gamma_rs^j`, under one map: its target, and its weight at a point.
pub struct RingShare<'a, E> {
    rings: &'a [RingSwitch<E>],
    scales: Vec<E>,
    map: RingMap<E>,
}

impl<E: Copy + PartialEq> RingShare<'_, E> {
    /// The family's target: the map applied once to the slices `sum_j gamma_rs^j s_{j,i}`.
    ///
    /// # Panics
    ///
    /// If a claim does not carry 64 slices.
    pub fn target<A: Arith<E = E>>(&self, a: &mut A) -> E {
        let claims = self.rings.iter().flat_map(|ring| &ring.claims);
        let zero = a.zero();
        let mut family = vec![zero; F64::DEGREE];
        for (claim, &scale) in claims.zip(&self.scales) {
            assert_eq!(claim.s_hat_v.len(), F64::DEGREE, "a ring-switched claim has 64 slices");
            for (f, &s) in family.iter_mut().zip(&claim.s_hat_v) {
                *f = a.mul_add(scale, s, *f);
            }
        }
        self.map.target(a, &family)
    }

    /// The family's weight at a point `x` of the stack cube: `sum_j eq(sel_j, x_hi) MLE(Phi(gamma_rs^j eq(r_j, .)))(x_lo)`.
    ///
    /// Claim `j` is the `j`-th claim across the regions in order, `sel_j` its region's selector bits.
    ///
    /// - The Frobenius moves onto `x`, so one ladder per coordinate serves every claim.
    /// - Claims whose points are prefixes of one another share one pass over the longest.
    /// - The claims of one region add their scaled terms and close once, the Frobenius being additive.
    ///
    /// # Panics
    ///
    /// If a region or a claim's point is longer than `x`.
    pub fn weight_at<A: Arith<E = E>>(&self, a: &mut A, x: &[E]) -> E {
        let max_vars = self.rings.iter().map(|ring| ring.qflock_vars).max().unwrap_or(0);
        let ladders: Vec<Vec<E>> = x[..max_vars]
            .iter()
            .map(|&q| inverse_frobenius_ladder(a, q, 1))
            .collect();
        let zero = a.zero();
        let mut sums = vec![vec![zero; F64::DEGREE]; self.rings.len()];
        for group in PrefixGroup::of(self.rings) {
            let at = self.map.prefix_terms(a, group.lead, &ladders, &group.lengths);
            for member in group.members {
                let scale = self.scales[member.claim];
                for (s, &term) in sums[member.ring].iter_mut().zip(&at[member.length]) {
                    *s = a.mul_add(scale, term, *s);
                }
            }
        }
        let mut weight = zero;
        for (ring, sum) in self.rings.iter().zip(&sums) {
            let part = RingMap::close(a, sum);
            let sel_eq = a.eq_bits(ring.offset >> ring.qflock_vars, &x[ring.qflock_vars..]);
            weight = a.mul_add(sel_eq, part, weight);
        }
        weight
    }
}

/// Ring claims whose suffix points are all prefixes of the longest, `lead`.
///
/// Its elements are values, or whatever a verifier holds them as: two points are prefixes of one another when their elements are equal.
#[derive(Clone, Debug)]
pub struct PrefixGroup<'a, E = F192> {
    /// The longest point.
    pub lead: &'a [E],
    /// The distinct prefix lengths its claims sit at.
    pub lengths: Vec<usize>,
    /// Its claims.
    pub members: Vec<PrefixMember>,
}

/// One claim of a prefix group.
#[derive(Clone, Copy, Debug)]
pub struct PrefixMember {
    /// Its index across every ring, which picks its scale.
    pub claim: usize,
    /// Its ring.
    pub ring: usize,
    /// Its entry in the group's lengths.
    pub length: usize,
}

impl<'a, E: PartialEq> PrefixGroup<'a, E> {
    /// Every ring claim in a group whose lead point it is a prefix of, longest points first.
    pub fn of(rings: &'a [RingSwitch<E>]) -> Vec<Self> {
        let mut claims: Vec<(usize, usize, &'a [E])> = rings
            .iter()
            .enumerate()
            .flat_map(|(r, ring)| ring.claims.iter().map(move |claim| (r, claim.suffix_point.as_slice())))
            .enumerate()
            .map(|(i, (r, point))| (i, r, point))
            .collect();
        claims.sort_by_key(|&(_, _, point)| Reverse(point.len()));
        let mut groups: Vec<Self> = Vec::new();
        for (claim, ring, point) in claims {
            let g = groups
                .iter()
                .position(|g| g.lead.starts_with(point))
                .unwrap_or_else(|| {
                    groups.push(Self {
                        lead: point,
                        lengths: Vec::new(),
                        members: Vec::new(),
                    });
                    groups.len() - 1
                });
            let group = &mut groups[g];
            let length = group.lengths.iter().position(|&n| n == point.len()).unwrap_or_else(|| {
                group.lengths.push(point.len());
                group.lengths.len() - 1
            });
            group.members.push(PrefixMember { claim, ring, length });
        }
        groups
    }
}

#[cfg(test)]
pub(crate) mod tests {
    use super::*;
    use crate::merkle::Hash;
    use crate::tensor_algebra::transpose_s_hat;
    use crate::whir::config::tests::test_config_for;
    use crate::whir::{
        VerifierConfig, commit, inner_product_base_ext, recursive_prover_with_basis,
        recursive_verifier_with_basis_succinct,
    };
    use fiat_shamir::arith::Native;
    use fiat_shamir::transcript::{ProofTranscript, ProverState, VerifierState};
    use primitives::field::F64;
    use primitives::test_util::Rng;
    use std::collections::HashSet;

    /// Total degree of the six-challenge composed batching map. This is the
    /// conservative degree used by the WHIR list-size soundness accounting.
    pub(crate) const RING_SWITCH_SOUNDNESS_DEGREE: usize =
        (1usize << 31) + (1usize << 15) + (1usize << 7) + (1usize << 3) + (1usize << 1) + 1;

    /// Standard inner product `sum_i a[i] * b[i]` over E.
    fn inner_product_ext(a: &[F192], b: &[F192]) -> F192 {
        assert_eq!(a.len(), b.len());
        let mut acc = F192::ZERO;
        for (&x, &y) in a.iter().zip(b.iter()) {
            acc += x * y;
        }
        acc
    }

    /// Compute `rs_eq_ind`, the transparent E-valued weight vector over the
    /// suffix domain: `rs_eq_ind[y] = Phi(suffix_tensor[y])` where `Phi` sends
    /// E-basis bit w to `coordinate_weights[w]`, i.e.
    ///
    /// `rs_eq_ind[y] = sum_w bit_w(suffix_tensor[y]) * coordinate_weights[w]`
    ///
    /// Naive reference: a per-position bit-scan over the three 64-bit limbs.
    /// See [`fold_ext_elems`] for the bytewise-table production version.
    fn fold_ext_elems_naive(suffix_tensor: &[F192], coordinate_weights: &[F192]) -> Vec<F192> {
        assert_eq!(coordinate_weights.len(), DEGREE_E);
        parallel::map_collect(suffix_tensor.len(), |i| {
            let elem = suffix_tensor[i];
            let mut acc = F192::ZERO;
            let mut c0 = elem.c0;
            while c0 != 0 {
                let w = c0.trailing_zeros() as usize;
                acc += coordinate_weights[w];
                c0 &= c0 - 1;
            }
            let mut c1 = elem.c1;
            while c1 != 0 {
                let w = c1.trailing_zeros() as usize;
                acc += coordinate_weights[64 | w];
                c1 &= c1 - 1;
            }
            let mut c2 = elem.c2;
            while c2 != 0 {
                let w = c2.trailing_zeros() as usize;
                acc += coordinate_weights[128 | w];
                c2 &= c2 - 1;
            }
            acc
        })
    }

    // The query's inverse Frobenius ladders, one per coordinate.
    fn ladders(query: &[F192]) -> Vec<Vec<F192>> {
        query
            .iter()
            .map(|&q| inverse_frobenius_ladder(&mut Native, q, 1))
            .collect()
    }

    // One claim's weight at the query's prefix of its length.
    fn eval_rs_eq(z_vals: &[F192], scale: F192, map: &RingMap<F192>, query: &[F192]) -> F192 {
        let terms = map.prefix_terms(&mut Native, z_vals, &ladders(query), &[z_vals.len()]);
        let scaled: Vec<F192> = terms[0].iter().map(|&term| term * scale).collect();
        RingMap::close(&mut Native, &scaled)
    }

    // The family's target in its column view, `sum_w Phi(b_w) t_w` over the transposed slices.
    fn column_target(s_hat_v: &[F192], coordinate_weights: &[F192]) -> F192 {
        inner_product_base_ext(&transpose_s_hat(s_hat_v), coordinate_weights)
    }

    /// Pack bit `64 * y + i` of `bits` into bit `i` of word `y`.
    fn pack_witness(bits: &[bool]) -> Vec<F64> {
        let word = |c: &[bool]| c.iter().rev().fold(0, |acc, &b| acc << 1 | b as u64);
        bits.chunks(F64::DEGREE).map(|c| F64(word(c))).collect()
    }

    #[test]
    fn a_family_at_unrelated_points_is_one_ring_switch() {
        let mut rng = Rng::new(0xdec0_de01_2345_6789);
        let n = 9;
        let packed = pack_witness(&rng.bits(1 << (n + F64::DEGREE.ilog2() as usize)));
        let challenges = std::array::from_fn(|_| rng.ext());
        let coordinate_weights = build_coordinate_weights(&challenges);
        let gamma_rs = rng.ext();
        let points: Vec<Vec<F192>> = (0..3).map(|_| rng.ext_vec(n)).collect();

        let mut slices = vec![F192::ZERO; F64::DEGREE];
        let mut dense = vec![F192::ZERO; packed.len()];
        let mut weights = Vec::new();
        let mut scale = F192::ONE;
        for point in &points {
            for (slot, s) in slices.iter_mut().zip(s_hat_v_reference(&packed, point)) {
                *slot += scale * s;
            }
            let scaled: Vec<F192> = eq_table(point).iter().map(|&e| scale * e).collect();
            for (slot, w) in dense.iter_mut().zip(fold_dense(&scaled, &coordinate_weights)) {
                *slot += w;
            }
            weights.push(deferred_weight(point, scale, &coordinate_weights));
            scale *= gamma_rs;
        }
        let mut combined = vec![F192::ZERO; packed.len()];
        combine_deferred_chunk(&weights, 0, &mut combined);
        assert_eq!(combined, dense);
        let target = inner_product_base_ext(&packed, &combined);
        assert_eq!(target, column_target(&slices, &coordinate_weights));
        assert_eq!(
            target,
            RingMap::new(&mut Native, &challenges).target(&mut Native, &slices)
        );
    }

    /// The contract between the native opener and every verifier that batches
    /// from `Phi`'s coefficients (the Python reference verifier): weighting the COLUMN view by `build_coordinate_weights` must
    /// equal applying `Phi` to the ROW view and combining with `x^j`. If this
    /// drifts, that verifier computes a different opening target than the prover.
    #[test]
    fn column_weights_match_the_row_side_linearized_map() {
        let mut rng = Rng::new(0xF00D_BEEF_1234_5678);
        for _ in 0..4 {
            let challenges = std::array::from_fn(|_| rng.ext());
            let s_hat_v = rng.ext_vec(F64::DEGREE);

            // Column side: sum_w weights[w] * t_w over the transposed K columns.
            let columns = transpose_s_hat(&s_hat_v);
            let lhs = inner_product_base_ext(&columns, &build_coordinate_weights(&challenges));

            // Row side: sum_j x^j * Phi(y_j).
            let x = F192::new(2, 0, 0);
            let mut rhs = F192::ZERO;
            let mut x_pow = F192::ONE;
            for y in &s_hat_v {
                let phi = apply_composed_map(*y, &challenges);
                rhs += x_pow * phi;
                x_pow *= x;
            }
            assert_eq!(lhs, rhs, "column weights and row-side Phi disagree");
        }
    }

    /// Expanding the composition must populate every Frobenius exponent exactly
    /// once. Distinct support monomials are the property used by soundness;
    /// pointwise distinct coordinate weights are neither required nor generally
    /// true for every challenge tuple.
    #[test]
    fn composed_map_has_full_frobenius_support() {
        let mut monomials = [None; F64::DEGREE];
        monomials[0] = Some([0u64; COMPOSITION_SHIFTS.len()]);
        for (stage, &shift) in COMPOSITION_SHIFTS.iter().enumerate() {
            let previous = monomials;
            for (i, exponents) in previous.into_iter().enumerate().take(F64::DEGREE - shift) {
                if let Some(mut exponents) = exponents {
                    for exponent in &mut exponents {
                        *exponent <<= shift;
                    }
                    exponents[stage] += 1;
                    assert!(monomials[i + shift].replace(exponents).is_none());
                }
            }
        }
        let monomials: HashSet<_> = monomials.into_iter().map(Option::unwrap).collect();
        assert_eq!(monomials.len(), F64::DEGREE);
        assert_eq!(
            monomials.iter().map(|exponents| exponents.iter().sum::<u64>()).max(),
            Some(RING_SWITCH_SOUNDNESS_DEGREE as u64)
        );

        let mut rng = Rng::new(0x1234_5678_9abc_def0);
        let challenges: [F192; COMPOSITION_SHIFTS.len()] = std::array::from_fn(|_| rng.ext());
        let mut coefficients = [F192::ZERO; F64::DEGREE];
        coefficients[0] = F192::ONE;
        for (&challenge, &shift) in challenges.iter().zip(COMPOSITION_SHIFTS.iter()) {
            let previous = coefficients;
            for (i, mut coefficient) in previous.into_iter().enumerate().take(F64::DEGREE - shift) {
                if coefficient == F192::ZERO {
                    continue;
                }
                for _ in 0..shift {
                    coefficient = coefficient.square();
                }
                coefficients[i + shift] = challenge * coefficient;
            }
        }
        assert!(coefficients.iter().all(|coefficient| *coefficient != F192::ZERO));

        let value = rng.ext();
        let mut expanded = F192::ZERO;
        let mut frobenius = value;
        for coefficient in coefficients {
            expanded += coefficient * frobenius;
            frobenius = frobenius.square();
        }
        assert_eq!(apply_composed_map(value, &challenges), expanded);
    }

    /// `Phi` of a dense tensor: the kernel `combine_deferred_chunk` runs per
    /// block, without its factored-eq slot generation.
    fn fold_dense(tensor: &[F192], coordinate_weights: &[F192]) -> Vec<F192> {
        let map = F192Map::new(coordinate_weights);
        let mut out = vec![F192::ZERO; tensor.len()];
        for (xs, out) in tensor.chunks(BLOCK).zip(out.chunks_mut(BLOCK)) {
            let mut block = [F192::ZERO; BLOCK];
            block[..xs.len()].copy_from_slice(xs);
            map.apply_add(&block, out);
        }
        out
    }

    /// Reference s_hat_v: brute-force partial evaluation of each bit-column
    /// MLE at the suffix point (direct bit-extract loop, no fold kernel).
    pub(crate) fn s_hat_v_reference(packed: &[F64], suffix_point: &[F192]) -> Vec<F192> {
        let eq_suffix = eq_table(suffix_point);
        (0..F64::DEGREE)
            .map(|i| {
                let mut acc = F192::ZERO;
                for (word, &w) in packed.iter().zip(eq_suffix.iter()) {
                    if (word.0 >> i) & 1 == 1 {
                        acc += w;
                    }
                }
                acc
            })
            .collect()
    }

    /// The prefix x suffix split factors the bit-MLE.
    #[test]
    fn slices_factor_the_bit_mle() {
        let m = 10;
        let mut rng = Rng::new(2);
        let bits = rng.bits(1usize << m);
        let packed = pack_witness(&bits);
        let point = rng.ext_vec(m);
        let prefix_weights = eq_table(&point[..F64::DEGREE.ilog2() as usize]);
        let suffix_point = &point[F64::DEGREE.ilog2() as usize..];

        let s_ref = s_hat_v_reference(&packed, suffix_point);
        let eq_full = eq_table(&point);
        let mut direct = F192::ZERO;
        for (x, &w) in eq_full.iter().enumerate() {
            if bits[x] {
                direct += w;
            }
        }
        assert_eq!(
            inner_product_ext(&prefix_weights, &s_ref),
            direct,
            "prefix x suffix split must factor the MLE"
        );
    }

    /// The byte-table fold behind `combine_deferred_chunk` must match the naive
    /// bit-scan on arbitrary (not necessarily eq-structured) input.
    #[test]
    fn rs_eq_ind_fast_matches_naive() {
        let mut rng = Rng::new(3);
        let tensor = rng.ext_vec(1usize << 8);
        let coordinate_weights = rng.ext_vec(DEGREE_E);
        assert_eq!(
            fold_dense(&tensor, &coordinate_weights),
            fold_ext_elems_naive(&tensor, &coordinate_weights)
        );
    }

    /// `eval_rs_eq` against the definition: materialize `rs_eq_ind = Phi(c·eq(z, .))` and take its MLE at the query's prefix with the eq table. One precomputed query serves every suffix length up to its own, as in the stacked opening, and one walk of the longest point serves each of its prefixes.
    #[test]
    fn eval_rs_eq_matches_dense() {
        let max_len = 8;
        let mut rng = Rng::new(4);
        for _ in 0..3 {
            let challenges = std::array::from_fn(|_| rng.ext());
            let coordinate_weights = build_coordinate_weights(&challenges);
            let map = RingMap::new(&mut Native, &challenges);
            let query = rng.ext_vec(max_len);
            let lead = rng.ext_vec(max_len);
            let lengths: Vec<usize> = (0..=max_len).rev().collect();
            let prefix_terms = map.prefix_terms(&mut Native, &lead, &ladders(&query), &lengths);
            for (&len, terms) in lengths.iter().zip(&prefix_terms) {
                let z = &lead[..len];
                let scale = rng.ext();
                let scaled: Vec<F192> = eq_table(z).iter().map(|&e| scale * e).collect();
                let rs_eq_ind = fold_dense(&scaled, &coordinate_weights);
                let dense = inner_product_ext(&rs_eq_ind, &eq_table(&query[..len]));
                assert_eq!(eval_rs_eq(z, scale, &map, &query), dense, "suffix length {len}");
                let scaled_terms: Vec<F192> = terms.iter().map(|&t| t * scale).collect();
                assert_eq!(RingMap::close(&mut Native, &scaled_terms), dense, "prefix length {len}");
            }
        }
    }

    struct E2e {
        vc: VerifierConfig,
        log_n: usize,
        prefix_weights: Vec<F192>,
        suffix_point: Vec<F192>,
        claim: F192,
        root: Hash,
        rs_s_hat_v: Vec<F192>,
        fs: ProofTranscript,
    }

    const E2E_DOMAIN: &[u8] = b"ring-switch-e2e-test";

    /// Full prover pipeline: random bit witness, pack, commit, ring switch
    /// (plain-point eq weights or a caller-supplied generalized weight
    /// vector), then the whir opening on (rs_eq_ind, sumcheck_claim),
    /// all over one continuous transcript.
    fn prove_e2e(m: usize, seed: u64, generalized_weights: bool) -> E2e {
        let mut rng = Rng::new(seed);
        let bits = rng.bits(1usize << m);
        let packed = pack_witness(&bits);
        let log_n = m - F64::DEGREE.ilog2() as usize;
        let pc = test_config_for(log_n);
        let (cm, pd) = commit(&packed, log_n, pc.initial_k(), pc.log_inv_rates()[0]);

        let suffix_point = rng.ext_vec(log_n);
        let prefix_weights: Vec<F192> = if generalized_weights {
            // Synthetic non-eq weights (e.g. standing in for phi_8 Lagrange
            // weights): any 64 E-values work.
            rng.ext_vec(F64::DEGREE)
        } else {
            eq_table(&rng.ext_vec(F64::DEGREE.ilog2() as usize))
        };
        let claim = inner_product_ext(&prefix_weights, &s_hat_v_reference(&packed, &suffix_point));

        // One family of one claim: its slices, the map, then its target and its weight at a scale of one.
        let mut ps = ProverState::from_label(E2E_DOMAIN);
        let rs_s_hat_v = s_hat_v_reference(&packed, &suffix_point);
        let coordinate_weights = build_coordinate_weights(&sample_map_challenges(&mut ps));
        let sumcheck_claim = column_target(&rs_s_hat_v, &coordinate_weights);
        let weight = deferred_weight(&suffix_point, F192::ONE, &coordinate_weights);
        let mut rs_eq_ind = vec![F192::ZERO; packed.len()];
        combine_deferred_chunk(&[weight], 0, &mut rs_eq_ind);
        assert_eq!(inner_product_base_ext(&packed, &rs_eq_ind), sumcheck_claim);
        recursive_prover_with_basis(
            &pc,
            log_n,
            &packed,
            rs_eq_ind.to_vec(),
            sumcheck_claim,
            &pd.codeword,
            &pd.merkle_tree,
            &mut ps,
        );
        E2e {
            vc: pc,
            log_n,
            prefix_weights,
            suffix_point,
            claim,
            root: cm.root,
            rs_s_hat_v,
            fs: ps.into_proof(),
        }
    }

    /// Finish the caller-supplied slices against the shared map: the verifier's
    /// half of the two phases, shared by both paths below. As in production, the
    /// slices ride the statement, tied to `claim` by the caller.
    fn verify_e2e_reduction(
        e: &E2e,
        vs: &mut VerifierState<'_>,
    ) -> Option<([F192; COMPOSITION_SHIFTS.len()], Vec<F192>, F192)> {
        if inner_product_ext(&e.prefix_weights, &e.rs_s_hat_v) != e.claim {
            return None;
        }
        let challenges = sample_map_challenges(vs);
        let coordinate_weights = build_coordinate_weights(&challenges);
        let sumcheck_claim = column_target(&e.rs_s_hat_v, &coordinate_weights);
        Some((challenges, coordinate_weights, sumcheck_claim))
    }

    /// Dense verification: rebuild `rs_eq_ind`, and let the whir verifier's
    /// terminal closure evaluate its MLE from the whole table.
    fn verify_e2e_dense(e: &E2e) -> bool {
        let mut vs = VerifierState::from_label(E2E_DOMAIN, &e.fs);
        let Some((_, coordinate_weights, sumcheck_claim)) = verify_e2e_reduction(e, &mut vs) else {
            return false;
        };
        let rs_eq_ind = fold_dense(&eq_table(&e.suffix_point), &coordinate_weights);
        recursive_verifier_with_basis_succinct(
            &mut vs,
            &e.vc,
            e.log_n,
            1 << e.vc.initial_k(),
            sumcheck_claim,
            e.root,
            |_, point| inner_product_ext(&rs_eq_ind, &eq_table(point)),
        )
        .is_ok()
    }

    /// Succinct verification: no `rs_eq_ind`, the succinct whir verifier's
    /// terminal closure evaluates its MLE once via `eval_rs_eq`.
    fn verify_e2e_succinct(e: &E2e) -> bool {
        let mut vs = VerifierState::from_label(E2E_DOMAIN, &e.fs);
        let Some((challenges, _, sumcheck_claim)) = verify_e2e_reduction(e, &mut vs) else {
            return false;
        };
        let map = RingMap::new(&mut Native, &challenges);
        recursive_verifier_with_basis_succinct(
            &mut vs,
            &e.vc,
            e.log_n,
            1 << e.vc.initial_k(),
            sumcheck_claim,
            e.root,
            |_, point| eval_rs_eq(&e.suffix_point, F192::ONE, &map, point),
        )
        .is_ok()
    }

    #[test]
    fn end_to_end_plain_point() {
        for (m, seed) in [(13usize, 10u64), (17, 11)] {
            let e = prove_e2e(m, seed, false);
            assert!(verify_e2e_dense(&e), "dense e2e rejected at m={m}");
            assert!(verify_e2e_succinct(&e), "succinct e2e rejected at m={m}");
        }
    }

    #[test]
    fn end_to_end_generalized_weights() {
        let e = prove_e2e(13, 12, true);
        assert!(verify_e2e_dense(&e), "dense e2e (generalized) rejected");
        assert!(verify_e2e_succinct(&e), "succinct e2e (generalized) rejected");
    }

    /// Tampering: a slice flip breaks the caller's claim check; a
    /// claim-preserving forgery (two slices adjusted so the weighted sum is
    /// unchanged) passes that check but diverges the ring-switch target, so the
    /// whir opening must reject it. A tampered claim value, or any whir stream
    /// word, is rejected too. Dense and succinct paths must agree throughout.
    #[test]
    fn end_to_end_rejects_tampering() {
        let e = prove_e2e(13, 13, false);
        let with = |s_hat_v: Vec<F192>, claim: F192, fs: ProofTranscript| E2e {
            rs_s_hat_v: s_hat_v,
            vc: e.vc.clone(),
            log_n: e.log_n,
            prefix_weights: e.prefix_weights.clone(),
            suffix_point: e.suffix_point.clone(),
            claim,
            root: e.root,
            fs,
        };

        // Plain slice flip: caught by the claim check.
        let mut s = e.rs_s_hat_v.clone();
        s[5].c1 ^= 1;
        let bad = with(s, e.claim, e.fs.clone());
        assert!(!verify_e2e_dense(&bad), "flipped slice accepted");
        assert!(!verify_e2e_succinct(&bad), "flipped slice accepted (succinct)");

        // Claim-preserving forgery: s'_1 = s_1 + d, s'_0 = s_0 + w_1*d/w_0
        // keeps sum_i w_i s'_i = claim, so the claim check passes; the ring
        // switch must still reject, its target and weights diverging from what
        // the whir proof was built for.
        let mut rng = Rng::new(99);
        let d = rng.ext();
        let (w0, w1) = (e.prefix_weights[0], e.prefix_weights[1]);
        assert!(!w0.is_zero() && !d.is_zero());
        let mut s = e.rs_s_hat_v.clone();
        s[1] += d;
        s[0] += w1 * d * w0.inv();
        let bad = with(s, e.claim, e.fs.clone());
        assert_eq!(
            inner_product_ext(&bad.prefix_weights, &bad.rs_s_hat_v),
            e.claim,
            "forgery must be claim-preserving for this test to bite"
        );
        assert!(!verify_e2e_dense(&bad), "claim-preserving forgery accepted (dense)");
        assert!(
            !verify_e2e_succinct(&bad),
            "claim-preserving forgery accepted (succinct)"
        );

        // Tampered claim value.
        let bad = with(e.rs_s_hat_v.clone(), e.claim + F192::ONE, e.fs.clone());
        assert!(!verify_e2e_dense(&bad), "tampered claim accepted");
        assert!(!verify_e2e_succinct(&bad), "tampered claim accepted (succinct)");

        // Tampered whir stream word.
        let mut fs = e.fs.clone();
        fs.stream[0] += F192::ONE;
        let bad = with(e.rs_s_hat_v.clone(), e.claim, fs);
        assert!(!verify_e2e_dense(&bad), "tampered stream word accepted");
        assert!(!verify_e2e_succinct(&bad), "tampered stream word accepted (succinct)");
    }
}
