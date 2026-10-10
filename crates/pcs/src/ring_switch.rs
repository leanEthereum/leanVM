// CREDIT: https://github.com/succinctlabs/flock (flock-core), MIT OR Apache-2.0.
//
// The rectangular (f = 64, e = 192) generalization described in the ring-switching-generalized note.

//! Ring switching: bit-slice claims on a packed witness, reduced to one claim the opening proves.
//!
//! The witness is 64 bit polynomials `Q_i`, packed into one `K = GF(2^64)` word per point, bit `i` in `x^i`.
//! A claim is the 64 slices `s_i = MLE(Q_i)(r)` at a point `r` over `E = GF(2^192)` (doc `leanvm` Annex A).
//!
//! # The reduction
//!
//! An `F_2`-linear map `Phi : E -> E` is drawn once the slices are bound (`rs:map`), and then:
//!
//! ```text
//!     sum_u Phi(eq(r, u)) * q(u)  =  sum_{i<64} x^i * Phi(s_i)
//! ```
//!
//! - The left side is what the opening proves: the packed witness `q` against the weight `Phi(eq(r, .))`.
//! - The right side is the target, which both sides compute from the slices.
//! - The caller sends and checks the slices, so this module reads no prover message: it only draws challenges.
//!
//! # One family per opening
//!
//! All of an opening's claims, on any regions and at unrelated points, are switched together (`rs:family`).
//! A challenge `gamma_rs` is drawn before `Phi`, and claim `j` takes the scale `gamma_rs^j` inside the map:
//!
//! ```text
//!     slice i of the family       =  sum_j gamma_rs^j * s_{j,i}
//!     weight on claim j's region  =  Phi(gamma_rs^j * eq(r_j, .))
//! ```
//!
//! # Prover and verifier
//!
//! - The prover keeps each claim's weight factored and adds every claim's weight into one dense weight.
//! - The verifier evaluates the weight's multilinear extension in closed form (`rs:weight`).
//! - It moves the Frobenius onto the opening's point (`rs:cost`), so one ladder per coordinate serves every claim.
//! - Claims whose points are prefixes of one another share one pass of products.

use fiat_shamir::arith::{Arith, Verifier};
use fiat_shamir::transcript::Challenger;
use primitives::bit_fold::{BLOCK, F192Map, Sliced};
use primitives::field::{F64, F192};
use primitives::multilinear::{EQ_PAR_LEN, eq_table, eq_table_seeded};
use std::cmp::Reverse;

/// The Frobenius shifts `d_p = 2^(5 - p)` of the six two-term maps, in the order they compose.
///
/// Descending order keeps every challenge's exponent at most `2^31`, so the check's degree stays below `2^32`.
pub const COMPOSITION_SHIFTS: [usize; 6] = [32, 16, 8, 4, 2, 1];

/// The degree of `E` over `F_2`: the number of coordinate bits the map weighs.
const DEGREE_E: usize = 192;

/// The image under `Phi` of each `F_2`-basis element of `E`: entry `w` is `Phi(e_w)`.
///
/// The basis element `e_w = x^(w % 64) * y^(w / 64)` is bit `w % 64` of coefficient `w / 64`.
/// `Phi` composes six two-term maps on its input `a_0 = a`:
///
/// ```text
///     a_{p+1} = a_p + f_p * a_p^(2^d_p)        d_p = 32, 16, 8, 4, 2, 1
///     Phi(a)  = a_6
/// ```
///
/// # Why these weights batch the slices
///
/// Write `s_{i,w}` for bit `w` of slice `s_i`, and `t_w = sum_i s_{i,w} * x^i` in `K` for column `w`.
/// `Phi` is `F_2`-linear, so the target is the columns against the weights:
///
/// ```text
///     sum_{i<64} x^i * Phi(s_i)  =  sum_{w<192} Phi(e_w) * t_w
/// ```
///
/// Expanding the composition gives the Frobenius form, with one distinct monomial at each exponent:
///
/// ```text
///     Phi(a) = sum_{k<64} C_k * a^(2^k)
///     C_k    = prod_{p : k_p = 1} f_p^(2^(k mod 2^(5-p)))        k = sum_p k_p * 2^(5-p)
/// ```
///
/// Applying the composition directly costs 63 squarings and six products.
///
/// # Soundness
///
/// Let `delta` be the prover's error on the columns `t_w`, nonzero and fixed before the six challenges are drawn.
/// The check misses it exactly when this sum vanishes:
///
/// ```text
///     sum_w Phi(e_w) * delta_w  =  sum_{k<64} C_k * V_k        V_k = sum_w e_w^(2^k) * delta_w
/// ```
///
/// Step 1: some `V_k` is nonzero.
/// Write `w = 64j + i`, so that `e_w^(2^k) = x^(i * 2^k) * (y^(2^k))^j`:
///
/// ```text
///     V_k     = sum_{j<3} (y^(2^k))^j * R_{j,k}
///     R_{j,k} = sum_{i<64} delta_{64j+i} * x^(i * 2^k)        in K
/// ```
///
/// - `y^(2^k)` is not in `K`: squaring is a bijection of `K`, so it would put `y` in `K`.
/// - `[E : K] = 3` is prime, so `1, y^(2^k), y^(2 * 2^k)` is a `K`-basis of `E`.
/// - Hence `V_k = 0` forces `R_{0,k} = R_{1,k} = R_{2,k} = 0`.
/// - At fixed `j`, `R_{j,k} = D_j(x^(2^k))` for the polynomial `D_j(U) = sum_{i<64} delta_{64j+i} * U^i`.
/// - The 64 points `x, x^2, x^4, ..., x^(2^63)` are distinct, since `x` has degree 64 over `F_2`.
/// - `D_j` has degree at most 63, so 64 roots force `D_j = 0`: all `V_k = 0` would mean `delta = 0`.
///
/// Step 2: the 64 `C_k` are distinct monomials in the challenges, so `sum_k C_k * V_k` is a nonzero polynomial.
/// Its total degree is that of `C_63`, below `2^32`, so by Schwartz-Zippel the check misses with probability below:
///
/// ```text
///     deg C_63 / |E|  =  (2^31 + 2^15 + 2^7 + 2^3 + 2 + 1) / 2^192  <  2^32 / 2^192  =  2^-160
/// ```
///
/// # Why 64 terms
///
/// A map with Frobenius exponents in a set `S` gives `|S|` equations over `E`, that is `3 |S|` over `K`.
/// There are 192 unknowns in `K`, so with `3 |S| < 192` some nonzero error passes for every choice of coefficients.
pub(crate) fn build_coordinate_weights(challenges: &[F192; COMPOSITION_SHIFTS.len()]) -> Vec<F192> {
    // `e_w` has only bit `w` set: `x^(w % 64)` in the coefficient of `1`, `y` or `y^2`.
    let basis = |w: usize| match w / F64::DEGREE {
        0 => F192::new(1u64 << (w % F64::DEGREE), 0, 0),
        1 => F192::new(0, 1u64 << (w % F64::DEGREE), 0),
        _ => F192::new(0, 0, 1u64 << (w % F64::DEGREE)),
    };
    (0..DEGREE_E)
        .map(|w| apply_composed_map(basis(w), challenges))
        .collect()
}

/// `Phi` of one value, by its six two-term maps.
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

/// Draws the six challenges `f_0..f_5` of `Phi`.
///
/// Call it only once every slice the map batches is bound to the transcript.
pub(crate) fn sample_map_challenges(ch: &mut impl Challenger) -> [F192; COMPOSITION_SHIFTS.len()] {
    std::array::from_fn(|_| ch.sample())
}

/// One claim's weight `Phi(scale * eq(point, .))`, kept factored rather than stored.
///
/// - `eq(point, .)` is the product of a table over the low variables and one over the high variables.
/// - `Phi` is `F_2`-linear, so several claims' weights add into one buffer with no product between them.
pub(crate) struct DeferredWeight {
    /// `eq` over the low variables of the point, lowest variable in the lowest index bit.
    eq_lo: Vec<F192>,
    /// `scale * eq` over the high variables.
    eq_hi: Vec<F192>,
    /// The map `Phi`.
    map: F192Map,
    /// The fast path, present when the low table is whole 64-entry blocks.
    sliced: Option<SlicedWeight>,
}

/// A weight's fast path: word `lo + |eq_lo| * hi` is the map of high entry `hi` applied to `eq_lo[lo]`.
struct SlicedWeight {
    /// The low table's blocks, transposed once into the layout the map reads.
    blocks: Vec<Sliced>,
    /// One map per high entry, `v -> Phi(eq_hi[hi] * v)`.
    maps: Vec<F192Map>,
}

/// The number of high variables of a sliced weight: none up to 14 variables, then one per extra variable, at most 8.
///
/// Why: each high entry costs one composed map, which pays off only over a long run of low entries.
fn sliced_hi_bits(n: usize) -> usize {
    n.saturating_sub(14).min(8)
}

impl DeferredWeight {
    /// The weights `map_i(scale_i * eq(point_i, .))` of several claims, without materializing them.
    ///
    /// # Algorithm
    ///
    /// - Each weight's factored eq tables are one task of a first dispatch.
    /// - Then every composed map of every weight is one task of a second, so one large claim does not run alone.
    ///
    /// It dispatches on the thread pool, so it must not run inside a parallel dispatch.
    pub(crate) fn batch<'a>(claims: impl IntoIterator<Item = (&'a [F192], F192, F192Map)>) -> Vec<Self> {
        let (specs, maps): (Vec<_>, Vec<_>) = claims
            .into_iter()
            .map(|(point, scale, map)| ((point, scale), map))
            .unzip();

        // Phase 1: the factored tables, and the sliced blocks where the low table is whole 64-entry blocks.
        // A low table large enough to build in parallel is built here, the others one task each.
        let n_lo = |n: usize| if n >= 6 { n - sliced_hi_bits(n) } else { split_n_lo(n) };
        let wide = |i: usize| 1usize << n_lo(specs[i].0.len()) >= EQ_PAR_LEN;
        let mut wide_tables = (0..specs.len())
            .filter(|&i| wide(i))
            .map(|i| {
                let (point, scale) = specs[i];
                Self::tables(point, n_lo(point.len()), scale, |eq_lo| {
                    let blocks = eq_lo.as_chunks::<BLOCK>().0;
                    parallel::map_collect(blocks.len(), |b| Sliced::new(&blocks[b]))
                })
            })
            .collect::<Vec<_>>()
            .into_iter();
        let narrow = parallel::map_collect(specs.len(), |i| {
            let (point, scale) = specs[i];
            (!wide(i)).then(|| {
                Self::tables(point, n_lo(point.len()), scale, |eq_lo| {
                    eq_lo.as_chunks::<BLOCK>().0.iter().map(Sliced::new).collect()
                })
            })
        });
        let tables = narrow
            .into_iter()
            .map(|t| t.unwrap_or_else(|| wide_tables.next().expect("one per wide claim")));
        let mut weights: Vec<Self> = (tables.into_iter().zip(maps))
            .map(|((eq_lo, eq_hi, sliced), map)| Self {
                eq_lo,
                eq_hi,
                map,
                sliced,
            })
            .collect();

        // Phase 2: one task per composed map `v -> map(eq_hi[hi] * v)`, across every sliced weight.
        let jobs: Vec<(usize, usize)> = (weights.iter().enumerate())
            .filter(|(_, w)| w.sliced.is_some())
            .flat_map(|(i, w)| (0..w.eq_hi.len()).map(move |hi| (i, hi)))
            .collect();
        let mut maps = parallel::map_collect(jobs.len(), |j| {
            let (i, hi) = jobs[j];
            weights[i].map.after_mul(weights[i].eq_hi[hi])
        })
        .into_iter();
        for w in &mut weights {
            if let Some(sliced) = &mut w.sliced {
                sliced.maps.extend(maps.by_ref().take(w.eq_hi.len()));
            }
        }
        weights
    }

    /// The factored tables of `scale * eq(point, .)` split after `n_lo` variables, the low one sliced by `slice` from six variables.
    fn tables(
        point: &[F192],
        n_lo: usize,
        scale: F192,
        slice: impl FnOnce(&[F192]) -> Vec<Sliced>,
    ) -> (Vec<F192>, Vec<F192>, Option<SlicedWeight>) {
        // Six or more variables: the low table is at least one 64-entry block, so the fast path applies.
        let (eq_lo, eq_hi) = (eq_table(&point[..n_lo]), eq_table_seeded(&point[n_lo..], scale));
        let sliced = (n_lo >= 6).then(|| SlicedWeight {
            blocks: slice(&eq_lo),
            maps: Vec::new(),
        });
        (eq_lo, eq_hi, sliced)
    }

    /// The number of words the weight spans, `2^|point|`.
    pub(crate) const fn len(&self) -> usize {
        self.eq_lo.len() * self.eq_hi.len()
    }

    /// Adds the weight's words `start..start + out.len()` into `out`.
    ///
    /// No copy of the weight is stored or read back, so a caller can sweep it one cache-resident window at a time.
    ///
    /// # Panics
    ///
    /// If the window runs past the weight's end.
    pub(crate) fn add_to(&self, start: usize, out: &mut [F192]) {
        let block_len = self.eq_lo.len();
        assert!(start + out.len() <= self.len());
        let mut eq = [F192::ZERO; BLOCK];
        for (b, out) in out.chunks_mut(BLOCK).enumerate() {
            let first = start + b * BLOCK;
            match &self.sliced {
                // An aligned block lies under one high entry: its pre-transposed low block through that entry's map.
                Some(SlicedWeight { blocks, maps }) if first.is_multiple_of(BLOCK) => {
                    maps[first / block_len].apply_sliced_add(&blocks[first % block_len / BLOCK], out);
                }
                // Otherwise form each word's `eq` product, then map the block.
                // Entries of `eq` past `out.len()` are stale, but the map adds only `out.len()` images.
                _ => {
                    for (i, e) in eq[..out.len()].iter_mut().enumerate() {
                        let index = first + i;
                        *e = self.eq_lo[index % block_len] * self.eq_hi[index / block_len];
                    }
                    self.map.apply_add(&eq, out);
                }
            }
        }
    }
}

/// The low variables of a small weight's split: half of `n`, but at least four, or all `n` when fewer.
///
/// Four is where two factor tables start to beat one full table.
fn split_n_lo(n: usize) -> usize {
    (n / 2).clamp(4.min(n), n)
}

/// The ring-switching map `Phi` in Frobenius form, stored as the 64 coefficients `C_k^(2^-k)`.
///
/// `Phi(v) = sum_{k<64} C_k * v^(2^k)`, and `a^(2^-k) = a^(2^(192-k))` undoes `k` squarings.
/// `E` is the element type: field values natively, or the wires the recursive verifier holds.
pub struct RingMap<E> {
    /// `C_k^(2^-k)` at index `k`.
    coefficients: Vec<E>,
}

/// `x^(2^-k)` for each `k < 64`, at compile time: `x^(2^(64 - k))`, since 64 squarings are the identity on `K`.
static X_ROOTS: [F64; F64::DEGREE] = {
    let mut roots = [F64::G; F64::DEGREE];
    let (mut power, mut i) = (F64::G, 1);
    while i < F64::DEGREE {
        // `x^(2^i)`, which is `x^(2^-(64 - i))`.
        power = power.square_portable();
        roots[F64::DEGREE - i] = power;
        i += 1;
    }
    roots
};

impl<E: Copy> RingMap<E> {
    /// The map of the six challenges `f_0..f_5`, in drawing order.
    ///
    /// ```text
    ///     C_k^(2^-k) = prod_{p : bit d_p of k is set} f_p^(2^-(k - k mod d_p))
    /// ```
    ///
    /// `k - k mod d_p` keeps the bits of `k` from `d_p` up, so the products grow one shift at a time.
    /// Stage `p` extends every index `k` built so far by `d_p`, or leaves it.
    pub fn new<A: Arith<E = E>>(a: &mut A, challenges: &[E; COMPOSITION_SHIFTS.len()]) -> Self {
        // Invariant: `prefixes` holds `(k, C_k^(2^-k))` for every `k` made of the shifts seen so far.
        let mut prefixes = vec![(0usize, a.one())];
        for (&f, &shift) in challenges.iter().zip(&COMPOSITION_SHIFTS) {
            // `ladder[j] = f^(2^-j)` for `j >= shift`, which covers every new index `k + shift`.
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

    /// The target `sum_{i<64} x^i * Phi(s_i)` of the 64 slices `s`.
    ///
    /// ```text
    ///     target = sum_{k<64} (C_k^(2^-k) * S(x^(2^-k)))^(2^k)        S(u) = sum_i s_i * u^i
    /// ```
    ///
    /// Why: the Frobenius is additive, and raising `x^(i * 2^-k)` to the power `2^k` gives back `x^i`.
    ///
    /// # Panics
    ///
    /// If there are not exactly 64 slices.
    pub fn target<A: Arith<E = E>>(&self, a: &mut A, slices: &[E]) -> E {
        assert_eq!(slices.len(), F64::DEGREE, "a family has 64 slices");
        let terms: Vec<E> = (0..F64::DEGREE)
            .map(|k| {
                // `S(x^(2^-k))` by Horner's rule, from the last slice down.
                let (&last, rest) = slices.split_last().expect("64 slices");
                let s = (rest.iter().rev()).fold(last, |acc, &sj| a.mul_const_add(acc, F192::from(X_ROOTS[k]), sj));
                a.mul(self.coefficients[k], s)
            })
            .collect();
        Self::close(a, &terms)
    }

    /// A claim's 64 terms `C_k^(2^-k) * P_k` at several prefix lengths of one point `z`, for a query `q`.
    ///
    /// ```text
    ///     P_k = prod_{n < len} (1 + z_n + q_n^(2^-k))
    ///     MLE(Phi(eq(z[..len], .)))(q[..len]) = sum_{k<64} (C_k^(2^-k) * P_k)^(2^k)
    /// ```
    ///
    /// This is the closed form of `rs:weight`, with every Frobenius power moved onto the query (`rs:cost`).
    ///
    /// # Arguments
    ///
    /// - `z`: the longest point; every claim's point is a prefix of it.
    /// - `ladders`: `ladders[n][k] = q_n^(2^-k)`, one ladder per coordinate of the query.
    /// - `lengths`: the prefix lengths wanted.
    ///
    /// # Returns
    ///
    /// Entry `i` holds the terms at prefix length `lengths[i]`.
    ///
    /// # Panics
    ///
    /// If a length exceeds `z` or the ladders.
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
        // Copies the current terms into every output whose length is `n`.
        let take = |n: usize, terms: &[E], out: &mut [Vec<E>]| {
            for (slot, _) in out.iter_mut().zip(lengths).filter(|&(_, &len)| len == n) {
                *slot = terms.to_vec();
            }
        };
        // One pass serves every length: extending a prefix by a coordinate multiplies each term by one factor.
        let mut terms = self.coefficients.clone();
        take(0, &terms, &mut out);
        for (n, (&zn, ladder)) in z.iter().zip(ladders).take(longest).enumerate() {
            // Term `k` times `1 + z_n + q_n^(2^-k)`.
            for (term, &power) in terms.iter_mut().zip(ladder) {
                let s = a.add(power, zn);
                *term = a.times_one_plus(*term, s);
            }
            take(n + 1, &terms, &mut out);
        }
        out
    }

    /// `sum_k terms[k]^(2^k)`, by the linearized Horner rule `acc <- acc^2 + terms[k]` from the last term down.
    ///
    /// The Frobenius is additive, so several claims' terms can be added first and closed once.
    ///
    /// # Panics
    ///
    /// If `terms` is empty.
    pub fn close<A: Arith<E = E>>(a: &mut A, terms: &[E]) -> E {
        let (&last, rest) = terms.split_last().expect("the map has 64 terms");
        rest.iter().rev().fold(last, |acc, &term| a.mul_add(acc, acc, term))
    }
}

/// The 64 entries `v^(2^-j)` for `j` from `lowest` up, and `v` itself below `lowest`.
///
/// It starts from `v^(2^-64) = v^(2^128)`, two applications of `a -> a^(2^64)`, which need no product (`rs:cost`).
/// Squaring then climbs from `v^(2^-63)` down to `v^(2^-lowest)`; a `lowest` of 0 acts as 1, entry 0 being `v`.
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

/// One ring-switched claim on a packed region: its 64 bit-slice values at a point.
///
/// - Slice `i` is the multilinear extension of the words' bit `i` at the point.
/// - The caller sends and checks the slices, so the opening only binds them to the commitment.
/// - `E` is the element type: field values natively, or the wires the recursive verifier holds.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SliceClaim<E = F192> {
    /// The point, one coordinate per variable of the region.
    pub suffix_point: Vec<E>,
    /// The 64 slice values at the point, slice `i` for bit `i`.
    pub s_hat_v: Vec<E>,
}

impl<E: Copy> SliceClaim<E> {
    /// A claim whose slices past the given ones are `zero`.
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

/// The challenges that make all of an opening's ring-switched claims one family (`rs:family`).
///
/// - `gamma_rs`, drawn once every claim's slices are bound: claim `j` takes the scale `gamma_rs^j`.
/// - Then the six challenges of `Phi`, one map for the whole family.
/// - `E` is the element type: field values natively, or the wires the recursive verifier holds.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct RingFamily<E = F192> {
    /// The scale challenge: claim `j` is scaled by `gamma_rs^j`.
    gamma_rs: E,
    /// The six challenges `f_0..f_5` of `Phi`, in drawing order.
    map_challenges: [E; COMPOSITION_SHIFTS.len()],
}

impl RingFamily {
    /// Draws the family's challenges on the prover's side: `gamma_rs`, then the six of `Phi`.
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

    /// `Phi` as an `F_2`-linear map on the 192 coordinate bits of `E`, the form the prover applies to blocks.
    pub(crate) fn map(&self) -> F192Map {
        F192Map::new(&build_coordinate_weights(&self.map_challenges))
    }
}

impl<E: Copy> RingFamily<E> {
    /// Draws the family's challenges on the verifier's side, in the prover's order.
    pub fn draw<V: Verifier<E = E>>(v: &mut V) -> Self {
        let gamma_rs = v.sample();
        let map = v.sample_vec(COMPOSITION_SHIFTS.len());
        Self {
            gamma_rs,
            map_challenges: std::array::from_fn(|i| map[i]),
        }
    }

    /// The family of the regions' claims under `Phi`, in region order then claim order.
    ///
    /// Claim `j` in that order takes the scale `gamma_rs^j`.
    pub fn share<'a, A: Arith<E = E>>(&self, a: &mut A, rings: &'a [RingSwitch<E>]) -> RingShare<'a, E> {
        let n_claims = rings.iter().map(|ring| ring.claims.len()).sum();
        let scales = a.powers(self.gamma_rs, n_claims);
        let map = RingMap::new(a, &self.map_challenges);
        RingShare { rings, scales, map }
    }
}

/// An opening's ring-switched claims as one family under one map: its target, and its weight at a point.
pub struct RingShare<'a, E> {
    /// The regions and their claims, in order.
    rings: &'a [RingSwitch<E>],
    /// `gamma_rs^j` for claim `j` across the regions.
    scales: Vec<E>,
    /// `Phi` in Frobenius form.
    map: RingMap<E>,
}

impl<E: Copy + PartialEq> RingShare<'_, E> {
    /// The family's target `sum_{i<64} x^i * Phi(sum_j gamma_rs^j * s_{j,i})`.
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

    /// The family's weight at a point `x` of the stack's cube.
    ///
    /// ```text
    ///     W(x) = sum_j eq(sel_j, x_hi) * MLE(Phi(gamma_rs^j * eq(r_j, .)))(x_lo)
    /// ```
    ///
    /// - Claim `j` is the `j`-th claim across the regions in order, at the point `r_j`.
    /// - `x_lo` is the coordinates of `x` below its region's variable count, `x_hi` the rest.
    /// - `sel_j` is the region's offset above its variables, read as bits.
    ///
    /// Three savings keep it cheap:
    ///
    /// - The Frobenius moves onto `x`, so one ladder per coordinate serves every claim.
    /// - Claims whose points are prefixes of one another share one pass of products over the longest.
    /// - A region's claims add their scaled terms and close once, the Frobenius being additive.
    ///
    /// # Panics
    ///
    /// If a region has more variables than `x` has coordinates, or a claim's point is longer than every region.
    pub fn weight_at<A: Arith<E = E>>(&self, a: &mut A, x: &[E]) -> E {
        let max_vars = self.rings.iter().map(|ring| ring.qflock_vars).max().unwrap_or(0);
        let ladders: Vec<Vec<E>> = x[..max_vars]
            .iter()
            .map(|&q| inverse_frobenius_ladder(a, q, 1))
            .collect();
        let zero = a.zero();
        // Phase 1: every prefix group's terms, each claim's scaled and summed into its region.
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
        // Phase 2: close each region's sum and select the region's place in the stack.
        let mut weight = zero;
        for (ring, sum) in self.rings.iter().zip(&sums) {
            let part = RingMap::close(a, sum);
            let sel_eq = a.eq_bits(ring.offset >> ring.qflock_vars, &x[ring.qflock_vars..]);
            weight = a.mul_add(sel_eq, part, weight);
        }
        weight
    }
}

/// Claims whose points are all prefixes of the longest one, `lead`, so one pass of products serves them all.
///
/// Points compare element by element: for the recursive verifier, two points match when they hold the same wires.
#[derive(Clone, Debug)]
pub struct PrefixGroup<'a, E = F192> {
    /// The longest point.
    pub lead: &'a [E],
    /// The distinct prefix lengths its claims sit at.
    pub lengths: Vec<usize>,
    /// Its claims, each naming the index of its length in `lengths`.
    pub members: Vec<PrefixMember>,
}

/// One claim of a prefix group.
#[derive(Clone, Copy, Debug)]
pub struct PrefixMember {
    /// Its index across every region's claims, which picks its scale.
    pub claim: usize,
    /// The index of its region.
    pub ring: usize,
    /// The index of its point's length in the group's lengths.
    pub length: usize,
}

impl<'a, E: PartialEq> PrefixGroup<'a, E> {
    /// Groups every claim of the regions, longest points first.
    ///
    /// A claim joins the first group whose lead its point is a prefix of, and otherwise opens a new group.
    pub fn of(rings: &'a [RingSwitch<E>]) -> Vec<Self> {
        let mut claims: Vec<(usize, usize, &'a [E])> = rings
            .iter()
            .enumerate()
            .flat_map(|(r, ring)| ring.claims.iter().map(move |claim| (r, claim.suffix_point.as_slice())))
            .enumerate()
            .map(|(i, (r, point))| (i, r, point))
            .collect();
        // Longest first, so a group's lead is its longest point; the stable sort keeps claim order among ties.
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
    use fiat_shamir::arith::Native;
    use primitives::multilinear::eq_eval;
    use primitives::test_util::Rng;
    use std::collections::HashSet;

    /// The total degree of `C_63`, the largest of the map's monomials in its six challenges.
    ///
    /// The WHIR soundness accounting takes it as the degree of the ring-switching check.
    pub(crate) const RING_SWITCH_SOUNDNESS_DEGREE: usize =
        (1usize << 31) + (1usize << 15) + (1usize << 7) + (1usize << 3) + (1usize << 1) + 1;

    /// The family's target from its definition: `sum_i x^i Phi(s_i)`, each `Phi` applied in its composed form.
    fn row_target(slices: &[F192], challenges: &[F192; COMPOSITION_SHIFTS.len()]) -> F192 {
        let x = F192::new(2, 0, 0);
        (slices.iter().rev()).fold(F192::ZERO, |acc, &s| acc * x + apply_composed_map(s, challenges))
    }

    /// The query's inverse Frobenius ladders, one per coordinate.
    fn ladders(query: &[F192]) -> Vec<Vec<F192>> {
        query
            .iter()
            .map(|&q| inverse_frobenius_ladder(&mut Native, q, 1))
            .collect()
    }

    /// `Phi` of a dense tensor, one block at a time.
    fn fold_dense(tensor: &[F192], map: &F192Map) -> Vec<F192> {
        let mut out = vec![F192::ZERO; tensor.len()];
        for (xs, out) in tensor.chunks(BLOCK).zip(out.chunks_mut(BLOCK)) {
            let mut block = [F192::ZERO; BLOCK];
            block[..xs.len()].copy_from_slice(xs);
            map.apply_add(&block, out);
        }
        out
    }

    /// Pack bit `64 * y + i` of `bits` into bit `i` of word `y`.
    fn pack_witness(bits: &[bool]) -> Vec<F64> {
        let word = |c: &[bool]| c.iter().rev().fold(0, |acc, &b| acc << 1 | b as u64);
        bits.chunks(F64::DEGREE).map(|c| F64(word(c))).collect()
    }

    /// The slices by brute force: each bit column's multilinear extension at the point, read bit by bit.
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

    #[test]
    fn the_coordinate_map_is_the_composed_map() {
        // Invariant: the byte-table map built from the 192 coordinate weights is `Phi` itself, on any value.
        let mut rng = Rng::new(3);
        for _ in 0..4 {
            let challenges = std::array::from_fn(|_| rng.ext());
            let map = F192Map::new(&build_coordinate_weights(&challenges));
            let values = rng.ext_vec(BLOCK);
            let want: Vec<F192> = values.iter().map(|&v| apply_composed_map(v, &challenges)).collect();
            assert_eq!(fold_dense(&values, &map), want);
        }
    }

    #[test]
    fn a_family_at_unrelated_points_is_one_ring_switch() {
        // Invariant: the packed witness against the family's weight is its target, for claims at unrelated points.
        let mut rng = Rng::new(0xdec0_de01_2345_6789);
        let n = 9;
        let packed = pack_witness(&rng.bits(1 << (n + F64::DEGREE.ilog2() as usize)));
        let challenges = std::array::from_fn(|_| rng.ext());
        let map = F192Map::new(&build_coordinate_weights(&challenges));
        let gamma_rs = rng.ext();

        // Three claims, claim `j` scaled by `gamma_rs^j`: their slices add, and so do their weights.
        let mut slices = vec![F192::ZERO; F64::DEGREE];
        let mut dense = vec![F192::ZERO; packed.len()];
        let mut combined = vec![F192::ZERO; packed.len()];
        let mut scale = F192::ONE;
        for point in (0..3).map(|_| rng.ext_vec(n)) {
            for (slot, s) in slices.iter_mut().zip(s_hat_v_reference(&packed, &point)) {
                *slot += scale * s;
            }
            let scaled: Vec<F192> = eq_table(&point).iter().map(|&e| scale * e).collect();
            for (slot, w) in dense.iter_mut().zip(fold_dense(&scaled, &map)) {
                *slot += w;
            }
            DeferredWeight::batch([(point.as_slice(), scale, map.clone())])
                .remove(0)
                .add_to(0, &mut combined);
            scale *= gamma_rs;
        }
        assert_eq!(combined, dense);

        // Invariant: `sum_y packed[y] * w[y] = sum_i x^i Phi(s_i)`, in its row form and in its Frobenius form.
        let target = (packed.iter().zip(&combined)).fold(F192::ZERO, |acc, (&k, &w)| acc + w.mul_base(k));
        assert_eq!(target, row_target(&slices, &challenges));
        assert_eq!(
            target,
            RingMap::new(&mut Native, &challenges).target(&mut Native, &slices)
        );
    }

    #[test]
    fn composed_map_has_full_frobenius_support() {
        // Invariant: expanding the composition puts exactly one monomial at every Frobenius exponent below 64.
        // Why: soundness uses distinct monomials; distinct coordinate weights are neither needed nor always true.
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

        // Invariant: at random challenges every coefficient is nonzero, and the expansion is the composition.
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

    #[test]
    fn slices_factor_the_bit_mle() {
        // Invariant: a bit polynomial's MLE is the slices at the suffix point, weighted by `eq` of the 6-bit prefix.
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
        let split = (prefix_weights.iter().zip(&s_ref)).fold(F192::ZERO, |acc, (&p, &s)| acc + p * s);
        assert_eq!(split, direct, "prefix x suffix split must factor the MLE");
    }

    #[test]
    fn the_weight_closed_form_is_its_mle() {
        // Invariant: the closed form is the MLE of the stored weight `Phi(scale * eq(z, .))` at the query's prefix.
        // Fixture state: one query and one walk of the longest point serve every prefix length, as in the opening.
        let max_len = 8;
        let mut rng = Rng::new(4);
        for _ in 0..3 {
            let challenges = std::array::from_fn(|_| rng.ext());
            let map = F192Map::new(&build_coordinate_weights(&challenges));
            let ring_map = RingMap::new(&mut Native, &challenges);
            let query = rng.ext_vec(max_len);
            let lead = rng.ext_vec(max_len);
            let lengths: Vec<usize> = (0..=max_len).rev().collect();
            let prefix_terms = ring_map.prefix_terms(&mut Native, &lead, &ladders(&query), &lengths);
            for (&len, terms) in lengths.iter().zip(&prefix_terms) {
                let scale = rng.ext();
                let scaled: Vec<F192> = eq_table(&lead[..len]).iter().map(|&e| scale * e).collect();
                let rs_eq_ind = fold_dense(&scaled, &map);
                let eq_query = eq_table(&query[..len]);
                let dense = (rs_eq_ind.iter().zip(&eq_query)).fold(F192::ZERO, |acc, (&w, &e)| acc + w * e);
                let scaled_terms: Vec<F192> = terms.iter().map(|&t| t * scale).collect();
                assert_eq!(RingMap::close(&mut Native, &scaled_terms), dense, "prefix length {len}");
            }
        }
    }

    #[test]
    fn a_batch_builds_wide_and_narrow_claims_alike() {
        // Invariant: every word of a batched weight is `Phi(scale * eq(point, index))`, whatever the claim's size.
        //
        // Fixture state: a 24-variable claim, whose 16-variable low table builds in parallel, beside a 7-variable one.
        let mut rng = Rng::new(0xB47C);
        let map = F192Map::new(&build_coordinate_weights(&std::array::from_fn(|_| rng.ext())));
        let points = [rng.ext_vec(24), rng.ext_vec(7)];
        let scales = [rng.ext(), rng.ext()];
        let claims = (points.iter().zip(scales)).map(|(point, scale)| (point.as_slice(), scale, map.clone()));
        let weights = DeferredWeight::batch(claims);

        for ((weight, point), scale) in weights.iter().zip(&points).zip(scales) {
            // Windows at the start, straddling a block, and at the end.
            for start in [0, 61, weight.len() - 64] {
                let mut got = [F192::ZERO; BLOCK];
                weight.add_to(start, &mut got);
                let eq: [F192; BLOCK] = std::array::from_fn(|i| {
                    let bits: Vec<F192> = (0..point.len())
                        .map(|b| F192::new(((start + i) >> b & 1) as u64, 0, 0))
                        .collect();
                    scale * eq_eval(point, &bits)
                });
                let mut want = [F192::ZERO; BLOCK];
                map.apply_add(&eq, &mut want);
                assert_eq!(got, want, "{} variables, start {start}", point.len());
            }
        }
    }
}
