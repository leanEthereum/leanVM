//! Hotwire's index side: the rounds over the index `j` of cycles, memory cells and instructions, lowest bit first, each
//! of degree 2.
//!
//! The summand is a sum of terms `coef·A(j)·B(j)` and `coef·A(j)` over arrays. An array stores its first entries and
//! has a closed form past them ([`Tail`]): zero for a scattered array, the index's power, or `eq` and its shift by one
//! for the tables that pair with it. A pair of entries of a term is summed only where both of its arrays can be
//! nonzero, so a table need only be stored as far as its partner reaches.
//!
//! The pointers scatter into arrays ([`Scatter`]): each row adds its weight at its pointer's index, XORed into two
//! atomic limbs, so the order of the adds does not matter ([`add_words`]).

use super::pointer::Chunks;
use primitives::field::{F64, F128};
use primitives::multilinear::{eq_table_serial, poly_eval};
use std::sync::atomic::{AtomicBool, AtomicU64, Ordering};

/// Pairs per task of a round.
const TASK_PAIRS: usize = 1 << 12;

/// One term of the summand, over arrays named by position.
#[derive(Clone, Copy, Debug)]
pub enum Term {
    Product { coef: F128, a: usize, b: usize },
    Single { coef: F128, a: usize },
}

/// What the index side ends at: the point `r`, every array's value there, and the claim the last round leaves.
pub struct IndexEnd {
    pub point: Vec<F128>,
    pub values: Vec<F128>,
    pub claim: F128,
}

/// What an array holds past its stored entries, at index `j` over the variables still unbound.
#[derive(Clone, Debug)]
pub enum Tail {
    Zero,
    /// `c·ratio^j`.
    Powers {
        c: F128,
        ratio: F64,
    },
    /// `a·eq(point, j) + b·eq(point, j + 1)`, the point lowest variable first.
    Eq(ShiftEq),
}

/// `eq(point, j)` as the product of an entry of `low`, `eq` of the point's low half at `j`'s low bits, and one of
/// `high`, of the high half at its high bits: two tables of the square root's size.
#[derive(Clone, Debug)]
pub struct SplitEq {
    /// The variables `low` covers.
    bits: usize,
    low: Vec<F128>,
    high: Vec<F128>,
}

impl SplitEq {
    pub fn new(point: &[F128]) -> Self {
        let bits = point.len().div_ceil(2);
        Self {
            bits,
            low: eq_table_serial(&point[..bits]),
            high: eq_table_serial(&point[bits..]),
        }
    }

    /// `eq(point, j)`, for `j < 2^n`.
    pub fn at(&self, j: usize) -> F128 {
        self.low[j & (self.low.len() - 1)] * self.high[j >> self.bits]
    }

    /// `c·eq(point, ·)`, `c` taken into the low table.
    fn scaled(&self, c: F128) -> Self {
        Self {
            bits: self.bits,
            low: self.low.iter().map(|&v| c * v).collect(),
            high: self.high.clone(),
        }
    }
}

/// `a·eq(point, j) + b·eq(point, j + 1)`, the second term dropped at the top index: `eq(ζ, ·)` (`b = 0`), its shift by
/// one (`a = 0`), and what binding the lowest variable makes of either. `eq` is split ([`SplitEq`]), so an array that
/// is all tail costs no memory.
#[derive(Clone, Debug)]
pub struct ShiftEq {
    a: F128,
    b: F128,
    point: Vec<F128>,
    /// `a·eq(point, ·)` and `b·eq(point, ·)`.
    scaled: [SplitEq; 2],
}

impl ShiftEq {
    pub fn new(a: F128, b: F128, point: Vec<F128>) -> Self {
        let eq = SplitEq::new(&point);
        Self {
            a,
            b,
            scaled: [eq.scaled(a), eq.scaled(b)],
            point,
        }
    }

    /// The value at `j < 2^n`.
    pub fn at(&self, j: usize) -> F128 {
        let term = |c: F128, eq: &SplitEq, j: usize| match c.is_zero() || j >> self.point.len() != 0 {
            true => F128::ZERO,
            false => eq.at(j),
        };
        term(self.a, &self.scaled[0], j) + term(self.b, &self.scaled[1], j + 1)
    }

    /// Bound the lowest variable at `x`: `eq(z, 2j' + 1) = z_0·eq(z', j')` and `eq(z, 2j' + 2) = (1 + z_0)·eq(z', j' +
    /// 1)`.
    pub fn fold(&self, x: F128) -> Self {
        let z = self.point[0];
        Self::new(
            self.a * (F128::ONE + z + x) + self.b * z * (F128::ONE + x),
            self.b * x * (F128::ONE + z),
            self.point[1..].to_vec(),
        )
    }
}

impl Tail {
    pub fn at(&self, j: usize) -> F128 {
        match self {
            Self::Zero => F128::ZERO,
            Self::Powers { c, ratio } => c.mul_base(ratio.pow(j as u128)),
            Self::Eq(eq) => eq.at(j),
        }
    }

    /// The tail once the lowest variable is bound at `x`.
    pub fn fold(&self, x: F128) -> Self {
        match self {
            Self::Zero => Self::Zero,
            Self::Powers { c, ratio } => Self::Powers {
                c: *c * (F128::ONE + x.mul_base(F64::ONE + *ratio)),
                ratio: ratio.square(),
            },
            Self::Eq(eq) => Self::Eq(eq.fold(x)),
        }
    }
}

/// An array of the summand: its stored entries, then its tail.
pub struct Array {
    pub head: Vec<F128>,
    pub tail: Tail,
}

impl From<Vec<F128>> for Array {
    fn from(head: Vec<F128>) -> Self {
        Self { head, tail: Tail::Zero }
    }
}

impl Array {
    /// The indices, of `size`, where it can be nonzero.
    fn len(&self, size: usize) -> usize {
        match self.tail {
            Tail::Zero => self.head.len(),
            _ => size,
        }
    }

    fn get(&self, j: usize) -> F128 {
        match self.head.get(j) {
            Some(&v) => v,
            None => self.tail.at(j),
        }
    }

    /// The array with its lowest variable bound at `x`.
    fn fold(self, x: F128) -> Self {
        let head = parallel::map_collect(self.head.len().div_ceil(2), |i| {
            let (a0, a1) = (self.head[2 * i], self.get(2 * i + 1));
            a0 + x * (a0 + a1)
        });
        Self {
            head,
            tail: self.tail.fold(x),
        }
    }
}

/// The round polynomial's coefficients over arrays of `size` indices: each term summed over the pairs `2k, 2k + 1`
/// where its arrays can be nonzero, a product as `A·B` at `X = 0`, `1` and `∞`, a single as `A` at `0` and `1`.
fn round_poly(arrays: &[Array], terms: &[Term], size: usize) -> [F128; 3] {
    let lens: Vec<usize> = arrays.iter().map(|a| a.len(size)).collect();
    let pairs: Vec<usize> = (terms.iter())
        .map(|&term| match term {
            Term::Product { a, b, .. } => lens[a].min(lens[b]).div_ceil(2),
            Term::Single { a, .. } => lens[a].div_ceil(2),
        })
        .collect();
    let n_tasks = pairs.iter().max().unwrap_or(&0).div_ceil(TASK_PAIRS);
    let sums = parallel::fold_reduce(
        n_tasks,
        || vec![[F128::ZERO; 3]; terms.len()],
        |acc, task| {
            for ((&term, &end), acc) in terms.iter().zip(&pairs).zip(acc.iter_mut()) {
                for k in task * TASK_PAIRS..end.min((task + 1) * TASK_PAIRS) {
                    match term {
                        Term::Product { a, b, .. } => {
                            let (a0, a1) = (arrays[a].get(2 * k), arrays[a].get(2 * k + 1));
                            let (b0, b1) = (arrays[b].get(2 * k), arrays[b].get(2 * k + 1));
                            acc[0] += a0 * b0;
                            acc[1] += a1 * b1;
                            acc[2] += (a0 + a1) * (b0 + b1);
                        }
                        Term::Single { a, .. } => {
                            acc[0] += arrays[a].get(2 * k);
                            acc[1] += arrays[a].get(2 * k + 1);
                        }
                    }
                }
            }
        },
        |mut x, y| {
            for (x, y) in x.iter_mut().zip(y) {
                for (x, y) in x.iter_mut().zip(y) {
                    *x += y;
                }
            }
            x
        },
    );
    let mut poly = [F128::ZERO; 3];
    for (&term, [lo, hi, mixed]) in terms.iter().zip(sums) {
        match term {
            Term::Product { coef, .. } => {
                poly[0] += coef * lo;
                poly[1] += coef * (lo + hi + mixed);
                poly[2] += coef * mixed;
            }
            Term::Single { coef, .. } => {
                poly[0] += coef * lo;
                poly[1] += coef * (lo + hi);
            }
        }
    }
    poly
}

/// The index side over `n_vars` variables. `round` takes each round polynomial's three coefficients and returns the
/// challenge.
pub fn prove(
    n_vars: usize,
    mut arrays: Vec<Array>,
    terms: &[Term],
    round: &mut dyn FnMut(&[F128]) -> F128,
) -> IndexEnd {
    assert!(
        arrays.iter().all(|a| a.head.len() <= 1 << n_vars),
        "an array past 2^{n_vars}"
    );
    let mut point = Vec::with_capacity(n_vars);
    let mut claim = None;
    for k in 0..n_vars {
        let poly = round_poly(&arrays, terms, 1 << (n_vars - k));
        debug_assert!(claim.is_none_or(|c: F128| c == poly[1] + poly[2]));
        let x = round(&poly);
        claim = Some(poly_eval(&poly, x));
        arrays = arrays.into_iter().map(|a| a.fold(x)).collect();
        point.push(x);
    }
    let values: Vec<F128> = arrays.iter().map(|a| a.get(0)).collect();
    let last = (terms.iter())
        .map(|&term| match term {
            Term::Product { coef, a, b } => coef * values[a] * values[b],
            Term::Single { coef, a } => coef * values[a],
        })
        .sum();
    debug_assert!(claim.is_none_or(|c| c == last));
    IndexEnd {
        point,
        values,
        claim: last,
    }
}

/// Arrays one pass over a pointer column's words adds into, at most.
const MAX_TARGETS: usize = 16;

/// Add each row `u < rows` of `words` at every index of its word ([`Chunks::indices`]), plus a shift, dropping an index
/// whose shift leaves its window ([`Chunks::shifted`]), into several arrays in one pass over the words: row `u` adds
/// `weights(u, ·)[k]` into `targets[k] = (array, shift)`. A zero weight adds nothing.
pub fn add_words(
    chunks: &Chunks,
    words: &[u64],
    rows: usize,
    targets: &[(&Scatter, usize)],
    weights: impl Fn(usize, &mut [F128]) + Sync,
) {
    assert!(rows <= words.len(), "rows past the words");
    assert!(targets.len() <= MAX_TARGETS, "at most {MAX_TARGETS} arrays a pass");
    parallel::for_each(rows, |u| {
        let mut w = [F128::ZERO; MAX_TARGETS];
        let w = &mut w[..targets.len()];
        weights(u, w);
        chunks.indices(words[u], &mut |j| {
            for (&(array, shift), &w) in targets.iter().zip(&*w).filter(|(_, w)| !w.is_zero()) {
                if let Some(j) = chunks.shifted(j, shift) {
                    array.add(j, w);
                }
            }
        });
    });
}

/// An array many rows add into at once: two `u64` limbs per entry, added by XOR (`AtomicU64::fetch_xor`), so the order
/// of the adds does not matter. An index past its length sets `overflow` and adds nothing, so a caller that sized it
/// for the honest indices can redo it at full size.
pub struct Scatter {
    limbs: Vec<AtomicU64>,
    overflow: AtomicBool,
}

impl Scatter {
    /// `len` zero entries.
    pub fn new(len: usize) -> Self {
        Self {
            limbs: parallel::map_collect(2 * len, |_| AtomicU64::new(0)),
            overflow: AtomicBool::new(false),
        }
    }

    /// Whether an index fell past the array.
    pub fn overflowed(&self) -> bool {
        self.overflow.load(Ordering::Relaxed)
    }

    /// Add `value` at entry `j`.
    pub fn add(&self, j: usize, value: F128) {
        let Some(cell) = self.limbs.get(2 * j..2 * j + 2) else {
            self.overflow.store(true, Ordering::Relaxed);
            return;
        };
        for (c, limb) in cell.iter().zip(value.to_limbs()) {
            c.fetch_xor(limb, Ordering::Relaxed);
        }
    }

    /// The entries, without the trailing zeros.
    pub fn into_vec(self) -> Vec<F128> {
        let limbs = self.limbs;
        let mut out = parallel::map_collect(limbs.len() / 2, |j| {
            F128::from_limbs([
                limbs[2 * j].load(Ordering::Relaxed),
                limbs[2 * j + 1].load(Ordering::Relaxed),
            ])
        });
        drop(limbs);
        let len = out.iter().rposition(|v| !v.is_zero()).map_or(0, |j| j + 1);
        out.truncate(len);
        out
    }
}

#[cfg(test)]
mod tests {
    use super::super::pointer::{ChunkEq, Shifts, eval_chunk};
    use super::*;
    use primitives::field::index_mle;
    use primitives::multilinear::{eq_eval, eq_table};
    use primitives::test_rng::Rng;

    impl Scatter {
        /// Add `weight(u)` at the index of each row `u < rows` of `words`, plus `shift`, dropping an index whose shift
        /// leaves its window ([`Chunks::shifted`]). A word whose chunks are not all one-hot adds at every index of it
        /// ([`Chunks::indices`]), which is what the row side's pointer of that word sums to. A row of zero weight adds
        /// nothing.
        fn add_words(
            &self,
            chunks: &Chunks,
            words: &[u64],
            rows: usize,
            shift: usize,
            weight: impl Fn(usize) -> F128 + Sync,
        ) {
            super::add_words(chunks, words, rows, &[(self, shift)], |u, w| w[0] = weight(u));
        }
    }

    fn mle(a: &[F128], point: &[F128]) -> F128 {
        eq_table(point).iter().zip(a).map(|(&e, &v)| e * v).sum()
    }

    fn at(v: &[F128], j: usize) -> F128 {
        v.get(j).copied().unwrap_or(F128::ZERO)
    }

    /// `j`'s bits as a point of `n` coordinates.
    fn bits(j: usize, n: usize) -> Vec<F128> {
        (0..n)
            .map(|h| if j >> h & 1 == 1 { F128::ONE } else { F128::ZERO })
            .collect()
    }

    /// The verifier's `shift_eq` (`crates/verifier/src/link.rs`): `Σ_j eq(r, j)·eq(ζ, j + 1)` over `j + 1 < 2^n`.
    fn shift_eq(zeta: &[F128], r: &[F128]) -> F128 {
        let (mut shift, mut carry) = (F128::ZERO, F128::ONE);
        for (&z, &x) in zeta.iter().zip(r) {
            shift = shift * (F128::ONE + z + x) + carry * (F128::ONE + x) * z;
            carry *= x * (F128::ONE + z);
        }
        shift
    }

    /// Every index of a word, by trying each: an index whose every chunk has its digit's bit set.
    fn naive_indices(chunks: &Chunks, word: u64) -> Vec<usize> {
        (0..1 << chunks.width)
            .filter(|&sigma| (0..chunks.d()).all(|i| chunks.bits(word, i) >> chunks.digit(sigma, i) & 1 == 1))
            .collect()
    }

    #[test]
    fn a_scatter_flags_an_index_past_its_length() {
        let chunks = Chunks::new(9);
        let words: Vec<u64> = [3, 7, 2].iter().map(|&s| chunks.encode(s)).collect();
        let fits = Scatter::new(8);
        fits.add_words(&chunks, &words, 3, 0, |_| F128::ONE);
        assert!(!fits.overflowed());
        let short = Scatter::new(7);
        short.add_words(&chunks, &words, 3, 0, |_| F128::ONE);
        assert!(short.overflowed());
        assert_eq!(short.into_vec(), [0, 0, 1, 1].map(|b| F128::new(b, 0)));
        // A row past `rows`, or of zero weight, adds nothing.
        let first = Scatter::new(7);
        first.add_words(&chunks, &words, 1, 0, |_| F128::ONE);
        first.add_words(&chunks, &words, 3, 0, |u| if u == 1 { F128::ZERO } else { F128::ONE });
        assert!(!first.overflowed());
        assert_eq!(first.into_vec(), [0, 0, 1].map(|b| F128::new(b, 0)));
    }

    #[test]
    fn index_side_matches_the_naive_sum_and_end() {
        let mut rng = Rng::new(0x1d5);
        let n = 9;
        let lens = [512usize, 300, 1, 0, 37, 512, 2, 257];
        let arrays: Vec<Vec<F128>> = lens.iter().map(|&l| rng.ext_vec(l)).collect();
        let terms = [(0, 1), (2, 1), (3, 0), (4, 5), (6, 7), (7, 7)]
            .map(|(a, b)| Term::Product { coef: rng.ext(), a, b })
            .into_iter()
            .chain([
                Term::Single { coef: rng.ext(), a: 2 },
                Term::Single { coef: rng.ext(), a: 7 },
            ])
            .collect::<Vec<_>>();
        let value = |values: &dyn Fn(usize) -> F128| -> F128 {
            (terms.iter())
                .map(|&t| match t {
                    Term::Product { coef, a, b } => coef * values(a) * values(b),
                    Term::Single { coef, a } => coef * values(a),
                })
                .sum()
        };
        let mut claim: F128 = (0..1 << n).map(|j| value(&|a| at(&arrays[a], j))).sum();
        let end = prove(
            n,
            arrays.iter().cloned().map(Array::from).collect(),
            &terms,
            &mut |poly| {
                assert_eq!(poly.len(), 3);
                assert_eq!(claim, poly[1] + poly[2], "a round's sum");
                let x = rng.ext();
                claim = poly_eval(poly, x);
                x
            },
        );
        assert_eq!(claim, end.claim);
        for (a, &v) in arrays.iter().zip(&end.values) {
            assert_eq!(mle(a, &end.point), v);
        }
        assert_eq!(end.claim, value(&|a| end.values[a]));
    }

    /// At every size, from no variable up, an eq tail holds `a·eq(j) + b·eq(j + 1)`, and arrays with zero, powers and
    /// both eq tail forms, stored up to any length, prove as the arrays they stand for.
    #[test]
    fn tails_prove_as_their_stored_arrays_at_every_size() {
        for n in [0usize, 1, 2, 3, 4, 5, 6, 7, 8, 11] {
            let mut rng = Rng::new(0x7a1 + n as u64);
            let size = 1usize << n;
            let (c, zeta) = (rng.ext(), rng.ext_vec(n));
            let tails = [
                Tail::Zero,
                Tail::Eq(ShiftEq::new(c, rng.ext(), zeta.clone())),
                Tail::Eq(ShiftEq::new(F128::ZERO, F128::ONE, zeta.clone())),
                Tail::Eq(ShiftEq::new(c, F128::ZERO, zeta.clone())),
                Tail::Powers {
                    c,
                    ratio: F64::G.pow(5),
                },
            ];
            let eq = eq_table(&zeta);
            for j in 0..size {
                assert_eq!(tails[2].at(j), at(&eq, j + 1), "n {n}, j {j}");
                assert_eq!(tails[3].at(j), c * eq[j], "n {n}, j {j}");
            }
            let lens = [
                (0, size),
                (0, size / 2 + 1),
                (0, 3),
                (1, 0),
                (2, 0),
                (1, 5),
                (3, 0),
                (0, size - 1),
                (0, 1),
                (4, 0),
                (4, 3),
            ];
            let heads: Vec<Array> = (lens.iter())
                .map(|&(t, len)| {
                    let tail = &tails[t];
                    let head: Vec<F128> = (0..len.min(size))
                        .map(|j| if t == 0 || j % 7 == 3 { rng.ext() } else { tail.at(j) })
                        .collect();
                    Array {
                        head,
                        tail: tail.clone(),
                    }
                })
                .collect();
            let full: Vec<Vec<F128>> = (heads.iter())
                .map(|a| match a.tail {
                    Tail::Zero => a.head.clone(),
                    _ => (0..size).map(|j| a.get(j)).collect(),
                })
                .collect();
            let terms = [
                (3, 0),
                (4, 0),
                (1, 4),
                (4, 1),
                (5, 2),
                (4, 7),
                (8, 3),
                (4, 6),
                (3, 8),
                (4, 4),
                (9, 10),
                (9, 5),
            ]
            .map(|(a, b)| Term::Product { coef: rng.ext(), a, b })
            .into_iter()
            .chain([
                Term::Single { coef: rng.ext(), a: 4 },
                Term::Single { coef: rng.ext(), a: 9 },
            ])
            .collect::<Vec<_>>();
            let run = |arrays: Vec<Array>| {
                let (mut rng, mut polys) = (Rng::new(0x7a2), Vec::new());
                let end = prove(n, arrays, &terms, &mut |poly| {
                    polys.push(poly.to_vec());
                    rng.ext()
                });
                (polys, end.values, end.claim)
            };
            let stored = run(full.into_iter().map(Array::from).collect());
            assert_eq!(run(heads), stored, "n {n}");
        }
    }

    /// `ShiftEq` is `a·eq(z, j) + b·eq(z, j + 1)`, and its fold is that array's fold at every index.
    #[test]
    fn shift_eq_folds_as_its_naive_array() {
        let mut rng = Rng::new(0x5f0);
        for n in 1..8 {
            let (a, b, z, x) = (rng.ext(), rng.ext(), rng.ext_vec(n), rng.ext());
            let shift = ShiftEq::new(a, b, z.clone());
            let naive = |j: usize| {
                let next = if j + 1 < 1 << n {
                    b * eq_eval(&z, &bits(j + 1, n))
                } else {
                    F128::ZERO
                };
                a * eq_eval(&z, &bits(j, n)) + next
            };
            for j in 0..1 << n {
                assert_eq!(shift.at(j), naive(j), "n {n}, j {j}");
            }
            let folded = shift.fold(x);
            for j in 0..1 << (n - 1) {
                let (f0, f1) = (naive(2 * j), naive(2 * j + 1));
                assert_eq!(folded.at(j), f0 + x * (f0 + f1), "n {n}, j {j}");
            }
        }
    }

    /// All-tail arrays end at the verifier's values: `eq(ζ, r)`, `shift_eq(ζ, r)` and `c·Σ_j eq(r, j)·g^j`.
    #[test]
    fn tails_end_at_the_verifiers_values() {
        let mut rng = Rng::new(0xe9d);
        for n in [0usize, 1, 2, 5, 10] {
            let (zeta, c) = (rng.ext_vec(n), rng.ext());
            let arrays = vec![
                Array {
                    head: Vec::new(),
                    tail: Tail::Eq(ShiftEq::new(F128::ONE, F128::ZERO, zeta.clone())),
                },
                Array {
                    head: Vec::new(),
                    tail: Tail::Eq(ShiftEq::new(F128::ZERO, F128::ONE, zeta.clone())),
                },
                Array {
                    head: Vec::new(),
                    tail: Tail::Powers { c, ratio: F64::G },
                },
            ];
            let terms = [0, 1, 2].map(|a| Term::Single { coef: F128::ONE, a });
            let end = prove(n, arrays, &terms, &mut |_| rng.ext());
            let r = &end.point;
            assert_eq!(end.values[0], eq_eval(&zeta, r), "n {n}");
            assert_eq!(end.values[1], shift_eq(&zeta, r), "n {n}");
            assert_eq!(end.values[2], c * index_mle(r), "n {n}");
        }
    }

    /// A scattered array at a point is the sum of its rows' `Φ_s` there, for any words: a read past its window drops
    /// on both sides.
    #[test]
    fn scatter_is_the_row_side_pointer() {
        let mut rng = Rng::new(0x5ca);
        for width in [3usize, 7, 10, 13] {
            let chunks = Chunks::new(width);
            let top = 1usize << width;
            let words: Vec<u64> = (0..300)
                .map(|u| {
                    let sigma = if u % 10 == 0 {
                        top - 1
                    } else {
                        rng.next_u64() as usize % top
                    };
                    let word = chunks.encode(sigma);
                    match u % 9 {
                        0 => word ^ 1 << (rng.next_u64() % 64),
                        1 => word | rng.next_u64() & rng.next_u64(),
                        _ => word,
                    }
                })
                .collect();
            let weights: Vec<F128> = (0..words.len())
                .map(|u| if u % 13 == 0 { F128::ZERO } else { rng.ext() })
                .collect();
            let r = rng.ext_vec(width);
            let eq = ChunkEq::at(&chunks, &r);
            let shifts = Shifts::new(&eq, 12);
            for shift in [0, 1, 5, 12] {
                let scatter = Scatter::new(top);
                scatter.add_words(&chunks, &words, words.len(), shift, |u| weights[u]);
                let array = scatter.into_vec();
                let rows: F128 = (words.iter().zip(&weights))
                    .map(|(&w, &weight)| {
                        let rest: F128 = (1..chunks.d()).map(|i| eq.eval(&chunks, w, i)).product();
                        weight * eval_chunk(&chunks, &shifts.tables[shift], w, 0) * rest
                    })
                    .sum();
                assert_eq!(mle(&array, &r), rows, "width {width}, shift {shift}");
            }
        }
    }

    /// One-hot, not one-hot and window-shifted words scatter as the sum, over each row and each index of its word
    /// found by trying every index, of the row's weight at the index plus the shift, past the window dropped.
    #[test]
    fn scatter_is_the_naive_sum_over_indices() {
        let mut rng = Rng::new(0x5cb);
        for width in [1usize, 4, 9, 12] {
            let chunks = Chunks::new(width);
            let (top, window) = (1usize << width, 1usize << chunks.widths[0]);
            let words: Vec<u64> = (0..400)
                .map(|u| {
                    let word = chunks.encode(rng.next_u64() as usize % top);
                    match u % 5 {
                        0 => word | rng.next_u64() & rng.next_u64() & rng.next_u64(),
                        1 => word ^ 1 << (rng.next_u64() % 64),
                        2 => rng.next_u64(),
                        _ => word,
                    }
                })
                .collect();
            let weights: Vec<F128> = (0..words.len()).map(|_| rng.ext()).collect();
            let rows = words.len() - 7;
            for shift in [0, 1, 3, window - 1, window] {
                let mut naive = vec![F128::ZERO; top + window];
                for (&word, &w) in words.iter().zip(&weights).take(rows) {
                    for sigma in naive_indices(&chunks, word) {
                        if sigma % window + shift < window {
                            naive[sigma + shift] += w;
                        }
                    }
                }
                let len = naive.iter().rposition(|v| !v.is_zero()).map_or(0, |j| j + 1);
                naive.truncate(len);
                let scatter = Scatter::new(top);
                scatter.add_words(&chunks, &words, rows, shift, |u| weights[u]);
                assert!(!scatter.overflowed());
                assert_eq!(scatter.into_vec(), naive, "width {width}, shift {shift}");
            }
        }
    }
}
