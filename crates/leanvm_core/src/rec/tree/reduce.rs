//! The per-node claim reduction: the claims a node's children leave on each fixed polynomial become one, at one
//! point all of them share, by sumchecks the circuit verifies and the node's prover answers.
//!
//! The dense reduction takes claims `Σ_t c_t·P(p_t) = v` on the dense polynomials (the program's stacked bytecode
//! table, RAM's image, the recursion circuits' fixed columns), batched by the powers of one challenge, to `P` at a
//! prefix of one point, by one degree-two sumcheck in which a polynomial of fewer variables waits on the high ones
//! (`constraints`' back-loaded batching, the low variables bound first here). The matrix reduction takes bilinear
//! claims `uᵀ(a·A + b·B)w = v` on each flock circuit's matrices to `A` and `B` at one row and one column point,
//! by a row phase over `u` and then a column phase over `w` (Spartan's second sumcheck), every circuit sharing the
//! challenges.

use crate::class_flock;
use crate::rec::circuit::{Builder, Ew};
use crate::rec::inner::flock::skip_weighted_sum;
use crate::rec::inner::math::{self, poly_eval};
use crate::rec::transcript::Transcript;
use flock::lincheck::{LincheckCircuit, build_quirky_eq_table};
use flock::zerocheck::K_SKIP;
use primitives::field::{F64, F192};
use primitives::multilinear::{eq_table, mle_eval_par};
use std::collections::BTreeMap;

/// What a test makes the prover forge: reduced values that satisfy the final identity and are false.
#[cfg(test)]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum Forge {
    None,
    Dense,
    Matrix,
}

#[cfg(test)]
thread_local! {
    pub(crate) static FORGE: std::cell::Cell<Forge> = const { std::cell::Cell::new(Forge::None) };
}

/// Make `values` satisfy `Σ_i coefs_i·values_i = claim` through the first, then move the first two against
/// each other along it: a prover passing on a false claim, and making one.
#[cfg(test)]
fn forge(values: &mut [F192], coefs: &[F192], claim: F192) {
    let rest = (values.iter().zip(coefs).skip(1)).fold(F192::ZERO, |acc, (&v, &c)| acc + v * c);
    values[0] = (claim + rest) * coefs[0].inv();
    let delta = F192::new(1, 2, 3);
    values[0] += delta;
    values[1] += delta * coefs[0] * coefs[1].inv();
}

/// `acc·x`, an absent `acc` being one.
fn times(b: &mut Builder, acc: Option<Ew>, x: Ew) -> Ew {
    acc.map_or(x, |a| b.mul(a, x))
}

/// `acc·eq(p, x)` for one coordinate.
fn times_eq(b: &mut Builder, acc: Option<Ew>, p: Ew, x: Ew) -> Ew {
    let s = b.add(p, x);
    match acc {
        Some(a) => math::times_one_plus(b, a, s),
        None => b.add_const(s, F192::ONE),
    }
}

/// `acc·eq(bit, x)` for a Boolean `bit`.
fn times_bit(b: &mut Builder, acc: Option<Ew>, bit: bool, x: Ew) -> Ew {
    match (bit, acc) {
        (true, _) => times(b, acc, x),
        (false, Some(a)) => math::times_one_plus(b, a, x),
        (false, None) => b.add_const(x, F192::ONE),
    }
}

/// `Π_j eq(p_j, x_j)`.
fn eq_eval(b: &mut Builder, p: &[Ew], x: &[Ew]) -> Option<Ew> {
    assert_eq!(p.len(), x.len());
    p.iter().zip(x).fold(None, |acc, (&p, &x)| Some(times_eq(b, acc, p, x)))
}

/// `Π_{j ≥ from} x_j`, the weight a polynomial of `from` variables waits on the higher ones with.
fn lift(b: &mut Builder, x: &[Ew], from: usize) -> Option<Ew> {
    x[from..].iter().fold(None, |acc, &x| Some(times(b, acc, x)))
}

/// One degree-two round: `c0` and `c2` sent and bound, `c1` from the running claim `h(0) + h(1)`.
fn round(b: &mut Builder, t: &mut Transcript, claim: Ew, c0: F192, c2: F192) -> (Ew, Ew) {
    let c0 = b.free_e(c0);
    let c2 = b.free_e(c2);
    t.observe(b, c0);
    t.observe(b, c2);
    let r = t.sample(b);
    let c1 = b.add(claim, c2);
    (r, poly_eval(b, &[c0, c1, c2], r))
}

/// `Σ_c γ^c·v_c`, and the powers.
fn batch(b: &mut Builder, gamma: Ew, values: &[Ew]) -> (Ew, Vec<Ew>) {
    let powers = math::powers(b, gamma, values.len());
    let zero = b.zero();
    (b.dot(&powers, values, zero), powers)
}

/// The values of `ws`.
fn values(b: &Builder, ws: &[Ew]) -> Vec<F192> {
    ws.iter().map(|&w| b.e(w)).collect()
}

/// Pairs a sumcheck folds together, one pair per claim.
type Tables = Vec<(Vec<F192>, Vec<F192>)>;

/// The entries one task of a parallel pass takes; a shorter pass stays on the calling thread.
const CHUNK: usize = 1 << 12;

/// `Σ_{k < n} f(k)` over pairs of elements, across the pool when long.
fn sum_pairs(n: usize, f: impl Fn(usize) -> (F192, F192) + Sync) -> (F192, F192) {
    let add = |(a, b): (F192, F192), (c, d): (F192, F192)| (a + c, b + d);
    let task = |i: usize| {
        (i * CHUNK..n.min((i + 1) * CHUNK))
            .map(&f)
            .fold((F192::ZERO, F192::ZERO), add)
    };
    if n <= CHUNK {
        return task(0);
    }
    parallel::map_reduce(n.div_ceil(CHUNK), || (F192::ZERO, F192::ZERO), task, add)
}

/// The table of `f(k)` for `k < n`, written across the pool when long.
fn table_of(n: usize, f: impl Fn(usize) -> F192 + Sync) -> Vec<F192> {
    if n <= CHUNK {
        return (0..n).map(f).collect();
    }
    let mut out = Vec::with_capacity(n);
    parallel::chunks_mut(&mut out.spare_capacity_mut()[..n], CHUNK, |i, dst| {
        for (j, slot) in dst.iter_mut().enumerate() {
            slot.write(f(i * CHUNK + j));
        }
    });
    // SAFETY: the chunks cover all `n` entries, each written once.
    unsafe { out.set_len(n) };
    out
}

/// `h(0)` and the leading coefficient of `Σ_k u(X, k)·g(X, k)` over the lowest variable, for tables of even length.
fn products(u: &[F192], g: &[F192]) -> (F192, F192) {
    sum_pairs(u.len() / 2, |k| {
        let (u0, u1, g0, g1) = (u[2 * k], u[2 * k + 1], g[2 * k], g[2 * k + 1]);
        (u0 * g0, (u0 + u1) * (g0 + g1))
    })
}

/// [`products`] for a `g` in the base field.
fn products_base(u: &[F192], g: &[F64]) -> (F192, F192) {
    sum_pairs(u.len() / 2, |k| {
        let (u0, u1, g0, g1) = (u[2 * k], u[2 * k + 1], g[2 * k], g[2 * k + 1]);
        (u0.mul_base(g0), (u0 + u1).mul_base(g0 + g1))
    })
}

/// Bind the lowest variable of `table` to `r`.
fn fold(table: &mut Vec<F192>, r: F192) {
    let t = &*table;
    let next = table_of(t.len() / 2, |k| t[2 * k] + r * (t[2 * k] + t[2 * k + 1]));
    *table = next;
}

/// [`fold`] for a table in the base field.
fn fold_base(table: &[F64], r: F192) -> Vec<F192> {
    table_of(table.len() / 2, |k| {
        r.mul_base(table[2 * k] + table[2 * k + 1]) + F192::from(table[2 * k])
    })
}

/// A dense polynomial the reduction's prover folds: its table in the base field until a round binds a variable.
enum Poly<'a> {
    Base(&'a [F64]),
    Ext(Vec<F192>),
}

impl Poly<'_> {
    fn products(&self, weights: &[F192]) -> (F192, F192) {
        match self {
            Self::Base(p) => products_base(weights, p),
            Self::Ext(p) => products(weights, p),
        }
    }

    fn fold(&mut self, r: F192) {
        match self {
            Self::Base(p) => *self = Self::Ext(fold_base(p, r)),
            Self::Ext(p) => fold(p, r),
        }
    }

    fn first(&self) -> F192 {
        match self {
            Self::Base(p) => F192::from(p[0]),
            Self::Ext(p) => p[0],
        }
    }
}

/// One term of a dense claim: `coef·P(low[..n_low] ‖ bits ‖ top)`, `coef` one when absent.
pub struct Term {
    pub coef: Option<Ew>,
    pub n_low: usize,
    pub bits: Vec<bool>,
    pub top: Vec<Ew>,
}

/// `Σ_t terms_t = value` on dense polynomial `poly`, the terms' points sharing the prefix `low`.
pub struct DenseClaim {
    pub poly: usize,
    pub low: Vec<Ew>,
    pub terms: Vec<Term>,
    pub value: Ew,
}

impl DenseClaim {
    /// `P(point) = value`.
    pub fn at(poly: usize, point: Vec<Ew>, value: Ew) -> Self {
        let n_low = point.len();
        Self {
            poly,
            low: point,
            terms: vec![Term {
                coef: None,
                n_low,
                bits: Vec::new(),
                top: Vec::new(),
            }],
            value,
        }
    }

    /// The terms of `scale` times this claim's weight, each placed in the polynomial's table by the Boolean suffix
    /// of its point.
    fn placed(&self, b: &Builder, scale: F192) -> Vec<Placed> {
        let boolean = |x: &F192| *x == F192::ZERO || *x == F192::ONE;
        let low = values(b, &self.low);
        self.terms
            .iter()
            .map(|t| {
                let mut point = low[..t.n_low].to_vec();
                point.extend(t.bits.iter().map(|&bit| F192::from(F64(u64::from(bit)))));
                point.extend(values(b, &t.top));
                let k = point.len() - point.iter().rev().take_while(|x| boolean(x)).count();
                let offset = (point[k..].iter().enumerate())
                    .map(|(i, &x)| usize::from(x == F192::ONE) << (k + i))
                    .sum();
                point.truncate(k);
                Placed {
                    coef: scale * t.coef.map_or(F192::ONE, |c| b.e(c)),
                    point,
                    offset,
                }
            })
            .collect()
    }

    /// `Σ_t coef_t·eq(p_t, r)`.
    fn weight(&self, b: &mut Builder, r: &[Ew]) -> Ew {
        let n = self.terms.iter().map(|t| t.n_low).max().unwrap_or(0);
        let mut prefix: Vec<Option<Ew>> = vec![None];
        for j in 0..n {
            let next = times_eq(b, prefix[j], self.low[j], r[j]);
            prefix.push(Some(next));
        }
        let mut total = b.zero();
        for term in &self.terms {
            let mut acc = prefix[term.n_low];
            for (i, &bit) in term.bits.iter().enumerate() {
                acc = Some(times_bit(b, acc, bit, r[term.n_low + i]));
            }
            let at = term.n_low + term.bits.len();
            for (i, &x) in term.top.iter().enumerate() {
                acc = Some(times_eq(b, acc, x, r[at + i]));
            }
            assert_eq!(
                at + term.top.len(),
                r.len(),
                "a term's point has its polynomial's variables"
            );
            let eq = acc.unwrap_or_else(|| b.one());
            total = match term.coef {
                Some(c) => b.mul_add(c, eq, total),
                None => b.add(eq, total),
            };
        }
        total
    }
}

/// One term of the prover's weight table: `coef·eq(point, ·)` at `offset`.
struct Placed {
    coef: F192,
    point: Vec<F192>,
    offset: usize,
}

/// The variables of the low eq tables [`add_eqs`] keeps in L1.
const LOW_VARS: usize = 10;

/// `table[offset + x] += Σ_t coef_t·eq(p_t, x)` for terms of one offset and size, in one pass over the table: each
/// term's eq table is the tensor of a low one and a high one scaled by its coefficient.
fn add_eqs(table: &mut [F192], terms: &[&Placed]) {
    let k = terms[0].point.len();
    let l = k.min(LOW_VARS);
    let lows: Vec<Vec<F192>> = terms.iter().map(|t| eq_table(&t.point[..l])).collect();
    let highs: Vec<Vec<F192>> = (terms.iter())
        .map(|t| eq_table(&t.point[l..]).into_iter().map(|e| e * t.coef).collect())
        .collect();
    let row = |h: usize, dst: &mut [F192]| {
        for (low, high) in lows.iter().zip(&highs) {
            for (slot, &e) in dst.iter_mut().zip(low) {
                *slot += high[h] * e;
            }
        }
    };
    let offset = terms[0].offset;
    let dst = &mut table[offset..offset + (1 << k)];
    if dst.len() <= CHUNK {
        dst.chunks_mut(1 << l).enumerate().for_each(|(h, d)| row(h, d));
    } else {
        parallel::chunks_mut(dst, 1 << l, row);
    }
}

/// The reduced dense claims: the shared point, and each polynomial's value at its prefix.
pub struct Dense {
    pub point: Vec<Ew>,
    pub values: Vec<Ew>,
}

/// Reduce `claims` on the dense polynomials of `n_vars` variables each to one point. `tables` are the polynomials,
/// which only the prover holds.
pub fn reduce_dense(
    b: &mut Builder,
    t: &mut Transcript,
    n_vars: &[usize],
    tables: Option<&[&[F64]]>,
    claims: &[DenseClaim],
) -> Dense {
    let n = n_vars.iter().copied().max().unwrap_or(0);
    let gamma = t.sample(b);
    let claim_values: Vec<Ew> = claims.iter().map(|c| c.value).collect();
    let (mut claim, powers) = batch(b, gamma, &claim_values);

    // A polynomial no claim weighs is not folded: its value is one evaluation at the end.
    let mut state = tables.map(|tables| {
        let mut terms: Vec<Vec<Placed>> = (0..n_vars.len()).map(|_| Vec::new()).collect();
        for (c, &g) in claims.iter().zip(&powers) {
            terms[c.poly].extend(c.placed(b, b.e(g)));
        }
        let weights: Vec<Option<Vec<F192>>> = (terms.iter().zip(n_vars))
            .map(|(terms, &k)| {
                (!terms.is_empty()).then(|| {
                    let mut regions: BTreeMap<(usize, usize), Vec<&Placed>> = BTreeMap::new();
                    for t in terms {
                        regions.entry((t.offset, t.point.len())).or_default().push(t);
                    }
                    let mut w = table_of(1 << k, |_| F192::ZERO);
                    for region in regions.values() {
                        add_eqs(&mut w, region);
                    }
                    w
                })
            })
            .collect();
        let polys: Vec<Poly> = tables.iter().map(|&p| Poly::Base(p)).collect();
        (polys, weights)
    });

    let mut point = Vec::with_capacity(n);
    for i in 0..n {
        let (c0, c2) = state.as_ref().map_or((F192::ZERO, F192::ZERO), |(polys, weights)| {
            (polys.iter().zip(weights).zip(n_vars))
                .filter(|&(_, &k)| k > i)
                .filter_map(|((p, w), _)| w.as_ref().map(|w| p.products(w)))
                .fold((F192::ZERO, F192::ZERO), |(c0, c2), (a, c)| (c0 + a, c2 + c))
        });
        let (r, next) = round(b, t, claim, c0, c2);
        claim = next;
        if let Some((polys, weights)) = &mut state {
            let rv = b.e(r);
            for ((p, w), &k) in polys.iter_mut().zip(weights.iter_mut()).zip(n_vars) {
                if let (true, Some(w)) = (k > i, w) {
                    p.fold(rv);
                    fold(w, rv);
                }
            }
        }
        point.push(r);
    }

    #[cfg_attr(not(test), expect(unused_mut, reason = "a test forges the values"))]
    let mut native: Vec<F192> = (0..n_vars.len())
        .map(|j| {
            state
                .as_ref()
                .map_or(F192::ZERO, |(polys, weights)| match (&weights[j], &polys[j]) {
                    (None, Poly::Base(p)) => mle_eval_par(p, &values(b, &point[..n_vars[j]])),
                    (_, p) => p.first(),
                })
        })
        .collect();
    #[cfg(test)]
    if let (Forge::Dense, Some((_, weights))) = (FORGE.get(), &state) {
        let rv = values(b, &point);
        let coefs: Vec<F192> = (0..n_vars.len())
            .map(|j| {
                let w = weights[j].as_ref().map_or(F192::ZERO, |w| w[0]);
                rv[n_vars[j]..].iter().fold(w, |acc, &x| acc * x)
            })
            .collect();
        forge(&mut native, &coefs, b.e(claim));
    }
    let reduced: Vec<Ew> = native.iter().map(|&x| b.free_e(x)).collect();
    let mut total = b.zero();
    for (j, &k) in n_vars.iter().enumerate() {
        let mut omega = b.zero();
        for (c, &g) in claims.iter().zip(&powers).filter(|(c, _)| c.poly == j) {
            let w = c.weight(b, &point[..k]);
            omega = b.mul_add(g, w, omega);
        }
        let weighted = lift(b, &point[..n], k).map_or(omega, |l| b.mul(omega, l));
        total = b.mul_add(weighted, reduced[j], total);
    }
    b.scope("dense reduction", |b| b.eq_e(claim, total));
    Dense { point, values: reduced }
}

/// A claim's row weight: flock's quirky eq at a zerocheck point, or `eq(p, ·)`.
pub enum Row {
    Quirky { z: Ew, rest: Vec<Ew> },
    Point(Vec<Ew>),
}

/// A claim's column weight: `eq(rest, ·) ⊗ slices`, lincheck's output, or `eq(p, ·)`.
pub enum Col {
    Slices { slices: Vec<Ew>, rest: Vec<Ew> },
    Point(Vec<Ew>),
}

/// A matrix's weight in a claim.
#[derive(Clone, Copy)]
pub enum Weight {
    Zero,
    One,
    W(Ew),
}

impl Weight {
    fn value(self, b: &Builder) -> F192 {
        match self {
            Self::Zero => F192::ZERO,
            Self::One => F192::ONE,
            Self::W(w) => b.e(w),
        }
    }

    fn times(self, b: &mut Builder, x: Ew, acc: Ew) -> Ew {
        match self {
            Self::Zero => acc,
            Self::One => b.add(x, acc),
            Self::W(w) => b.mul_add(w, x, acc),
        }
    }
}

/// `uᵀ(a·A + b·B)w = value` on flock circuit `circuit`'s matrices.
pub struct MatrixClaim {
    pub circuit: usize,
    pub row: Row,
    pub col: Col,
    pub weights: [Weight; 2],
    pub value: Ew,
}

impl Row {
    fn table(&self, b: &Builder) -> Vec<F192> {
        match self {
            Self::Quirky { z, rest } => build_quirky_eq_table(b.e(*z), &values(b, rest), K_SKIP),
            Self::Point(p) => eq_table(&values(b, p)),
        }
    }

    /// The weight's multilinear extension at `r`, `skip` being `eq(r[..K_SKIP], ·)`.
    fn eval(&self, b: &mut Builder, r: &[Ew], skip: &[Ew]) -> Ew {
        match self {
            Self::Quirky { z, rest } => {
                let low = skip_weighted_sum(b, *z, skip);
                let high = eq_eval(b, rest, &r[K_SKIP..]);
                times(b, high, low)
            }
            Self::Point(p) => eq_eval(b, p, r).unwrap_or_else(|| b.one()),
        }
    }
}

impl Col {
    fn table(&self, b: &Builder) -> Vec<F192> {
        match self {
            Self::Slices { slices, rest } => {
                let slices = values(b, slices);
                eq_table(&values(b, rest))
                    .into_iter()
                    .flat_map(|h| slices.iter().map(move |&s| s * h))
                    .collect()
            }
            Self::Point(p) => eq_table(&values(b, p)),
        }
    }

    fn eval(&self, b: &mut Builder, s: &[Ew], skip: &[Ew]) -> Ew {
        match self {
            Self::Slices { slices, rest } => {
                let zero = b.zero();
                let low = b.dot(slices, skip, zero);
                let high = eq_eval(b, rest, &s[K_SKIP..]);
                times(b, high, low)
            }
            Self::Point(p) => eq_eval(b, p, s).unwrap_or_else(|| b.one()),
        }
    }
}

/// The reduced matrix claims: one row point and one column point, and each circuit's `A` and `B` at their
/// prefixes of its size.
pub struct Matrices {
    pub rows: Vec<Ew>,
    pub cols: Vec<Ew>,
    pub values: Vec<[Ew; 2]>,
}

/// The largest circuit's `k_log`: the reduction's variables in each phase.
pub fn matrix_vars() -> usize {
    (0..class_flock::N_FLOCKS)
        .map(|f| class_flock::shape(f).k_log)
        .max()
        .expect("a circuit")
}

/// Reduce `claims` on the flock circuits' matrices to one row and one column point; `honest` when the builder
/// holds a real assignment, whose prover messages are computed.
pub fn reduce_matrices(b: &mut Builder, t: &mut Transcript, honest: bool, claims: &[MatrixClaim]) -> Matrices {
    let k_max = matrix_vars();
    let n_circuits = class_flock::N_FLOCKS;
    let ks: Vec<usize> = (0..n_circuits).map(|f| class_flock::shape(f).k_log).collect();
    let gamma = t.sample(b);
    let claim_values: Vec<Ew> = claims.iter().map(|c| c.value).collect();
    let (mut claim, powers) = batch(b, gamma, &claim_values);

    // Per circuit, per claim: `γ^c·u` and `g = (a·A + b·B)·w`.
    let mut rows_state: Option<Vec<Tables>> = honest.then(|| {
        let mut state: Vec<Tables> = vec![Vec::new(); n_circuits];
        for (c, &g) in claims.iter().zip(&powers) {
            let gv = b.e(g);
            let u: Vec<F192> = c.row.table(b).into_iter().map(|x| gv * x).collect();
            let (ra, rb) = class_flock::circuit(c.circuit).row_values(&c.col.table(b));
            let [wa, wb] = c.weights.map(|w| w.value(b));
            let g = ra.iter().zip(&rb).map(|(&x, &y)| wa * x + wb * y).collect();
            state[c.circuit].push((u, g));
        }
        state
    });
    let mut r = Vec::with_capacity(k_max);
    for i in 0..k_max {
        let (c0, c2) = rows_state.as_ref().map_or((F192::ZERO, F192::ZERO), |state| {
            (state.iter().zip(&ks))
                .filter(|&(_, &k)| k > i)
                .flat_map(|(s, _)| s)
                .fold((F192::ZERO, F192::ZERO), |(c0, c2), (u, g)| {
                    let (a, c) = products(u, g);
                    (c0 + a, c2 + c)
                })
        });
        let (ri, next) = round(b, t, claim, c0, c2);
        claim = next;
        if let Some(state) = &mut rows_state {
            let rv = b.e(ri);
            for (s, &k) in state.iter_mut().zip(&ks) {
                if k > i {
                    for (u, g) in s {
                        fold(u, rv);
                        fold(g, rv);
                    }
                }
            }
        }
        r.push(ri);
    }

    // The column phase: per circuit, `A(r, ·)`, `B(r, ·)` and their weights `Σ_c γ^c·u_c(r)·a_c·w_c`, lifted.
    let mut cols_state: Option<Vec<[Vec<F192>; 4]>> = rows_state.map(|state| {
        let rv = values(b, &r);
        (0..n_circuits)
            .map(|f| {
                let k = ks[f];
                let lambda = rv[k..].iter().fold(F192::ONE, |acc, &x| acc * x);
                let circuit = class_flock::circuit(f);
                let eq = eq_table(&rv[..k]);
                let at = circuit.fold_alpha_batched(F192::ZERO, &eq);
                let both = circuit.fold_alpha_batched(F192::ONE, &eq);
                let bt: Vec<F192> = at.iter().zip(&both).map(|(&x, &y)| x + y).collect();
                let (mut wa, mut wb) = (vec![F192::ZERO; 1 << k], vec![F192::ZERO; 1 << k]);
                for (c, (u, _)) in claims.iter().filter(|c| c.circuit == f).zip(&state[f]) {
                    let [a, bw] = c.weights.map(|w| w.value(b));
                    let scale = lambda * u[0];
                    for ((x, y), w) in wa.iter_mut().zip(wb.iter_mut()).zip(c.col.table(b)) {
                        *x += scale * a * w;
                        *y += scale * bw * w;
                    }
                }
                [at, wa, bt, wb]
            })
            .collect()
    });
    let mut s = Vec::with_capacity(k_max);
    for i in 0..k_max {
        let (c0, c2) = cols_state.as_ref().map_or((F192::ZERO, F192::ZERO), |state| {
            (state.iter().zip(&ks)).filter(|&(_, &k)| k > i).fold(
                (F192::ZERO, F192::ZERO),
                |(c0, c2), ([at, wa, bt, wb], _)| {
                    let (a0, a2) = products(wa, at);
                    let (b0, b2) = products(wb, bt);
                    (c0 + a0 + b0, c2 + a2 + b2)
                },
            )
        });
        let (si, next) = round(b, t, claim, c0, c2);
        claim = next;
        if let Some(state) = &mut cols_state {
            let sv = b.e(si);
            for (tables, &k) in state.iter_mut().zip(&ks) {
                if k > i {
                    tables.iter_mut().for_each(|table| fold(table, sv));
                }
            }
        }
        s.push(si);
    }

    #[cfg_attr(not(test), expect(unused_mut, reason = "a test forges the values"))]
    let mut native: Vec<[F192; 2]> = (0..n_circuits)
        .map(|f| {
            cols_state
                .as_ref()
                .map_or([F192::ZERO; 2], |state| [state[f][0][0], state[f][2][0]])
        })
        .collect();
    #[cfg(test)]
    if let (Forge::Matrix, Some(state)) = (FORGE.get(), &cols_state) {
        let sv = values(b, &s);
        let mut flat: Vec<F192> = native.iter().flatten().copied().collect();
        let coefs: Vec<F192> = (0..n_circuits)
            .flat_map(|f| {
                let mu = sv[ks[f]..].iter().fold(F192::ONE, |acc, &x| acc * x);
                [mu * state[f][1][0], mu * state[f][3][0]]
            })
            .collect();
        forge(&mut flat, &coefs, b.e(claim));
        native = flat.chunks(2).map(|v| [v[0], v[1]]).collect();
    }
    let reduced: Vec<[Ew; 2]> = native.iter().map(|v| v.map(|x| b.free_e(x))).collect();

    let skip_r = math::eq_table(b, &r[..K_SKIP]);
    let skip_s = math::eq_table(b, &s[..K_SKIP]);
    let mut total = b.zero();
    for f in 0..n_circuits {
        let k = ks[f];
        let (mut wa, mut wb) = (b.zero(), b.zero());
        for (c, &g) in claims.iter().zip(&powers).filter(|(c, _)| c.circuit == f) {
            let u = c.row.eval(b, &r[..k], &skip_r);
            let w = c.col.eval(b, &s[..k], &skip_s);
            let uw = b.mul(u, w);
            let guw = b.mul(g, uw);
            wa = c.weights[0].times(b, guw, wa);
            wb = c.weights[1].times(b, guw, wb);
        }
        let zero = b.zero();
        let form = b.mul_add(reduced[f][0], wa, zero);
        let form = b.mul_add(reduced[f][1], wb, form);
        let lifts = [lift(b, &r, k), lift(b, &s, k)];
        let weighted = lifts.into_iter().flatten().fold(form, |acc, l| b.mul(acc, l));
        total = b.add(weighted, total);
    }
    b.scope("matrix reduction", |b| b.eq_e(claim, total));
    Matrices {
        rows: r,
        cols: s,
        values: reduced,
    }
}
