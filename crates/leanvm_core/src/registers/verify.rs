//! The verifier's side of the log's argument, over the verifier's arithmetic.

use super::{CELL_BITS, CELLS, GROUPS, Link, LinkShare, LogOpening, LogShape, RegisterError, Statement, WRITE};
use crate::pcs::SliceClaim;
use fiat_shamir::arith::{Arith, Verifier};
use fiat_shamir::transcript::TranscriptError;
use primitives::field::{F64, F192, G};

/// What a sumcheck opens at its final point: each group's cell word's slices, the increment, the flags' slices.
pub(super) struct Opened<E> {
    pub(super) point: Vec<E>,
    pub(super) slices: [Vec<E>; GROUPS],
    pub(super) inc: E,
    pub(super) flag: Vec<E>,
}

impl<E: Copy> Opened<E> {
    /// Read what the prover opens at `point`.
    fn read<V: Verifier<E = E>>(v: &mut V, point: Vec<E>) -> Result<Self, TranscriptError> {
        let mut slices: [Vec<E>; GROUPS] = Default::default();
        for s in &mut slices {
            *s = v.next_scalars(CELLS)?;
        }
        Ok(Self {
            point,
            slices,
            inc: v.next_scalar()?,
            flag: v.next_scalars(CELLS)?,
        })
    }

    /// Group `g`'s cell at the cell point, whose eq table is `ek`.
    fn cell<A: Arith<E = E>>(&self, a: &mut A, ek: &[E], g: usize) -> E {
        dot(a, ek, &self.slices[g])
    }

    /// The flags at the point: their packed word's slices weighted by its six low coordinates.
    fn flag<A: Arith<E = E>>(&self, a: &mut A) -> E {
        let eq = a.eq_table(&self.point[..CELL_BITS]);
        dot(a, &eq, &self.flag)
    }

    /// Refuse a cell word whose rows' weights are not one.
    fn check<V: Verifier<E = E>>(&self, v: &mut V) -> Result<(), RegisterError> {
        let one = v.one();
        for s in &self.slices {
            let weight = s.iter().fold(v.zero(), |acc, &x| v.add(acc, x));
            v.ensure_eq(weight, one, || RegisterError::Parity)?;
        }
        Ok(())
    }
}

/// The evaluation sumcheck's batching weights, drawn in this order after its collision point.
struct Weights<E> {
    /// The collision check's cell point.
    r_col: Vec<E>,
    /// Each group's collision weight, whose cube weighs its term.
    col: Vec<E>,
    /// The flag check's weight.
    ptr: E,
    /// Each output's weight.
    out: Vec<E>,
}

impl<E: Copy> Weights<E> {
    fn draw<V: Verifier<E = E>>(v: &mut V, shape: &LogShape) -> Self {
        Self {
            r_col: v.sample_vec(CELL_BITS),
            col: v.sample_vec(GROUPS),
            ptr: v.sample(),
            out: v.sample_vec(shape.outputs.len()),
        }
    }
}

/// Replay a log's argument from the bus's share, returning what it leaves the opening and the program.
///
/// # Errors
///
/// Returns a sumcheck that does not close, a cell word of even weight, or a malformed stream.
pub(crate) fn verify<V: Verifier>(
    v: &mut V,
    shape: &LogShape,
    statement: Statement<'_, V::E>,
    share: &LinkShare<V::E>,
) -> Result<LogOpening<V::E>, RegisterError> {
    let live = statement.live;
    assert_eq!(
        live.len(),
        shape.log_rows + 1,
        "the live count has a bit per row bit, and one past"
    );
    let link = Link::new(v, shape, &share.weights);
    let read_write = read_write(v, shape, live, share, &link)?;
    let evaluation = evaluation(v, shape, statement, &read_write)?;
    Ok(opening(read_write.opened, evaluation))
}

/// The read-write sumcheck's outcome: the eq table at its cell point, `Val` there, and what it opened.
struct ReadWrite<E> {
    ek: Vec<E>,
    val: E,
    opened: Opened<E>,
}

/// The read-write sumcheck, cell bits lowest first, then cycle bits highest first.
///
/// ```text
///     sum_{k,j} u(j) sum_g ra_g(k, j) (value_g Val(k, j) + address_g map(k) + inc_g inc(j) + flag_g f(j))
/// ```
///
fn read_write<V: Verifier>(
    v: &mut V,
    shape: &LogShape,
    live: &[V::E],
    share: &LinkShare<V::E>,
    link: &Link<V::E>,
) -> Result<ReadWrite<V::E>, RegisterError> {
    let mut claim = target(v, live, share, link);
    let mut fc_cell = Vec::with_capacity(CELL_BITS);
    for _ in 0..CELL_BITS {
        let coeffs = v.next_round_poly(3, claim, None)?;
        let r = v.sample();
        claim = v.poly_eval(&coeffs, r);
        fc_cell.push(r);
    }
    let (fc_row, _) = cycle_rounds(v, shape.log_rows, LogShape::READ_WRITE_COEFFS, &mut claim)?;
    let val = v.next_scalar()?;
    let opened = Opened::read(v, fc_row)?;

    let ek = v.eq_table(&fc_cell);
    let map = v.int_index(F64::ZERO, 0, &fc_cell);
    let flag = opened.flag(v);
    let mut sum = v.zero();
    for g in 0..GROUPS {
        let mut inner = v.mul(link.value[g], val);
        inner = v.mul_add(link.address[g], map, inner);
        if g == WRITE {
            inner = v.mul_add(link.inc, opened.inc, inner);
        }
        if g == 0 {
            inner = v.mul_add(link.flag, flag, inner);
        }
        let ra = opened.cell(v, &ek, g);
        sum = v.mul_add(ra, inner, sum);
    }
    let weight = live_eq(v, live, &share.point, &opened.point);
    let expected = v.mul(weight, sum);
    v.ensure_eq(expected, claim, || RegisterError::ReadWrite)?;
    opened.check(v)?;
    Ok(ReadWrite { ek, val, opened })
}

/// What the live rows' tuples sum to under `u = eq(zeta, .) live`, past the slots the verifier knows.
///
/// A live row's leaf is `beta + sum_i w_i slot_i` and a dead row's one, so with `Lambda = sum_j u(j)`:
///
/// ```text
///     value = beta Lambda + sum_i w_i sum_j u(j) slot_i(j) + 1 + Lambda
/// ```
fn target<A: Arith>(a: &mut A, live: &[A::E], share: &LinkShare<A::E>, link: &Link<A::E>) -> A::E {
    let lambda = live_sum(a, live, &share.point, None);
    let time = live_sum(a, live, &share.point, Some(G));
    let one = a.one();
    let per_row = a.add(share.beta, link.constant);
    let per_row = a.add(per_row, one);
    let known = a.mul(per_row, lambda);
    let known = a.mul_add(link.time, time, known);
    let known = a.add(known, one);
    a.add(share.value, known)
}

/// The evaluation sumcheck: `Val` at the read-write point, the outputs, and the zero checks.
fn evaluation<V: Verifier>(
    v: &mut V,
    shape: &LogShape,
    statement: Statement<'_, V::E>,
    read_write: &ReadWrite<V::E>,
) -> Result<Opened<V::E>, RegisterError> {
    let ReadWrite { ek, val, opened: first } = read_write;
    let lw = Weights::draw(v, shape);
    let mut claim = *val;
    for (&output, &weight) in statement.outputs.iter().zip(&lw.out) {
        claim = v.mul_add(weight, output, claim);
    }
    let (fc_ev, _) = cycle_rounds(v, shape.log_rows, LogShape::EVALUATION_COEFFS, &mut claim)?;
    let opened = Opened::read(v, fc_ev)?;
    let expected = summand(v, shape, statement.live, &lw, ek, &opened, &first.point);
    v.ensure_eq(expected, claim, || RegisterError::Evaluation)?;
    opened.check(v)?;
    Ok(opened)
}

/// The evaluation sumcheck's summand at its final point, from what it opened.
///
/// ```text
///     LT(fc_ev, fc_row) wa(fc_cell, fc_ev) inc + eq(fc_row, fc_ev) zero_checks + inc live(fc_ev) sum_o lambda_o wa(o, fc_ev)
/// ```
fn summand<A: Arith>(
    a: &mut A,
    shape: &LogShape,
    live: &[A::E],
    lw: &Weights<A::E>,
    ek: &[A::E],
    opened: &Opened<A::E>,
    fc_row: &[A::E],
) -> A::E {
    let fc_ev = &opened.point;
    let wa = opened.cell(a, ek, WRITE);
    let lt = lt_eval(a, fc_ev, fc_row);
    let lt_wa = a.mul(lt, wa);
    let mut total = a.mul(lt_wa, opened.inc);
    let checks = zero_checks(a, lw, opened);
    let eq = a.eq_eval(fc_row, fc_ev);
    total = a.mul_add(eq, checks, total);
    let live = live_sum(a, live, fc_ev, None);
    let written = &opened.slices[WRITE];
    let psi = (shape.outputs.iter().zip(&lw.out)).fold(a.zero(), |acc, (&cell, &l)| a.mul_add(l, written[cell], acc));
    let live_psi = a.mul(live, psi);
    a.mul_add(live_psi, opened.inc, total)
}

/// What vanishes on an honest row: each group's collision term, and the flag's write.
///
/// ```text
///     x^3 + beta^3 C y,   x = beta A(r_col),   y = A(r'),   eq(r, k)^3 = C eq(r', k)
/// ```
fn zero_checks<A: Arith>(a: &mut A, lw: &Weights<A::E>, opened: &Opened<A::E>) -> A::E {
    let (twisted, scale) = cube_point(a, &lw.r_col);
    let (er, et) = (a.eq_table(&lw.r_col), a.eq_table(&twisted));
    let mut checks = a.zero();
    for (slices, &beta) in opened.slices.iter().zip(&lw.col) {
        let x = dot(a, &er, slices);
        let x = a.mul(beta, x);
        let x2 = a.square(x);
        checks = a.mul_add(x2, x, checks);
        let y = dot(a, &et, slices);
        let b2 = a.square(beta);
        let b3 = a.mul(b2, beta);
        let w = a.mul(b3, scale);
        checks = a.mul_add(w, y, checks);
    }
    let f = opened.flag(a);
    let df = a.mul(lw.ptr, f);
    a.mul_add(df, opened.inc, checks)
}

/// Mirror of a sumcheck over the cycles: `n` rounds of `n_coeffs` coefficients, highest variable first.
///
/// Returns the point, and the product of its coordinates: the final claim's slope in the first.
fn cycle_rounds<V: Verifier>(
    v: &mut V,
    n: usize,
    n_coeffs: usize,
    claim: &mut V::E,
) -> Result<(Vec<V::E>, V::E), TranscriptError> {
    let zero = v.zero();
    let mut point = vec![zero; n];
    let mut product = v.one();
    for var in (0..n).rev() {
        let coeffs = v.next_round_poly(n_coeffs, *claim, None)?;
        let r = v.sample();
        *claim = v.poly_eval(&coeffs, r);
        product = v.mul(product, r);
        point[var] = r;
    }
    Ok((point, product))
}

/// What the log leaves the opening: each cell word's slices, the increments and the flags', at both points.
pub(super) fn opening<E: Copy>(read_write: Opened<E>, evaluation: Opened<E>) -> LogOpening<E> {
    let [rw, ev] = [read_write, evaluation];
    let claim = |point: &[E], s_hat_v: Vec<E>| SliceClaim {
        suffix_point: point.to_vec(),
        s_hat_v,
    };
    let [rs, es] = [rw.slices, ev.slices];
    let mut es = es.into_iter();
    let cells = rs.map(|a| {
        [
            claim(&rw.point, a),
            claim(&ev.point, es.next().expect("a slice per group")),
        ]
    });
    LogOpening {
        cells,
        flag: [
            claim(&rw.point[CELL_BITS..], rw.flag),
            claim(&ev.point[CELL_BITS..], ev.flag),
        ],
        inc: [(rw.point, rw.inc), (ev.point, ev.inc)],
    }
}

/// `sum_{j < live} eq(zeta, j) g^j`, or `sum_{j < live} eq(zeta, j)` without `g`.
pub(super) fn live_sum<A: Arith>(a: &mut A, live: &[A::E], zeta: &[A::E], g: Option<F64>) -> A::E {
    let mut factors = Vec::with_capacity(zeta.len());
    let mut power = g;
    for &z in zeta {
        let one = a.one();
        let zero_side = a.add(one, z);
        let one_side = power.map_or(z, |p| a.mul_const(z, F192::from(p)));
        power = power.map(|p| p * p);
        factors.push((zero_side, one_side));
    }
    prefix_sum(a, &factors, live)
}

/// `sum_{j < live} eq(zeta, j) eq(r, j)`: the read-write weight at the cycle point.
fn live_eq<A: Arith>(a: &mut A, live: &[A::E], zeta: &[A::E], r: &[A::E]) -> A::E {
    let factors: Vec<(A::E, A::E)> = (zeta.iter().zip(r))
        .map(|(&z, &x)| {
            let one = a.one();
            let (nz, nx) = (a.add(one, z), a.add(one, x));
            (a.mul(nz, nx), a.mul(z, x))
        })
        .collect();
    prefix_sum(a, &factors, live)
}

/// `sum_{j < live} prod_b f_b(j_b)`, each `f_b` given at 0 and 1, and `live` by its bits, lowest first.
///
/// At the highest bit where `j` and `live` differ, `j` has a 0 and `live` a 1.
/// The bit past the cube's says `live` is the whole cube.
pub(super) fn prefix_sum<A: Arith>(a: &mut A, f: &[(A::E, A::E)], live: &[A::E]) -> A::E {
    let mut below = vec![a.one()];
    for &(z, o) in f {
        let s = a.add(z, o);
        let next = a.mul(below[below.len() - 1], s);
        below.push(next);
    }
    let mut acc = a.mul(live[f.len()], below[f.len()]);
    let mut prefix = a.one();
    for (b, &(z, o)) in f.iter().enumerate().rev() {
        let taken = a.mul(prefix, z);
        let taken = a.mul(taken, below[b]);
        acc = a.mul_add(live[b], taken, acc);
        let flip = a.add(z, o);
        let factor = a.mul_add(live[b], flip, z);
        prefix = a.mul(prefix, factor);
    }
    acc
}

/// A count's bits as field elements, lowest first, `n + 1` of them.
pub(crate) fn live_bits(live: usize, n: usize) -> Vec<F192> {
    (0..=n).map(|b| F192::from(F64((live >> b & 1) as u64))).collect()
}

/// The multilinear extension of `[x < y]`, coordinates lowest first.
pub(super) fn lt_eval<A: Arith>(a: &mut A, x: &[A::E], y: &[A::E]) -> A::E {
    let (mut acc, mut eq_above) = (a.zero(), a.one());
    for (&xi, &yi) in x.iter().zip(y).rev() {
        let t = a.times_one_plus(eq_above, xi);
        acc = a.mul_add(t, yi, acc);
        let s = a.add(xi, yi);
        eq_above = a.times_one_plus(eq_above, s);
    }
    acc
}

/// The point `r'` and scale `C` with `eq(r, k)^3 = C eq(r', k)` on Boolean `k`.
///
/// Per coordinate `c = 1 + r + r^2` and `r' = r^3 / c`, since `(1 + r)^3 = c (1 + r')`.
pub(super) fn cube_point<A: Arith>(a: &mut A, r: &[A::E]) -> (Vec<A::E>, A::E) {
    let mut scale = a.one();
    let twisted = r
        .iter()
        .map(|&x| {
            let (x2, one) = (a.square(x), a.one());
            let c = a.add(one, x);
            let c = a.add(c, x2);
            scale = a.mul(scale, c);
            let (x3, inv) = (a.mul(x2, x), a.inv(c));
            a.mul(x3, inv)
        })
        .collect();
    (twisted, scale)
}

fn dot<A: Arith>(a: &mut A, x: &[A::E], y: &[A::E]) -> A::E {
    x.iter().zip(y).fold(a.zero(), |acc, (&p, &q)| a.mul_add(p, q, acc))
}

#[cfg(test)]
mod tests {
    use super::*;
    use fiat_shamir::arith::Native;
    use primitives::multilinear::eq_table;
    use primitives::test_util::Rng;

    #[test]
    fn the_collision_term_vanishes_exactly_on_one_hot_rows() {
        // For a row with cells S, A(r)^3 + C A(r') sums eq(r, k) eq(r, k')^2 over pairs k != k' in S.
        let r = Rng::new(1).ext_vec(CELL_BITS);
        let (twisted, scale) = cube_point(&mut Native, &r);
        let (er, et) = (eq_table(&r), eq_table(&twisted));
        let term = |cells: &[usize]| {
            let a = cells.iter().fold(F192::ZERO, |acc, &k| acc + er[k]);
            let b = cells.iter().fold(F192::ZERO, |acc, &k| acc + et[k]);
            a.square() * a + scale * b
        };
        assert!(term(&[]).is_zero());
        assert!((0..CELLS).all(|k| term(&[k]).is_zero()));
        assert!(!term(&[3, 17]).is_zero());
        assert!(!term(&[0, 5, 63]).is_zero());
    }

    #[test]
    fn the_less_than_extension_is_the_comparison() {
        let bits = |v: usize| (0..4).map(|i| F192::new((v >> i & 1) as u64, 0, 0)).collect::<Vec<_>>();
        for (x, y) in (0..16).flat_map(|x| (0..16).map(move |y| (x, y))) {
            assert_eq!(
                lt_eval(&mut Native, &bits(x), &bits(y)),
                F192::new(u64::from(x < y), 0, 0)
            );
        }
    }

    #[test]
    fn a_prefix_sum_sums_the_live_vertices() {
        let mut rng = Rng::new(2);
        let f: Vec<(F192, F192)> = (0..5).map(|_| (rng.ext(), rng.ext())).collect();
        for live in [0, 1, 13, 31, 32] {
            let want = (0..live).fold(F192::ZERO, |acc, j: usize| {
                acc + (0..5).fold(F192::ONE, |p, b| p * if j >> b & 1 == 1 { f[b].1 } else { f[b].0 })
            });
            assert_eq!(prefix_sum(&mut Native, &f, &live_bits(live, 5)), want);
        }
    }
}
