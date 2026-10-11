//! The verifier's side of a log's argument, over the verifier's arithmetic.

use super::{CHUNK, CHUNK_BITS, ImageClaim, Kind, Link, LinkShare, LogOpening, LogShape, MemoryError, Statement};
use crate::pcs::SliceClaim;
use fiat_shamir::arith::{Arith, Verifier};
use fiat_shamir::transcript::TranscriptError;
use primitives::field::{F64, F192, G};

/// What a sumcheck opens at its final point: each address word's slices, group-major, the increment, the flags' slices.
pub(super) struct Opened<E> {
    pub(super) point: Vec<E>,
    pub(super) slices: Vec<Vec<E>>,
    pub(super) inc: E,
    pub(super) flag: Option<Vec<E>>,
}

impl<E: Copy> Opened<E> {
    /// Read what the prover opens at `point`.
    fn read<V: Verifier<E = E>>(v: &mut V, shape: &LogShape, point: Vec<E>) -> Result<Self, TranscriptError> {
        let slices = (0..shape.groups() * shape.chunks())
            .map(|_| v.next_scalars(CHUNK))
            .collect::<Result<_, _>>()?;
        let inc = v.next_scalar()?;
        let flag = shape.flagged().then(|| v.next_scalars(CHUNK)).transpose()?;
        Ok(Self {
            point,
            slices,
            inc,
            flag,
        })
    }

    /// Chunk `c` of group `g`'s address word.
    fn slice(&self, shape: &LogShape, g: usize, c: usize) -> &[E] {
        &self.slices[g * shape.chunks() + c]
    }

    /// Group `g`'s address at the cell point, whose chunks' eq tables are `eks`.
    fn address<A: Arith<E = E>>(&self, a: &mut A, shape: &LogShape, eks: &[Vec<E>], g: usize) -> E {
        (0..shape.chunks()).fold(a.one(), |acc, c| {
            let e = dot(a, &eks[c], self.slice(shape, g, c));
            a.mul(acc, e)
        })
    }

    /// The flags at the point: their packed word's slices weighted by its six low coordinates.
    fn flag<A: Arith<E = E>>(&self, a: &mut A) -> E {
        match &self.flag {
            Some(slices) => {
                let eq = a.eq_table(&self.point[..CHUNK_BITS]);
                dot(a, &eq, slices)
            }
            None => a.zero(),
        }
    }

    /// Refuse an address word whose rows' weights are not one, or which names a cell of no region.
    fn check<V: Verifier<E = E>>(&self, v: &mut V, shape: &LogShape) -> Result<(), MemoryError> {
        let one = v.one();
        for s in &self.slices {
            let weight = s.iter().fold(v.zero(), |acc, &x| v.add(acc, x));
            v.ensure_eq(weight, one, || MemoryError::Parity)?;
        }
        if let Kind::Memory(regions) = &shape.kind {
            let zero = v.zero();
            for s in regions.unused() {
                v.ensure_eq(self.slice(shape, 0, shape.chunks() - 1)[s], zero, || {
                    MemoryError::Unmapped
                })?;
            }
        }
        Ok(())
    }
}

/// The evaluation sumcheck's batching weights, drawn in this order after its collision point.
struct Weights<E> {
    /// The collision check's chunk point.
    r_col: Vec<E>,
    /// Each group's and chunk's collision weight, whose cube weighs its term.
    col: Vec<E>,
    /// The flag check's weight.
    ptr: E,
    /// The partial region check's weight.
    part: E,
    /// Each output's weight.
    out: Vec<E>,
}

impl<E: Copy> Weights<E> {
    fn draw<V: Verifier<E = E>>(v: &mut V, shape: &LogShape) -> Self {
        let r_col = v.sample_vec(CHUNK_BITS);
        let col = v.sample_vec(shape.groups() * shape.chunks());
        let (ptr, part, out) = match &shape.kind {
            Kind::Registers { outputs } => (v.sample(), v.zero(), v.sample_vec(outputs.len())),
            Kind::Memory(regions) => {
                let part = if regions.partial().is_some() {
                    v.sample()
                } else {
                    v.zero()
                };
                (v.zero(), part, Vec::new())
            }
        };
        Self {
            r_col,
            col,
            ptr,
            part,
            out,
        }
    }
}

/// Replay a log's argument from the bus's share, returning what it leaves the opening and the program.
///
/// # Errors
///
/// Returns a sumcheck that does not close, an address word of even weight or of no region, or a malformed stream.
pub(crate) fn verify<V: Verifier>(
    v: &mut V,
    shape: &LogShape,
    statement: Statement<'_, V::E>,
    share: &LinkShare<V::E>,
) -> Result<LogOpening<V::E>, MemoryError> {
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

/// The read-write sumcheck's outcome: its cell point and each chunk's eq table there, `Val` there, and what it opened.
struct ReadWrite<E> {
    fc_cell: Vec<E>,
    eks: Vec<Vec<E>>,
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
) -> Result<ReadWrite<V::E>, MemoryError> {
    let mut claim = target(v, live, share, link);
    let mut fc_cell = Vec::with_capacity(shape.cell_bits());
    for _ in 0..shape.cell_bits() {
        let coeffs = v.next_round_poly(3, claim, None)?;
        let r = v.sample();
        claim = v.poly_eval(&coeffs, r);
        fc_cell.push(r);
    }
    let (fc_row, _) = cycle_rounds(v, shape.log_rows, shape.read_write_coeffs(), &mut claim)?;
    let val = v.next_scalar()?;
    let opened = Opened::read(v, shape, fc_row)?;

    let eks: Vec<Vec<V::E>> = (0..shape.chunks())
        .map(|c| v.eq_table(&fc_cell[CHUNK_BITS * c..][..CHUNK_BITS]))
        .collect();
    let map = shape.address_mle(v, &fc_cell);
    let flag = opened.flag(v);
    let mut sum = v.zero();
    for g in 0..shape.groups() {
        let mut inner = v.mul(link.value[g], val);
        inner = v.mul_add(link.address[g], map, inner);
        if g == shape.write() {
            inner = v.mul_add(link.inc, opened.inc, inner);
        }
        if g == 0 {
            inner = v.mul_add(link.flag, flag, inner);
        }
        let ra = opened.address(v, shape, &eks, g);
        sum = v.mul_add(ra, inner, sum);
    }
    let weight = live_eq(v, live, &share.point, &opened.point);
    let expected = v.mul(weight, sum);
    v.ensure_eq(expected, claim, || MemoryError::ReadWrite)?;
    opened.check(v, shape)?;
    Ok(ReadWrite {
        fc_cell,
        eks,
        val,
        opened,
    })
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
///
/// RAM's image is the program's: the sumcheck runs without its term, which the final claim carries at weight `prod r`.
fn evaluation<V: Verifier>(
    v: &mut V,
    shape: &LogShape,
    statement: Statement<'_, V::E>,
    read_write: &ReadWrite<V::E>,
) -> Result<Evaluation<V::E>, MemoryError> {
    let ReadWrite {
        fc_cell,
        eks,
        val,
        opened: first,
    } = read_write;
    let lw = Weights::draw(v, shape);
    let mut claim = *val;
    let advice = match &shape.kind {
        Kind::Memory(regions) => {
            let (factor, point) = regions.at(v, fc_cell, regions.advice);
            let value = v.next_scalar()?;
            claim = v.mul_add(factor, value, claim);
            Some((point, value))
        }
        Kind::Registers { .. } => {
            for (&output, &weight) in statement.outputs.iter().zip(&lw.out) {
                claim = v.mul_add(weight, output, claim);
            }
            None
        }
    };
    let (fc_ev, product) = cycle_rounds(v, shape.log_rows, shape.evaluation_coeffs(), &mut claim)?;
    let opened = Opened::read(v, shape, fc_ev)?;
    let expected = summand(v, shape, statement.live, &lw, eks, &opened, &first.point);
    let image = match &shape.kind {
        Kind::Memory(regions) => {
            let (factor, point) = regions.at(v, fc_cell, regions.ram);
            let weight = v.mul(factor, product);
            let value = v.add(claim, expected);
            Some(ImageClaim { weight, point, value })
        }
        Kind::Registers { .. } => {
            v.ensure_eq(expected, claim, || MemoryError::Evaluation)?;
            None
        }
    };
    opened.check(v, shape)?;
    Ok(Evaluation { opened, advice, image })
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
    eks: &[Vec<A::E>],
    opened: &Opened<A::E>,
    fc_row: &[A::E],
) -> A::E {
    let fc_ev = &opened.point;
    let wa = opened.address(a, shape, eks, shape.write());
    let lt = lt_eval(a, fc_ev, fc_row);
    let lt_wa = a.mul(lt, wa);
    let mut total = a.mul(lt_wa, opened.inc);
    let checks = zero_checks(a, shape, lw, opened);
    let eq = a.eq_eval(fc_row, fc_ev);
    total = a.mul_add(eq, checks, total);
    if let Kind::Registers { outputs } = &shape.kind {
        let live = live_sum(a, live, fc_ev, None);
        let written = opened.slice(shape, shape.write(), 0);
        let psi = (outputs.iter().zip(&lw.out)).fold(a.zero(), |acc, (&cell, &l)| a.mul_add(l, written[cell], acc));
        let live_psi = a.mul(live, psi);
        total = a.mul_add(live_psi, opened.inc, total);
    }
    total
}

/// What vanishes on an honest row: each address chunk's collision term, the flag's write, and a partial region's excess.
///
/// ```text
///     x^3 + beta^3 C y,   x = beta A(r_col),   y = A(r'),   eq(r, k)^3 = C eq(r', k)
/// ```
fn zero_checks<A: Arith>(a: &mut A, shape: &LogShape, lw: &Weights<A::E>, opened: &Opened<A::E>) -> A::E {
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
    match &shape.kind {
        Kind::Registers { .. } => {
            let f = opened.flag(a);
            let df = a.mul(lw.ptr, f);
            checks = a.mul_add(df, opened.inc, checks);
        }
        Kind::Memory(regions) => {
            if let Some(region) = regions.partial() {
                let top = opened.slice(shape, 0, shape.chunks() - 1)[region.first];
                let mut inside = a.one();
                for (c, m) in regions.allowed(region) {
                    let ok = opened.slice(shape, 0, c)[..m]
                        .iter()
                        .fold(a.zero(), |acc, &s| a.add(acc, s));
                    inside = a.mul(inside, ok);
                }
                let one = a.one();
                let outside = a.add(one, inside);
                let excess = a.mul(top, outside);
                checks = a.mul_add(lw.part, excess, checks);
            }
        }
    }
    checks
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

/// The evaluation sumcheck's outcome: what it opened, and the claims on the advice and on RAM's image.
pub(super) struct Evaluation<E> {
    pub(super) opened: Opened<E>,
    pub(super) advice: Option<(Vec<E>, E)>,
    pub(super) image: Option<ImageClaim<E>>,
}

/// What a log leaves the opening: its address words' slices, its increments, its flags, and its initial memory.
pub(super) fn opening<E: Copy>(read_write: Opened<E>, evaluation: Evaluation<E>) -> LogOpening<E> {
    let Evaluation { opened, advice, image } = evaluation;
    let [rw, ev] = [read_write, opened];
    let flag = match (rw.flag, ev.flag) {
        (Some(a), Some(b)) => Some([
            SliceClaim {
                suffix_point: rw.point[CHUNK_BITS..].to_vec(),
                s_hat_v: a,
            },
            SliceClaim {
                suffix_point: ev.point[CHUNK_BITS..].to_vec(),
                s_hat_v: b,
            },
        ]),
        _ => None,
    };
    let addresses = (rw.slices.into_iter().zip(ev.slices))
        .map(|(a, b)| {
            [
                SliceClaim {
                    suffix_point: rw.point.clone(),
                    s_hat_v: a,
                },
                SliceClaim {
                    suffix_point: ev.point.clone(),
                    s_hat_v: b,
                },
            ]
        })
        .collect();
    LogOpening {
        addresses,
        inc: [(rw.point, rw.inc), (ev.point, ev.inc)],
        flag,
        advice,
        image,
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
        let r = Rng::new(1).ext_vec(CHUNK_BITS);
        let (twisted, scale) = cube_point(&mut Native, &r);
        let (er, et) = (eq_table(&r), eq_table(&twisted));
        let term = |cells: &[usize]| {
            let a = cells.iter().fold(F192::ZERO, |acc, &k| acc + er[k]);
            let b = cells.iter().fold(F192::ZERO, |acc, &k| acc + et[k]);
            a.square() * a + scale * b
        };
        assert!(term(&[]).is_zero());
        assert!((0..CHUNK).all(|k| term(&[k]).is_zero()));
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
