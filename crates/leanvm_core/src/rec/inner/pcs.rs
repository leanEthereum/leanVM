//! The stacked opening's verifier (`crate::pcs::verify`) as a circuit: the ring-switch batching and the
//! lifted weight of `pcs::stack_open::verify_opening_batch_mixed_whir_stacked`, and the succinct WHIR
//! verifier under it (`pcs::whir::recursive_verifier_with_basis_succinct`).

use super::{RingRegion, StackClaim, math};
use crate::rec::circuit::{Builder, Dw, Ew, Kw};
use crate::rec::transcript::Transcript;
use ::pcs::pack::PACKING_WIDTH;
use ::pcs::ring_switch::COMPOSITION_SHIFTS;
use ::pcs::whir::{VerifierConfig, config_for_rate, eval_sk_at_vks};
use primitives::field::{F64, F192};

/// `c·x + acc`, where an absent `c` is one and an absent `acc` is zero.
fn mac(b: &mut Builder, acc: Option<Ew>, c: Option<Ew>, x: Ew) -> Ew {
    match (acc, c) {
        (None, None) => x,
        (Some(a), None) => b.add(x, a),
        (None, Some(c)) => b.mul(c, x),
        (Some(a), Some(c)) => b.mul_add(c, x, a),
    }
}

/// `acc·f`, where an absent `acc` is one.
fn times(b: &mut Builder, acc: Option<Ew>, f: Ew) -> Ew {
    acc.map_or(f, |a| b.mul(a, f))
}

fn or_one(b: &mut Builder, x: Option<Ew>) -> Ew {
    x.unwrap_or_else(|| b.one())
}

/// `x^0, ..., x^(n-1)`, the first absent for one.
fn powers(b: &mut Builder, x: Ew, n: usize) -> Vec<Option<Ew>> {
    let mut out: Vec<Option<Ew>> = Vec::with_capacity(n);
    for i in 0..n {
        out.push(match i {
            0 => None,
            1 => Some(x),
            _ => Some(b.mul(out[i - 1].expect("a power past the first"), x)),
        });
    }
    out
}

/// `acc·(1 + x)`, where an absent `acc` is one.
fn times_one_plus(b: &mut Builder, acc: Option<Ew>, x: Ew) -> Ew {
    match acc {
        None => b.add_const(x, F192::ONE),
        Some(a) => math::times_one_plus(b, a, x),
    }
}

/// `acc·x` if `bit`, else `acc·(1 + x)`: one coordinate of a Boolean point's equality weight.
fn select(b: &mut Builder, acc: Option<Ew>, x: Ew, bit: bool) -> Ew {
    if bit {
        times(b, acc, x)
    } else {
        times_one_plus(b, acc, x)
    }
}

/// `acc·(1 + p + x)`: one coordinate of `eq(p, x)`.
fn times_eq(b: &mut Builder, acc: Option<Ew>, p: Ew, x: Ew) -> Ew {
    let s = b.add(p, x);
    times_one_plus(b, acc, s)
}

/// `eq(r, ·)` at the first `len` indices, lowest coordinate first (`primitives::multilinear::eq_table`).
fn eq_table(b: &mut Builder, r: &[Ew], len: usize) -> Vec<Option<Ew>> {
    assert!(len <= 1 << r.len());
    let mut eq: Vec<Option<Ew>> = vec![None];
    for (i, &ri) in r.iter().enumerate() {
        let half = 1usize << i;
        let need = len.min(2 * half);
        let lo: Vec<Option<Ew>> = eq[..need.min(half)]
            .iter()
            .map(|&e| Some(times_one_plus(b, e, ri)))
            .collect();
        let hi: Vec<Option<Ew>> = eq[..need.saturating_sub(half)]
            .iter()
            .map(|&e| Some(times(b, e, ri)))
            .collect();
        eq = lo;
        eq.extend(hi);
    }
    eq.truncate(len);
    eq
}

/// `Σ_i y[i]·eq(r, i)`, the multilinear extension of `y` at `r`, folding the lowest coordinate first.
fn mle(b: &mut Builder, y: &[Ew], r: &[Ew]) -> Ew {
    assert_eq!(y.len(), 1 << r.len());
    let mut y = y.to_vec();
    for &ri in r {
        y = y.chunks(2).map(|p| math::interp(b, p[0], p[1], ri)).collect();
    }
    y[0]
}

/// The ring-switching map `Phi` from its six challenges, as the coefficients `C_k^(2^-k)` of its Frobenius
/// form (`ring_switch::RsEqQuery`); absent is one.
struct Map {
    coefficients: Vec<Option<Ew>>,
}

impl Map {
    fn new(b: &mut Builder, challenges: &[Ew]) -> Self {
        // C_k^(2^-k) = prod_{p : k & d_p} f_p^(2^-(k - k mod d_p)), and k - k mod d_p is the part of k at
        // the shifts down to d_p, so the product grows one shift at a time.
        let mut coefficients: Vec<Option<Ew>> = vec![None];
        let mut prefixes = vec![0usize];
        for (&f, &shift) in challenges.iter().zip(COMPOSITION_SHIFTS.iter()) {
            let ladder = math::inverse_frobenius_ladder(b, f, shift, PACKING_WIDTH);
            let mut next_c = Vec::with_capacity(2 * coefficients.len());
            let mut next_p = Vec::with_capacity(2 * prefixes.len());
            for (&c, &k) in coefficients.iter().zip(&prefixes) {
                next_c.push(c);
                next_p.push(k);
                next_c.push(Some(times(b, c, ladder[k + shift])));
                next_p.push(k + shift);
            }
            coefficients = next_c;
            prefixes = next_p;
        }
        let mut by_k = vec![None; PACKING_WIDTH];
        for (c, k) in coefficients.into_iter().zip(prefixes) {
            by_k[k] = c;
        }
        Self { coefficients: by_k }
    }

    /// `ring_switch::verify_finish`: `Σ_w Phi(b_w)·t_w` over the transposed slices `t`, which is
    /// `Σ_j x^j·Phi(s_j) = Σ_k (C_k^(2^-k)·S(x^(2^-k)))^(2^k)` for `S(u) = Σ_j s_j·u^j`, closed by the
    /// linearized Horner rule from `k = 63` down.
    fn finish(&self, b: &mut Builder, s_hat_v: &[Ew]) -> Ew {
        assert_eq!(s_hat_v.len(), PACKING_WIDTH);
        let mut acc: Option<Ew> = None;
        for k in (0..PACKING_WIDTH).rev() {
            let mut xk = F64(2);
            for _ in 0..(PACKING_WIDTH - k) % PACKING_WIDTH {
                xk = xk.square();
            }
            let xk = F192::from(xk);
            let mut s = s_hat_v[PACKING_WIDTH - 1];
            for &sj in s_hat_v[..PACKING_WIDTH - 1].iter().rev() {
                s = b.mul_const_add(s, xk, sj);
            }
            let term = self.coefficients[k].map_or(s, |c| b.mul(c, s));
            acc = Some(acc.map_or(term, |a| b.mul_add(a, a, term)));
        }
        acc.expect("the map has 64 terms")
    }

    /// `ring_switch::eval_rs_eq` at the suffix point `z`, against the query's ladders.
    fn eval_rs_eq(&self, b: &mut Builder, z: &[Ew], ladders: &[Vec<Ew>]) -> Ew {
        assert!(z.len() <= ladders.len());
        let mut terms = self.coefficients.clone();
        for (&zn, ladder) in z.iter().zip(ladders) {
            for (term, &power) in terms.iter_mut().zip(ladder) {
                *term = Some(times_eq(b, *term, power, zn));
            }
        }
        let mut terms: Vec<Ew> = terms.into_iter().map(|t| or_one(b, t)).collect();
        let last = terms.pop().expect("the map has 64 terms");
        terms.iter().rev().fold(last, |acc, &term| b.mul_add(acc, acc, term))
    }
}

/// Where the ring-switched claims' share of the opening is settled.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum RingMode {
    /// Hinted and exposed as a [`RingShare`], which a native verifier recomputes.
    Hint,
    /// Computed in the circuit from the map's challenges, as the native verifier does.
    Prove,
}

/// The ring-switched claims' share of the opening, which the circuit leaves to the outer verifier: the map's
/// challenges and the batching challenge, the terminal point, and what the claims put into the target and
/// into the weight there (`stack_open::verify_opening_batch_mixed_whir_stacked`). Their slices and points are
/// the circuit's own wires, which the statement exposes too.
pub struct RingShare {
    pub map: Vec<Ew>,
    pub lambda: Ew,
    pub point: Vec<Ew>,
    pub target: Ew,
    pub weight: Ew,
}

/// The native ring-switched share of the target, `Σ_c λ^c·verify_finish(s_c)`.
pub fn ring_target(map: &[F192; 6], lambda: F192, slices: &[&[F192]]) -> F192 {
    let weights = ::pcs::ring_switch::build_coordinate_weights(map);
    let mut g = F192::ONE;
    let mut total = F192::ZERO;
    for s in slices {
        total += g * ::pcs::ring_switch::verify_finish(s, &weights);
        g *= lambda;
    }
    total
}

/// The native ring-switched share of the weight at the terminal point `x`, each region `(offset,
/// qflock_vars, suffix points)`, the claims in order taking `λ^c`.
pub fn ring_weight(map: &[F192; 6], lambda: F192, rings: &[(usize, usize, Vec<&[F192]>)], x: &[F192]) -> F192 {
    let max_qflock_vars = rings.iter().map(|r| r.1).max().unwrap_or(0);
    let query = ::pcs::ring_switch::RsEqQuery::new(map, &x[..max_qflock_vars]);
    let mut g = F192::ONE;
    let mut total = F192::ZERO;
    for (offset, qflock_vars, points) in rings {
        let sel = offset >> qflock_vars;
        let sel_eq = x[*qflock_vars..].iter().enumerate().fold(F192::ONE, |acc, (k, &xi)| {
            acc * if (sel >> k) & 1 == 1 { xi } else { F192::ONE + xi }
        });
        let mut part = F192::ZERO;
        for z in points {
            part += g * ::pcs::ring_switch::eval_rs_eq(z, &query);
            g *= lambda;
        }
        total += sel_eq * part;
    }
    total
}

/// One coordinate of a claim's full point: a wire, or a Boolean selector bit.
#[derive(Clone, Copy)]
enum Coord {
    At(Ew),
    Bit(bool),
}

/// `stack_open::stack_claim_eq_at`: the claim's equality weight at the full stack point `x`.
fn stack_claim_eq_at(b: &mut Builder, claim: &StackClaim, x: &[Ew]) -> Ew {
    let (low, sel): (Vec<Coord>, usize) = match claim {
        StackClaim::Point { offset, low_point, .. } => (
            low_point.iter().map(|&p| Coord::At(p)).collect(),
            offset >> low_point.len(),
        ),
        StackClaim::Strided {
            offset,
            slot,
            stride_log,
            point,
            ..
        } => {
            let slot_bits = (0..*stride_log).map(|k| Coord::Bit((slot >> k) & 1 == 1));
            let low = slot_bits.chain(point.iter().map(|&p| Coord::At(p))).collect();
            (low, offset >> (stride_log + point.len()))
        }
    };
    let sel_bits = (0..x.len() - low.len()).map(|k| Coord::Bit((sel >> k) & 1 == 1));
    let mut e: Option<Ew> = None;
    for (c, &xi) in low.into_iter().chain(sel_bits).zip(x) {
        e = Some(match c {
            Coord::At(p) => times_eq(b, e, p, xi),
            Coord::Bit(bit) => select(b, e, xi, bit),
        });
    }
    or_one(b, e)
}

/// The end of the stack range a claim's weight is supported on (`stack_open::claim_range`).
fn claim_end(claim: &StackClaim) -> usize {
    match claim {
        StackClaim::Point { offset, low_point, .. } => offset + (1usize << low_point.len()),
        StackClaim::Strided {
            offset,
            stride_log,
            point,
            ..
        } => offset + (1usize << (stride_log + point.len())),
    }
}

/// Verify the opening of the commitment `root` against the point claims `slots` and the ring-switched
/// regions `rings` (`crate::pcs::verify`). The claims' values and slices were bound by the caller.
///
/// Under [`RingMode::Hint`] the ring-switched claims' share of the target and of the terminal weight is a hint,
/// settled by the outer verifier from the returned [`RingShare`] ([`ring_target`], [`ring_weight`]); under
/// [`RingMode::Prove`] the circuit computes both and returns nothing.
#[expect(
    clippy::too_many_arguments,
    reason = "the opening's inputs, as `pcs::verify` takes them"
)]
pub fn verify(
    b: &mut Builder,
    t: &mut Transcript,
    slots: &[StackClaim],
    rings: &[RingRegion],
    shape: crate::witness::StackShape,
    log_inv_rate: usize,
    root: Dw,
    mode: RingMode,
) -> Option<RingShare> {
    let log_n = shape.mu;
    let config = config_for_rate(log_n, log_inv_rate)
        .unwrap_or_else(|e| panic!("whir config for mu={log_n}, log_inv_rate={log_inv_rate}: {e}"));
    let n_rs: usize = rings.iter().map(|ring| ring.claims.len()).sum();
    assert!(n_rs > 0, "stacked PCS opening carries at least one ring-switched claim");
    for ring in rings {
        assert!(ring.qflock_vars <= log_n);
        assert!(
            ring.offset.is_multiple_of(1usize << ring.qflock_vars),
            "q_flock offset must be 2^qflock_vars-aligned"
        );
        for claim in &ring.claims {
            assert_eq!(claim.suffix_point.len(), ring.qflock_vars);
            assert_eq!(claim.s_hat_v.len(), PACKING_WIDTH);
        }
        assert!(ring.offset + (1usize << ring.qflock_vars) <= 1usize << log_n);
    }
    assert!(
        slots.iter().all(|c| claim_end(c) <= 1usize << log_n),
        "every claim must live inside the committed cube"
    );

    let map = t.sample_vec(b, COMPOSITION_SHIFTS.len());
    let lambda = t.sample(b);
    let lambdas = powers(b, lambda, n_rs + slots.len());
    let (lambdas_rs, lambdas_pd) = lambdas.split_at(n_rs);
    let map_values: [F192; 6] = std::array::from_fn(|i| b.e(map[i]));
    let phi = (mode == RingMode::Prove).then(|| b.scope("ring switch map", |b| Map::new(b, &map)));

    let ring_target_wire = match &phi {
        Some(phi) => b.scope("ring target", |b| {
            let mut target = None;
            for (claim, &g) in rings.iter().flat_map(|ring| &ring.claims).zip(lambdas_rs) {
                let v = phi.finish(b, &claim.s_hat_v);
                target = Some(mac(b, target, g, v));
            }
            target.expect("at least one ring-switched claim")
        }),
        None => {
            let slices: Vec<Vec<F192>> = rings
                .iter()
                .flat_map(|r| &r.claims)
                .map(|c| c.s_hat_v.iter().map(|&w| b.e(w)).collect())
                .collect();
            let slice_refs: Vec<&[F192]> = slices.iter().map(Vec::as_slice).collect();
            b.free_e(ring_target(&map_values, b.e(lambda), &slice_refs))
        }
    };

    let target = b.scope("target", |b| {
        let mut target = ring_target_wire;
        for (claim, &g) in slots.iter().zip(lambdas_pd) {
            target = mac(b, Some(target), g, claim.value());
        }
        target
    });

    let points: Vec<Vec<Vec<F192>>> = rings
        .iter()
        .map(|r| {
            r.claims
                .iter()
                .map(|c| c.suffix_point.iter().map(|&w| b.e(w)).collect())
                .collect()
        })
        .collect();
    let max_qflock_vars = rings.iter().map(|ring| ring.qflock_vars).max().unwrap_or(0);
    let mut share = None;
    let eval_b_at = |b: &mut Builder, x: &[Ew], init: Option<Ew>| -> Ew {
        let weight = match &phi {
            Some(phi) => {
                let ladders: Vec<Vec<Ew>> = x[..max_qflock_vars]
                    .iter()
                    .map(|&q| math::inverse_frobenius_ladder(b, q, 1, PACKING_WIDTH))
                    .collect();
                let mut weight = None;
                let mut lambdas_rs = lambdas_rs.iter();
                for ring in rings {
                    let sel = ring.offset >> ring.qflock_vars;
                    let mut sel_eq = None;
                    for (k, &xi) in x[ring.qflock_vars..].iter().enumerate() {
                        sel_eq = Some(select(b, sel_eq, xi, (sel >> k) & 1 == 1));
                    }
                    let mut part = None;
                    for (claim, &g) in ring.claims.iter().zip(lambdas_rs.by_ref()) {
                        let v = phi.eval_rs_eq(b, &claim.suffix_point, &ladders);
                        part = Some(mac(b, part, g, v));
                    }
                    let part = part.unwrap_or_else(|| b.zero());
                    weight = Some(mac(b, weight, sel_eq, part));
                }
                weight.expect("at least one ring-switched region")
            }
            None => {
                let x_values: Vec<F192> = x.iter().map(|&w| b.e(w)).collect();
                let regions: Vec<(usize, usize, Vec<&[F192]>)> = rings
                    .iter()
                    .zip(&points)
                    .map(|(r, p)| (r.offset, r.qflock_vars, p.iter().map(Vec::as_slice).collect()))
                    .collect();
                b.free_e(ring_weight(&map_values, b.e(lambda), &regions, &x_values))
            }
        };
        share = Some((x.to_vec(), weight));
        let mut acc = mac(b, init, None, weight);
        for (claim, &g) in slots.iter().zip(lambdas_pd) {
            let e = stack_claim_eq_at(b, claim, x);
            acc = mac(b, Some(acc), g, e);
        }
        acc
    };

    b.scope("whir", |b| {
        whir(b, t, &config, log_n, shape.n_lanes, target, root, eval_b_at);
    });
    let (point, weight) = share.expect("the terminal check evaluates the weight");
    (mode == RingMode::Hint).then_some(RingShare {
        map,
        lambda,
        point,
        target: ring_target_wire,
        weight,
    })
}

/// A round's quadratic `c + b·X + a·X^2` (`whir::sumcheck::RoundQuad`).
#[derive(Clone, Copy)]
struct Quad {
    c: Ew,
    b: Ew,
    a: Ew,
}

impl Quad {
    /// `whir::sumcheck::recv_quad`.
    fn recv(b: &mut Builder, t: &mut Transcript, claim: Ew) -> Self {
        let h = t.next_round_poly(b, 3, claim, None);
        Self {
            c: h[0],
            b: h[1],
            a: h[2],
        }
    }

    fn eval(self, b: &mut Builder, r: Ew) -> Ew {
        let u = b.mul_add(self.a, r, self.b);
        b.mul_add(u, r, self.c)
    }

    fn fold(self, b: &mut Builder, other: Self, alpha: Ew) -> Self {
        Self {
            c: b.mul_add(alpha, other.c, self.c),
            b: b.mul_add(alpha, other.b, self.b),
            a: b.mul_add(alpha, other.a, self.a),
        }
    }
}

/// `whir::verify::replay_fold_rounds`.
fn fold_rounds(b: &mut Builder, t: &mut Transcript, k: usize, t_r: &mut Ew, quad: &mut Quad) -> Vec<Ew> {
    (0..k)
        .map(|_| {
            let ri = t.sample(b);
            *t_r = quad.eval(b, ri);
            *quad = Quad::recv(b, t, *t_r);
            ri
        })
        .collect()
}

/// `whir::verify::OodReplay`.
struct Ood {
    z: Vec<Ew>,
    y: Ew,
    intro: Quad,
}

/// `whir::verify::replay_ood`.
fn replay_ood(b: &mut Builder, t: &mut Transcript, n_vars: usize) -> Ood {
    let z = t.sample_vec(b, n_vars);
    let y = t.next_scalar(b);
    let intro = Quad::recv(b, t, y);
    Ood { z, y, intro }
}

/// `whir::verify::batch_level_claims`: the scalars the OOD claims and the query batch took.
fn batch_level_claims(
    b: &mut Builder,
    lambda: Ew,
    ood: &[Ood],
    query_intro: Quad,
    query_sum: Ew,
    t_r: &mut Ew,
    quad: &mut Quad,
) -> (Vec<Ew>, Ew) {
    let mut scalar: Option<Ew> = None;
    let mut ood_scalars = Vec::with_capacity(ood.len());
    for claim in ood {
        let s = times(b, scalar, lambda);
        scalar = Some(s);
        *quad = quad.fold(b, claim.intro, s);
        *t_r = b.mul_add(s, claim.y, *t_r);
        ood_scalars.push(s);
    }
    let s = times(b, scalar, lambda);
    *quad = quad.fold(b, query_intro, s);
    *t_r = b.mul_add(s, query_sum, *t_r);
    (ood_scalars, s)
}

/// `whir::sample_queries_ordered`: each query's `d` index bits, lowest first, cut from the 192 bits of a
/// challenge (`c0 | c1 << 64 | c2 << 128`).
fn sample_queries(b: &mut Builder, t: &mut Transcript, d: usize, count: usize) -> Vec<Vec<Kw>> {
    let per = 192 / d;
    let mut out = Vec::with_capacity(count);
    while out.len() < count {
        let v = t.sample(b);
        let n = per.min(count - out.len());
        let limbs = b.e_to_k(v);
        let mut bits = Vec::with_capacity(192);
        for &limb in &limbs[..(n * d).div_ceil(64)] {
            bits.extend(b.split(limb));
        }
        out.extend((0..n).map(|j| bits[j * d..(j + 1) * d].to_vec()));
    }
    out
}

/// `whir_induce::induce_sumcheck_enforced_sum` over `K` rows: `Σ_i w_i·<row_i, eq(v, ·)>`.
fn enforced_sum_k(b: &mut Builder, rows: &[Vec<Kw>], v: &[Ew], w: &[Option<Ew>]) -> Ew {
    let width = rows[0].len();
    let eq = eq_table(b, v, width);
    let one = b.one();
    let zero = b.zero();
    let mut sum = None;
    for (l, &e) in eq.iter().enumerate() {
        let u = rows
            .iter()
            .zip(w)
            .fold(zero, |acc, (row, &wi)| b.mul_k_add(wi.unwrap_or(one), row[l], acc));
        sum = Some(mac(b, sum, e, u));
    }
    sum.expect("a row has a word")
}

/// `whir_induce::induce_sumcheck_enforced_sum` over `E` rows.
fn enforced_sum_e(b: &mut Builder, rows: &[Vec<Ew>], v: &[Ew], w: &[Option<Ew>]) -> Ew {
    let width = rows[0].len();
    let eq = eq_table(b, v, width);
    let mut sum = None;
    for (l, &e) in eq.iter().enumerate() {
        let u = rows
            .iter()
            .zip(w)
            .fold(None, |acc, (row, &wi)| Some(mac(b, acc, wi, row[l])))
            .expect("a level has a query");
        sum = Some(mac(b, sum, e, u));
    }
    sum.expect("a row has an element")
}

/// `whir_induce::induce_sumcheck_evaluate_at_residual` at one point:
/// `Σ_i w_i·Π_k (1 + p_k·(1 + s_k(q_i)/s_k(v_k)))`, with `q_i` the query index as a `K` element.
fn induce_at(b: &mut Builder, log_msg_cols: usize, queries: &[Vec<Kw>], weights: &[Option<Ew>], point: &[Ew]) -> Ew {
    assert_eq!(point.len(), log_msg_cols);
    let sks = eval_sk_at_vks(log_msg_cols);
    // 1 + p·(1 + s/σ) = (1 + p) + (p/σ)·s.
    let lin: Vec<(Ew, Ew)> = point
        .iter()
        .zip(&sks)
        .map(|(&p, &sigma)| {
            let inv = if sigma == F64(0) { F64(0) } else { sigma.inv() };
            let c = b.mul_const(p, F192::from(inv));
            (b.add_const(p, F192::ONE), c)
        })
        .collect();
    let mut acc = None;
    for (bits, &w) in queries.iter().zip(weights) {
        let q = b.pack(bits);
        let mut s = b.k_to_e1(q);
        let mut prod = None;
        for (k, &(a, c)) in lin.iter().enumerate() {
            if k > 0 {
                let u = b.mul_const(s, F192::from(sks[k - 1]));
                s = b.mul_add(s, s, u);
            }
            let f = b.mul_add(c, s, a);
            prod = Some(times(b, prod, f));
        }
        let prod = or_one(b, prod);
        acc = Some(mac(b, acc, w, prod));
    }
    acc.expect("a level has a query")
}

/// The level whose rows the next query phase opens (`whir::verify::PrevLevel`).
struct PrevLevel {
    root: Dw,
    log_num_interleaved: usize,
    log_msg_cols: usize,
    log_inv_rate: usize,
}

struct LevelCtx {
    log_msg_cols: usize,
    queries: Vec<Vec<Kw>>,
    weights: Vec<Option<Ew>>,
    ris_start: usize,
    beta: Ew,
}

struct OodCtx {
    z: Vec<Ew>,
    ris_start: usize,
    beta: Ew,
}

/// One level's opened `E` rows: each query's row read as three `K` words per element.
fn open_e_rows(b: &mut Builder, t: &mut Transcript, prev: &PrevLevel, queries: &[Vec<Kw>]) -> Vec<Vec<Ew>> {
    let leaf_words = 3 << prev.log_num_interleaved;
    queries
        .iter()
        .map(|bits| {
            assert_eq!(bits.len(), prev.log_msg_cols + prev.log_inv_rate);
            let words = t.open_row(b, prev.root, bits, leaf_words, leaf_words);
            words.chunks(3).map(|c| b.k_to_e([c[0], c[1], c[2]])).collect()
        })
        .collect()
}

/// `whir::recursive_verifier_with_basis_succinct`, with `eval_b_at` the caller's weight at the
/// terminal point (indexed by witness coordinate) added to `init`.
#[allow(clippy::too_many_arguments)]
fn whir(
    b: &mut Builder,
    t: &mut Transcript,
    config: &VerifierConfig,
    log_n: usize,
    n_lanes: usize,
    target: Ew,
    root: Dw,
    eval_b_at: impl FnOnce(&mut Builder, &[Ew], Option<Ew>) -> Ew,
) {
    let initial_k = config.initial_k();
    let r = config.level_steps();
    let max = 1usize << initial_k;
    assert!(
        n_lanes != 0 && n_lanes <= max,
        "{n_lanes} committed lanes, and a leaf holds 1 to {max}"
    );
    let log_inv_rate_0 = config.log_inv_rates()[0];
    let n1 = log_n - initial_k;
    let depth_0 = n1 + log_inv_rate_0;

    let mut t_r = target;
    let mut quad = Quad::recv(b, t, t_r);
    let r_lane_fold = fold_rounds(b, t, initial_k, &mut t_r, &mut quad);
    let root_1 = t.next_root(b);
    let level_ood: Vec<Ood> = (0..config.ood_samples()[1]).map(|_| replay_ood(b, t, n1)).collect();
    t.grind_check(b, config.grinding_bits()[0] as u32);

    let num_queries_0 = config.queries()[0];
    let queries_0 = sample_queries(b, t, depth_0, num_queries_0);
    let lambda_0 = t.sample(b);
    let weights_0 = powers(b, lambda_0, num_queries_0);
    // The proof stores the committed lanes, the image's tail; the image is lane-descending.
    let rows_0: Vec<Vec<Kw>> = b.scope("L0 rows", |b| {
        queries_0
            .iter()
            .map(|bits| {
                let mut row = t.open_row(b, root, bits, n_lanes, max);
                row.reverse();
                row
            })
            .collect()
    });
    let enforced_sum_0 = enforced_sum_k(b, &rows_0, &r_lane_fold, &weights_0);
    let intro_0 = Quad::recv(b, t, enforced_sum_0);
    let (ood_scalars_0, query_scalar_0) =
        batch_level_claims(b, lambda_0, &level_ood, intro_0, enforced_sum_0, &mut t_r, &mut quad);
    let mut ood_ctxs: Vec<OodCtx> = level_ood
        .into_iter()
        .zip(ood_scalars_0)
        .map(|(ood, beta)| OodCtx {
            z: ood.z,
            ris_start: initial_k,
            beta,
        })
        .collect();
    let mut level_ctxs = vec![LevelCtx {
        log_msg_cols: n1,
        queries: queries_0,
        weights: weights_0,
        ris_start: initial_k,
        beta: query_scalar_0,
    }];
    let mut ris = r_lane_fold;

    let mut prev = PrevLevel {
        root: root_1,
        log_num_interleaved: config.level_ks()[0],
        log_msg_cols: n1 - config.level_ks()[0],
        log_inv_rate: config.log_inv_rates()[1],
    };
    let mut n_current = n1;

    for i in 0..r {
        let k_i = config.level_ks()[i];
        assert!(
            n_current >= k_i,
            "level {i} of the configuration does not fit the witness"
        );
        let level_rs = fold_rounds(b, t, k_i, &mut t_r, &mut quad);
        ris.extend_from_slice(&level_rs);
        n_current -= k_i;

        if i == r - 1 {
            let yr = t.next_scalars(b, 1 << n_current);
            t.grind_check(b, config.grinding_bits()[i + 1] as u32);
            let num_queries_last = config.queries()[i + 1];
            let queries_last = sample_queries(b, t, prev.log_msg_cols + prev.log_inv_rate, num_queries_last);
            let lambda_last = t.sample(b);
            let weights_last = powers(b, lambda_last, num_queries_last);
            let rows_last = b.scope(format!("L{} rows", i + 1), |b| open_e_rows(b, t, &prev, &queries_last));
            let enforced_sum_last = enforced_sum_e(b, &rows_last, &level_rs, &weights_last);
            let intro_last = Quad::recv(b, t, enforced_sum_last);
            let (_, query_scalar_last) =
                batch_level_claims(b, lambda_last, &[], intro_last, enforced_sum_last, &mut t_r, &mut quad);
            level_ctxs.push(LevelCtx {
                log_msg_cols: n_current,
                queries: queries_last,
                weights: weights_last,
                ris_start: ris.len(),
                beta: query_scalar_last,
            });

            let yr_log_n = n_current;
            let mut ris_tail = Vec::with_capacity(yr_log_n);
            for j in 0..yr_log_n {
                let ri = t.sample(b);
                t_r = quad.eval(b, ri);
                ris_tail.push(ri);
                if j + 1 < yr_log_n {
                    quad = Quad::recv(b, t, t_r);
                }
            }

            b.scope("terminal", |b| {
                let mut weight = None;
                for ctx in &level_ctxs {
                    assert!(
                        ctx.log_msg_cols >= yr_log_n && ctx.ris_start + (ctx.log_msg_cols - yr_log_n) <= ris.len(),
                        "level {i} of the configuration does not fit the witness"
                    );
                    let folded = ctx.log_msg_cols - yr_log_n;
                    let mut point = ris[ctx.ris_start..ctx.ris_start + folded].to_vec();
                    point.extend_from_slice(&ris_tail);
                    let at = induce_at(b, ctx.log_msg_cols, &ctx.queries, &ctx.weights, &point);
                    weight = Some(mac(b, weight, Some(ctx.beta), at));
                }
                for ctx in &ood_ctxs {
                    assert!(
                        ctx.z.len() >= yr_log_n && ctx.ris_start + (ctx.z.len() - yr_log_n) <= ris.len(),
                        "level {i} of the configuration does not fit the witness"
                    );
                    let folded = ctx.z.len() - yr_log_n;
                    let mut scalar = ctx.beta;
                    let at = ris[ctx.ris_start..ctx.ris_start + folded].iter().chain(&ris_tail);
                    for (&z, &x) in ctx.z.iter().zip(at) {
                        let s = b.add(z, x);
                        scalar = math::times_one_plus(b, scalar, s);
                    }
                    weight = Some(weight.map_or(scalar, |w| b.add(scalar, w)));
                }
                let mut full_point = ris.clone();
                full_point.extend_from_slice(&ris_tail);
                full_point.rotate_left(initial_k);
                let weight = eval_b_at(b, &full_point, weight);
                let folded_yr = mle(b, &yr, &ris_tail);
                let lhs = b.mul(weight, folded_yr);
                b.eq_e(lhs, t_r);
            });
            return;
        }

        let root_next = t.next_root(b);
        let level_ood: Vec<Ood> = (0..config.ood_samples()[i + 2])
            .map(|_| replay_ood(b, t, n_current))
            .collect();
        let ood_ris_start = ris.len();
        t.grind_check(b, config.grinding_bits()[i + 1] as u32);

        let num_queries_i = config.queries()[i + 1];
        let queries_i = sample_queries(b, t, prev.log_msg_cols + prev.log_inv_rate, num_queries_i);
        let lambda_i = t.sample(b);
        let weights_i = powers(b, lambda_i, num_queries_i);
        let rows_i = b.scope(format!("L{} rows", i + 1), |b| open_e_rows(b, t, &prev, &queries_i));
        let enforced_sum_i = enforced_sum_e(b, &rows_i, &level_rs, &weights_i);
        let intro_i = Quad::recv(b, t, enforced_sum_i);
        let (ood_scalars_i, query_scalar_i) =
            batch_level_claims(b, lambda_i, &level_ood, intro_i, enforced_sum_i, &mut t_r, &mut quad);
        ood_ctxs.extend(level_ood.into_iter().zip(ood_scalars_i).map(|(ood, beta)| OodCtx {
            z: ood.z,
            ris_start: ood_ris_start,
            beta,
        }));
        level_ctxs.push(LevelCtx {
            log_msg_cols: n_current,
            queries: queries_i,
            weights: weights_i,
            ris_start: ris.len(),
            beta: query_scalar_i,
        });

        let k_next = config.level_ks()[i + 1];
        prev = PrevLevel {
            root: root_next,
            log_num_interleaved: k_next,
            log_msg_cols: n_current
                .checked_sub(k_next)
                .unwrap_or_else(|| panic!("level {i} of the configuration does not fit the witness")),
            log_inv_rate: config.log_inv_rates()[i + 2],
        };
    }
    unreachable!("the configuration has at least one level")
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::pcs::{RingSwitchClaim, RingSwitchOpen, RingSwitchVerify, SlotClaim};
    use crate::rec::circuit::{Circuit, Limbs};
    use crate::rec::inner::SliceClaim;
    use crate::rec::transcript::Source;
    use crate::witness::StackShape;
    use ::pcs::ring_switch::fold_1b_rows;
    use ::pcs::stack_open::RingSwitchVerifyClaim;
    use ::pcs::whir::inner_product_base_ext;
    use fiat_shamir::transcript::{ProverState, RawProof, VerifierState};
    use primitives::test_rng::Rng;

    const LABEL: &[u8] = b"rec-inner-pcs-test";
    /// Fewer lanes than a leaf holds, and not whole blocks of them, so the L0 image has a zero prefix.
    const N_LANES: usize = 37;

    #[derive(Clone)]
    struct Ring {
        offset: usize,
        qflock_vars: usize,
        /// Each claim's suffix point and slices.
        claims: Vec<(Vec<F192>, Vec<F192>)>,
    }

    /// Point and Strided claims and two ring-switched regions on a stack of `N_LANES` lanes, their values
    /// read from `q` when there is one.
    fn claims(mu: usize, q: Option<&[F64]>, rng: &mut Rng) -> (Vec<SlotClaim>, Vec<Ring>) {
        let lane = 1usize << (mu - crate::pcs::LOG_BATCH);
        let eq = primitives::multilinear::eq_table;
        let mut slots = Vec::new();
        for (offset, vars) in [(0, mu - 6), (2 * lane, mu - 5), (8, 3), (5, 0)] {
            let low_point = rng.ext_vec(vars);
            let value = q.map_or(F192::ZERO, |q| {
                inner_product_base_ext(&q[offset..offset + (1 << vars)], &eq(&low_point))
            });
            slots.push(SlotClaim::Point {
                offset,
                low_point,
                value,
            });
        }
        for (offset, slot, stride_log) in [(4 * lane, 5, 3), (6 * lane, 0, 0)] {
            let point = rng.ext_vec(mu - 6 - stride_log);
            let value = q.map_or(F192::ZERO, |q| {
                eq(&point).iter().enumerate().fold(F192::ZERO, |acc, (j, e)| {
                    acc + e.mul_base(q[offset + slot + (j << stride_log)])
                })
            });
            slots.push(SlotClaim::Strided {
                offset,
                slot,
                stride_log,
                point,
                value,
            });
        }
        let rings = [(4 * lane, mu - 4, 2), (16 * lane, mu - 5, 1)]
            .into_iter()
            .map(|(offset, qflock_vars, n_claims)| Ring {
                offset,
                qflock_vars,
                claims: (0..n_claims)
                    .map(|_| {
                        let suffix_point = rng.ext_vec(qflock_vars);
                        let s_hat_v = q.map_or_else(
                            || vec![F192::ZERO; PACKING_WIDTH],
                            |q| fold_1b_rows(&q[offset..offset + (1 << qflock_vars)], &eq(&suffix_point)),
                        );
                        (suffix_point, s_hat_v)
                    })
                    .collect(),
            })
            .collect();
        (slots, rings)
    }

    fn label_cv() -> Limbs {
        let d = primitives::hash::hash(LABEL);
        std::array::from_fn(|i| u64::from_le_bytes(d[8 * i..8 * i + 8].try_into().expect("eight bytes")))
    }

    /// The circuit replaying `raw` (zeros for `Source::Shape`), its failures, and whether it read the whole
    /// proof.
    fn build(
        shape: StackShape,
        log_inv_rate: usize,
        slots: &[SlotClaim],
        rings: &[Ring],
        source: Source,
        mode: RingMode,
    ) -> (Circuit, Vec<String>, bool) {
        let shaped = matches!(source, Source::Shape);
        let mut b = Builder::new();
        let wire = |b: &mut Builder, v: &F192| b.free_e(if shaped { F192::ZERO } else { *v });
        let cv = b.d_const(label_cv());
        let mut t = Transcript::from_state(cv, source);
        let root = t.next_root(&mut b);
        let slot_wires: Vec<StackClaim> = slots
            .iter()
            .map(|claim| match claim {
                SlotClaim::Point {
                    offset,
                    low_point,
                    value,
                } => StackClaim::Point {
                    offset: *offset,
                    low_point: low_point.iter().map(|v| wire(&mut b, v)).collect(),
                    value: wire(&mut b, value),
                },
                SlotClaim::Strided {
                    offset,
                    slot,
                    stride_log,
                    point,
                    value,
                } => StackClaim::Strided {
                    offset: *offset,
                    slot: *slot,
                    stride_log: *stride_log,
                    point: point.iter().map(|v| wire(&mut b, v)).collect(),
                    value: wire(&mut b, value),
                },
            })
            .collect();
        let ring_wires: Vec<RingRegion> = rings
            .iter()
            .map(|ring| RingRegion {
                offset: ring.offset,
                qflock_vars: ring.qflock_vars,
                claims: ring
                    .claims
                    .iter()
                    .map(|(suffix_point, s_hat_v)| SliceClaim {
                        suffix_point: suffix_point.iter().map(|v| wire(&mut b, v)).collect(),
                        s_hat_v: s_hat_v.iter().map(|v| wire(&mut b, v)).collect(),
                    })
                    .collect(),
            })
            .collect();
        verify(
            &mut b,
            &mut t,
            &slot_wires,
            &ring_wires,
            shape,
            log_inv_rate,
            root,
            mode,
        );
        let finished = t.finished();
        let (circuit, _, failures) = b.finish();
        (circuit, failures, finished)
    }

    /// Commit and open natively, verify natively, then replay the verification in the circuit, the
    /// ring-switched share settled as `mode` says.
    fn check(mu: usize, log_inv_rate: usize, seed: u64, mode: RingMode) {
        let mut rng = Rng::new(seed);
        let shape = StackShape { mu, n_lanes: N_LANES };
        let q: Vec<F64> = (0..shape.committed_len()).map(|_| F64(rng.next_u64())).collect();
        let (slots, rings) = claims(mu, Some(&q), &mut rng);

        let mut ps = ProverState::from_label(LABEL);
        let committed = crate::pcs::commit(&mut ps, &q, shape, log_inv_rate);
        let opens: Vec<RingSwitchOpen> = rings
            .iter()
            .map(|ring| RingSwitchOpen {
                offset: ring.offset,
                qflock_vars: ring.qflock_vars,
                claims: ring
                    .claims
                    .iter()
                    .enumerate()
                    .map(|(i, (suffix_point, s_hat_v))| RingSwitchClaim {
                        suffix_point: suffix_point.clone(),
                        // The first claim of each region folds its slices from the witness.
                        s_hat_v: (i > 0).then(|| s_hat_v.clone()),
                    })
                    .collect(),
            })
            .collect();
        crate::pcs::open(&mut ps, &committed, &q, &slots, &opens);
        let proof = ps.into_proof();

        let verifies: Vec<RingSwitchVerify> = rings
            .iter()
            .map(|ring| RingSwitchVerify {
                offset: ring.offset,
                qflock_vars: ring.qflock_vars,
                claims: ring
                    .claims
                    .iter()
                    .map(|(suffix_point, s_hat_v)| RingSwitchVerifyClaim {
                        suffix_point,
                        s_hat_v: s_hat_v.as_slice().try_into().expect("64 slices"),
                    })
                    .collect(),
            })
            .collect();
        let mut vs = VerifierState::from_label(LABEL, &proof);
        let root = crate::pcs::read_commitment(&mut vs).expect("root");
        crate::pcs::verify(&mut vs, &slots, &verifies, shape, log_inv_rate, &root).expect("native verify");
        vs.finish().expect("native verify consumes the proof");
        let raw = vs.into_raw_proof();

        let what = format!("mu {mu}, log_inv_rate {log_inv_rate}, {mode:?}");
        let build = |slots: &[SlotClaim], rings: &[Ring], source: Source<'_>| {
            build(shape, log_inv_rate, slots, rings, source, mode)
        };
        let (circuit, failures, finished) = build(&slots, &rings, Source::Proof(&raw));
        assert!(failures.is_empty(), "{what}: {failures:?}");
        assert!(finished, "{what}: the circuit left part of the proof unread");
        let (shaped, _, _) = build(&slots, &rings, Source::Shape);
        assert!(circuit == shaped, "{what}: the shape builds another circuit");

        let mut bad = RawProof {
            stream: raw.stream.clone(),
            merkle: raw.merkle.clone(),
        };
        let mid = bad.stream.len() / 2;
        bad.stream[mid].c1 ^= 1;
        let (_, failures, _) = build(&slots, &rings, Source::Proof(&bad));
        assert!(!failures.is_empty(), "{what}: a tampered scalar passes");

        // Every claim reaches the terminal check.
        for i in 0..slots.len() {
            let mut bad = slots.clone();
            match &mut bad[i] {
                SlotClaim::Point { value, .. } | SlotClaim::Strided { value, .. } => *value += F192::ONE,
            }
            let (_, failures, _) = build(&bad, &rings, Source::Proof(&raw));
            assert!(
                failures.iter().any(|f| f.contains("terminal")),
                "{what}: a wrong value of slot claim {i} passes: {failures:?}"
            );
        }
        for r in 0..rings.len() {
            for c in 0..rings[r].claims.len() {
                let mut bad = rings.clone();
                bad[r].claims[c].1[7] += F192::ONE;
                let (_, failures, _) = build(&slots, &bad, Source::Proof(&raw));
                assert!(
                    failures.iter().any(|f| f.contains("terminal")),
                    "{what}: a wrong slice of ring {r} claim {c} passes: {failures:?}"
                );
            }
        }

        for opening in [0, raw.merkle.len() - 1] {
            let mut bad = RawProof {
                stream: raw.stream.clone(),
                merkle: raw.merkle.clone(),
            };
            bad.merkle[opening].path[1][0] ^= 1;
            let (_, failures, _) = build(&slots, &rings, Source::Proof(&bad));
            assert!(
                !failures.is_empty(),
                "{what}: a tampered sibling of opening {opening} passes"
            );
        }
    }

    #[test]
    fn the_circuit_replays_the_smallest_opening() {
        check(crate::pcs::MIN_MU, 1, 1, RingMode::Hint);
        check(crate::pcs::MIN_MU, 2, 2, RingMode::Prove);
    }

    #[test]
    fn the_circuit_replays_a_larger_opening() {
        check(20, 1, 3, RingMode::Prove);
        check(20, 2, 4, RingMode::Hint);
    }
}
