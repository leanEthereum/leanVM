//! The stacked opening in rows: the claims batched under one challenge, then the succinct WHIR verifier.
//!
//! Every query opens a full Merkle path whose directions are the query's bits, so the rows never depend on which rows are opened.

use super::ring::RingShare;
use super::{Rows, infallible};
use crate::arith::{Arith, Verifier};
use crate::pcs::SlotClaim;
use crate::rec::circuit::{Dw, Ew, Kw};
use crate::witness::StackShape;
use ::pcs::ring_switch::COMPOSITION_SHIFTS;
use ::pcs::stack_open::RingSwitchVerify;
use ::pcs::whir::{VerifierConfig, config_for_rate, eval_sk_at_vks};
use primitives::field::{F64, F192};

/// One opening of the committed stack: its point claims and its ring-switched regions.
pub(super) struct Opening<'a, 'r> {
    /// The point claims, each on an aligned slice of the stack.
    pub(super) slots: &'a [SlotClaim<Ew>],
    /// The ring-switched regions, their claims' slices bound upstream.
    pub(super) rings: &'a [RingSwitchVerify<'r, Ew>],
    /// The committed stack's size and its committed lanes.
    pub(super) shape: StackShape,
    /// The commitment's base-two logarithm of the inverse rate.
    pub(super) log_inv_rate: usize,
}

/// A round's quadratic `c + b X + a X^2`.
#[derive(Clone, Copy)]
struct Quad {
    c: Ew,
    b: Ew,
    a: Ew,
}

/// An out-of-domain claim on a level's oracle: its point, its value, and its intro round.
struct Ood {
    z: Vec<Ew>,
    y: Ew,
    intro: Quad,
}

/// What a level's query batch leaves for the terminal weight.
struct LevelCtx {
    log_msg_cols: usize,
    /// Each query's index bits, lowest first.
    queries: Vec<Vec<Kw>>,
    /// One power of the level's batching challenge per query.
    weights: Vec<Ew>,
    /// Where the level's fold challenges start among all of them.
    ris_start: usize,
    /// The level's power in the running claim.
    beta: Ew,
}

/// What an out-of-domain claim leaves for the terminal weight.
struct OodCtx {
    z: Vec<Ew>,
    ris_start: usize,
    beta: Ew,
}

/// The oracle the next query batch opens.
struct Oracle {
    root: Dw,
    log_num_interleaved: usize,
    log_msg_cols: usize,
    log_inv_rate: usize,
}

/// One level's query batch: its grinding, its index width and its count.
#[derive(Clone, Copy)]
struct QueryPhase {
    grinding: u32,
    depth: usize,
    count: usize,
}

/// The succinct WHIR verifier's state as it runs in rows.
struct WhirReplay<'c> {
    config: &'c VerifierConfig,
    /// The running claim and its round's quadratic.
    t_r: Ew,
    quad: Quad,
    /// Every fold challenge, in round order.
    ris: Vec<Ew>,
    levels: Vec<LevelCtx>,
    oods: Vec<OodCtx>,
}

impl Opening<'_, '_> {
    /// Verify the opening of the commitment `root`.
    ///
    /// The family takes the batching challenge's power one, and point claim `i` its power `i + 1`.
    pub(super) fn verify(&self, r: &mut Rows<'_, '_>, root: Dw) {
        let log_n = self.shape.mu;
        let config = config_for_rate(log_n, self.log_inv_rate)
            .unwrap_or_else(|e| panic!("a valid shape has a configuration for mu {log_n}: {e}"));
        self.check_shape();

        let gamma_rs = r.sample();
        let map = r.sample_vec(COMPOSITION_SHIFTS.len());
        let lambda = r.sample();
        let lambdas = r.powers(lambda, 1 + self.slots.len());
        let family = RingShare::new(r, self.rings, gamma_rs, &map);
        let target = r.scope("target", |r| {
            let family_target = family.target(r);
            (self.slots.iter().zip(&lambdas[1..]))
                .fold(family_target, |acc, (claim, &g)| r.mul_add(g, claim.value(), acc))
        });
        let weight_at = |r: &mut Rows<'_, '_>, x: &[Ew]| {
            let family_weight = family.weight_at(r, x);
            (self.slots.iter().zip(&lambdas[1..])).fold(family_weight, |acc, (claim, &g)| {
                let eq = Self::claim_eq_at(r, claim, x);
                r.mul_add(g, eq, acc)
            })
        };
        r.scope("whir", |r| {
            WhirReplay::run(r, &config, self.shape, target, root, weight_at);
        });
    }

    /// A point claim's weight `eq(full claim point, x)` at the stack point `x`.
    ///
    /// A plain claim's full point is its low point then its offset's bits.
    ///
    /// A strided claim's is its slot's bits, its point, then its offset's bits.
    fn claim_eq_at(r: &mut Rows<'_, '_>, claim: &SlotClaim<Ew>, x: &[Ew]) -> Ew {
        match claim {
            SlotClaim::Point { offset, low_point, .. } => {
                let n = low_point.len();
                let low = r.eq_eval(low_point, &x[..n]);
                let sel = r.eq_bits(offset >> n, &x[n..]);
                r.mul(low, sel)
            }
            SlotClaim::Strided {
                offset,
                slot,
                stride_log,
                point,
                ..
            } => {
                let block = stride_log + point.len();
                let slot = r.eq_bits(*slot, &x[..*stride_log]);
                let low = r.eq_eval(point, &x[*stride_log..block]);
                let sel = r.eq_bits(offset >> block, &x[block..]);
                let inner = r.mul(slot, low);
                r.mul(inner, sel)
            }
        }
    }

    /// The statement's invariants the native verifier asserts: every region and claim inside the committed cube.
    fn check_shape(&self) {
        let cube = 1usize << self.shape.mu;
        assert!(
            self.rings.iter().any(|ring| !ring.claims.is_empty()),
            "an opening has a ring-switched claim"
        );
        for ring in self.rings {
            assert!(ring.offset.is_multiple_of(1 << ring.qflock_vars), "a region is aligned");
            assert!(
                ring.offset + (1 << ring.qflock_vars) <= cube,
                "a region is inside the cube"
            );
            assert!(
                ring.claims.iter().all(|c| c.suffix_point.len() == ring.qflock_vars),
                "a claim spans its region"
            );
        }
        assert!(
            self.slots.iter().all(|c| c.range().1 <= cube),
            "every claim is inside the cube"
        );
    }
}

impl Quad {
    /// The next round's quadratic, its linear coefficient fixed by the running claim.
    fn recv(r: &mut Rows<'_, '_>, claim: Ew) -> Self {
        let h = infallible(r.next_round_poly(3, claim, None));
        Self {
            c: h[0],
            b: h[1],
            a: h[2],
        }
    }

    fn eval(self, r: &mut Rows<'_, '_>, x: Ew) -> Ew {
        let u = r.mul_add(self.a, x, self.b);
        r.mul_add(u, x, self.c)
    }

    /// `self + s·other`.
    fn fold(self, r: &mut Rows<'_, '_>, other: Self, s: Ew) -> Self {
        Self {
            c: r.mul_add(s, other.c, self.c),
            b: r.mul_add(s, other.b, self.b),
            a: r.mul_add(s, other.a, self.a),
        }
    }
}

impl Ood {
    /// Draw an out-of-domain point, then read its value and its intro round.
    fn replay(r: &mut Rows<'_, '_>, n_vars: usize) -> Self {
        let z = r.sample_vec(n_vars);
        let y = infallible(r.next_scalar());
        let intro = Quad::recv(r, y);
        Self { z, y, intro }
    }
}

impl LevelCtx {
    /// The level's induced basis at `point`: `sum_i w_i prod_k (1 + p_k (1 + s_k(q_i) / s_k(v_k)))`, `q_i` the query index in `K`.
    fn basis_at(&self, r: &mut Rows<'_, '_>, point: &[Ew]) -> Ew {
        assert_eq!(point.len(), self.log_msg_cols, "a point of the level's cube");
        let sks = eval_sk_at_vks(self.log_msg_cols);
        // `1 + p (1 + s / sigma) = (1 + p) + (p / sigma) s`.
        let lin: Vec<(Ew, Ew)> = (point.iter().zip(&sks))
            .map(|(&p, &sigma)| {
                let inv = if sigma == F64(0) { F64(0) } else { sigma.inv() };
                (r.add_const(p, F192::ONE), r.mul_const(p, F192::from(inv)))
            })
            .collect();
        let zero = r.zero();
        (self.queries.iter().zip(&self.weights)).fold(zero, |acc, (bits, &w)| {
            let q = r.b.pack(bits);
            let mut s = r.b.k_to_e1(q);
            let mut product = r.one();
            for (k, &(a, c)) in lin.iter().enumerate() {
                if k > 0 {
                    // The subspace polynomials' recurrence `s_k = s_{k-1}^2 + s_{k-1}(v_{k-1}) s_{k-1}`.
                    let u = r.mul_const(s, F192::from(sks[k - 1]));
                    s = r.mul_add(s, s, u);
                }
                let f = r.mul_add(c, s, a);
                product = r.mul(product, f);
            }
            r.mul_add(w, product, acc)
        })
    }
}

impl QueryPhase {
    /// Each query's index bits, lowest first, cut from the 192 bits of a challenge `c0 | c1 << 64 | c2 << 128`.
    fn sample(self, r: &mut Rows<'_, '_>) -> Vec<Vec<Kw>> {
        let per = 192 / self.depth;
        let mut out = Vec::with_capacity(self.count);
        while out.len() < self.count {
            let v = r.sample();
            let n = per.min(self.count - out.len());
            let limbs = r.b.e_to_k(v);
            let mut bits = Vec::with_capacity(192);
            for &limb in &limbs[..(n * self.depth).div_ceil(64)] {
                bits.extend(r.b.split(limb));
            }
            out.extend((0..n).map(|j| bits[j * self.depth..(j + 1) * self.depth].to_vec()));
        }
        out
    }
}

impl Oracle {
    /// The width of a query's index bits.
    const fn depth(&self) -> usize {
        self.log_msg_cols + self.log_inv_rate
    }

    /// Open each query's row of `E` elements, three words each.
    fn open_e_rows(&self, r: &mut Rows<'_, '_>, queries: &[Vec<Kw>]) -> OpenedRows<Ew> {
        let leaf_words = 3 << self.log_num_interleaved;
        let rows = (queries.iter())
            .map(|bits| {
                let words = r.t.open_row(r.b, self.root, bits, leaf_words, leaf_words);
                words.chunks(3).map(|c| r.b.k_to_e([c[0], c[1], c[2]])).collect()
            })
            .collect();
        OpenedRows(rows)
    }
}

impl<'c> WhirReplay<'c> {
    /// The succinct WHIR verifier in rows.
    ///
    /// The caller's weight is evaluated once, at the terminal point indexed by witness coordinate.
    fn run(
        r: &mut Rows<'_, '_>,
        config: &'c VerifierConfig,
        shape: StackShape,
        target: Ew,
        root: Dw,
        weight_at: impl FnOnce(&mut Rows<'_, '_>, &[Ew]) -> Ew,
    ) {
        let initial_k = config.initial_k();
        let max = 1usize << initial_k;
        assert!(
            shape.n_lanes != 0 && shape.n_lanes <= max,
            "a leaf holds 1 to {max} lanes"
        );
        let quad = Quad::recv(r, target);
        let mut w = Self {
            config,
            t_r: target,
            quad,
            ris: Vec::new(),
            levels: Vec::new(),
            oods: Vec::new(),
        };
        let mut n_current = shape.mu - initial_k;
        let lane_fold = w.fold_rounds(r, initial_k);
        let root_1 = r.t.next_root(r.b);
        let oods = (0..config.ood_samples()[1])
            .map(|_| Ood::replay(r, n_current))
            .collect();
        let phase = w.phase(0, n_current + config.log_inv_rates()[0]);
        // The proof stores the committed lanes, the image's tail; the image is lane-descending.
        w.query(r, phase, oods, n_current, |r, queries, weights| {
            let rows: Vec<Vec<Kw>> = (queries.iter())
                .map(|bits| {
                    let mut row = r.t.open_row(r.b, root, bits, shape.n_lanes, max);
                    row.reverse();
                    row
                })
                .collect();
            OpenedRows(rows).enforced_sum(r, &lane_fold, weights)
        });

        let mut oracle = w.oracle(root_1, 0, n_current);
        for i in 0..config.level_steps() {
            let k = config.level_ks()[i];
            assert!(
                n_current >= k,
                "level {i} of the configuration does not fit the witness"
            );
            let level_rs = w.fold_rounds(r, k);
            n_current -= k;
            if i + 1 == config.level_steps() {
                return w.last_level(r, &oracle, &level_rs, n_current, weight_at);
            }
            let root = r.t.next_root(r.b);
            let oods = (0..config.ood_samples()[i + 2])
                .map(|_| Ood::replay(r, n_current))
                .collect();
            let phase = w.phase(i + 1, oracle.depth());
            w.query(r, phase, oods, n_current, |r, queries, weights| {
                let rows = oracle.open_e_rows(r, queries);
                rows.enforced_sum(r, &level_rs, weights)
            });
            oracle = w.oracle(root, i + 1, n_current);
        }
        unreachable!("the configuration has at least one level")
    }

    /// Level `level`'s query batch over indices of `depth` bits.
    fn phase(&self, level: usize, depth: usize) -> QueryPhase {
        QueryPhase {
            grinding: u32::try_from(self.config.grinding_bits()[level]).expect("a few grinding bits"),
            depth,
            count: self.config.queries()[level],
        }
    }

    /// The oracle a level's fold commits, on the variables left after it.
    fn oracle(&self, root: Dw, level: usize, n_current: usize) -> Oracle {
        let k = self.config.level_ks()[level];
        Oracle {
            root,
            log_num_interleaved: k,
            log_msg_cols: n_current.checked_sub(k).expect("the configuration fits the witness"),
            log_inv_rate: self.config.log_inv_rates()[level + 1],
        }
    }

    /// `k` fold rounds: each draws a challenge, evaluates the running quadratic, and reads the next.
    fn fold_rounds(&mut self, r: &mut Rows<'_, '_>, k: usize) -> Vec<Ew> {
        let rs: Vec<Ew> = (0..k)
            .map(|_| {
                let ri = r.sample();
                self.t_r = self.quad.eval(r, ri);
                self.quad = Quad::recv(r, self.t_r);
                ri
            })
            .collect();
        self.ris.extend_from_slice(&rs);
        rs
    }

    /// One query batch: grind, draw the queries and their batching challenge, open them, then batch the level's claims.
    ///
    /// `enforced` opens the queries and returns their weighted sum at the level's fold point.
    fn query(
        &mut self,
        r: &mut Rows<'_, '_>,
        phase: QueryPhase,
        oods: Vec<Ood>,
        log_msg_cols: usize,
        enforced: impl FnOnce(&mut Rows<'_, '_>, &[Vec<Kw>], &[Ew]) -> Ew,
    ) {
        r.t.grind_check(r.b, phase.grinding);
        let queries = phase.sample(r);
        let lambda = r.sample();
        let weights = r.powers(lambda, phase.count);
        let sum = r.scope("rows", |r| enforced(r, &queries, &weights));
        let intro = Quad::recv(r, sum);

        // The OOD claims, then the query batch, each at the next power of the level's challenge.
        let ris_start = self.ris.len();
        let mut scalar = r.one();
        for ood in oods {
            scalar = r.mul(scalar, lambda);
            self.quad = self.quad.fold(r, ood.intro, scalar);
            self.t_r = r.mul_add(scalar, ood.y, self.t_r);
            self.oods.push(OodCtx {
                z: ood.z,
                ris_start,
                beta: scalar,
            });
        }
        scalar = r.mul(scalar, lambda);
        self.quad = self.quad.fold(r, intro, scalar);
        self.t_r = r.mul_add(scalar, sum, self.t_r);
        self.levels.push(LevelCtx {
            log_msg_cols,
            queries,
            weights,
            ris_start,
            beta: scalar,
        });
    }

    /// The last level: its residual polynomial, its query batch, the residual rounds, then the terminal check.
    fn last_level(
        mut self,
        r: &mut Rows<'_, '_>,
        oracle: &Oracle,
        level_rs: &[Ew],
        n_current: usize,
        weight_at: impl FnOnce(&mut Rows<'_, '_>, &[Ew]) -> Ew,
    ) {
        let yr = infallible(r.next_scalars(1 << n_current));
        let phase = self.phase(self.config.level_steps(), oracle.depth());
        self.query(r, phase, Vec::new(), n_current, |r, queries, weights| {
            let rows = oracle.open_e_rows(r, queries);
            rows.enforced_sum(r, level_rs, weights)
        });
        let mut ris_tail = Vec::with_capacity(n_current);
        for j in 0..n_current {
            let ri = r.sample();
            self.t_r = self.quad.eval(r, ri);
            ris_tail.push(ri);
            if j + 1 < n_current {
                self.quad = Quad::recv(r, self.t_r);
            }
        }
        r.scope("terminal", |r| self.terminal(r, &yr, &ris_tail, weight_at));
    }

    /// `weight · <yr, eq(ris_tail)> = t_r`, the weight every level's basis, every OOD claim and the caller's at the full point.
    fn terminal(
        &self,
        r: &mut Rows<'_, '_>,
        yr: &[Ew],
        ris_tail: &[Ew],
        weight_at: impl FnOnce(&mut Rows<'_, '_>, &[Ew]) -> Ew,
    ) {
        let tail = ris_tail.len();
        let zero = r.zero();
        let mut weight = zero;
        for ctx in &self.levels {
            let folded = ctx.log_msg_cols - tail;
            let mut point = self.ris[ctx.ris_start..ctx.ris_start + folded].to_vec();
            point.extend_from_slice(ris_tail);
            let at = ctx.basis_at(r, &point);
            weight = r.mul_add(ctx.beta, at, weight);
        }
        for ctx in &self.oods {
            let folded = ctx.z.len() - tail;
            let at = self.ris[ctx.ris_start..ctx.ris_start + folded].iter().chain(ris_tail);
            let mut scalar = ctx.beta;
            for (&z, &x) in ctx.z.iter().zip(at) {
                let s = r.add(z, x);
                scalar = r.times_one_plus(scalar, s);
            }
            weight = r.add(weight, scalar);
        }
        // The fold challenges in round order; the first `initial_k` bind the witness's top variables.
        let mut full_point = self.ris.clone();
        full_point.extend_from_slice(ris_tail);
        full_point.rotate_left(self.config.initial_k());
        let caller = weight_at(r, &full_point);
        let weight = r.add(weight, caller);
        let folded_yr = r.mle(yr, ris_tail);
        let lhs = r.mul(weight, folded_yr);
        r.b.eq_e(lhs, self.t_r);
    }
}

/// The rows a query batch opened, one per query.
struct OpenedRows<T>(Vec<Vec<T>>);

impl OpenedRows<Kw> {
    /// The level-0 enforced sum over `K` rows: `sum_i w_i <row_i, eq(v, .)>`.
    ///
    /// Each row's inner product is its own, so the first query's weight, one, costs no row.
    fn enforced_sum(&self, r: &mut Rows<'_, '_>, v: &[Ew], weights: &[Ew]) -> Ew {
        let rows = &self.0;
        let eq = r.eq_table_prefix(v, rows[0].len());
        let zero = r.zero();
        (rows.iter().zip(weights)).fold(zero, |acc, (row, &w)| {
            let inner = (eq.iter().zip(row)).fold(zero, |s, (&e, &k)| r.b.mul_k_add(e, k, s));
            r.mul_add(w, inner, acc)
        })
    }
}

impl OpenedRows<Ew> {
    /// A later level's enforced sum over `E` rows: `sum_l eq(v, l) sum_i w_i row_i[l]`.
    fn enforced_sum(&self, r: &mut Rows<'_, '_>, v: &[Ew], weights: &[Ew]) -> Ew {
        let rows = &self.0;
        let eq = r.eq_table_prefix(v, rows[0].len());
        let zero = r.zero();
        (eq.iter().enumerate()).fold(zero, |acc, (l, &e)| {
            let column = (rows.iter().zip(weights)).fold(zero, |s, (row, &w)| r.mul_add(w, row[l], s));
            r.mul_add(e, column, acc)
        })
    }
}
