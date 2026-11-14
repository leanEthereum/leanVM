//! The layer prover.
//!
//! One layer makes three passes over the bits of the states it reduces to:
//!
//! 1. the product polynomial, before its evaluation point `s` is known;
//! 2. once per sumcheck round over the packs of half a block, folding them at the challenges so
//!    far;
//! 3. one field element per half block and position, for the rounds that remain.
//!
//! At `s`, a pack's value is the sum of the instance weights of its set bits, so a folded pack is
//! a sum of byte lookups ([`PackFold`]).

use fiat_shamir::transcript::ProverState;
use primitives::field::{F128, F128Unreduced};
use primitives::multilinear::{eq_table, interp, poly_eval};

use crate::keccak::{BITS, LOCAL_VARS, along, linear_transpose, row_positions};
use crate::kernels::byte_sums;
use crate::kernels::{GROUP, PACKS, SKIP, embed, products};
use crate::open::fold;
use crate::protocol::{Claim, chi_weights, mu_at};
use crate::rmfe::{PACK, PROD_BITS};
use crate::witness::{Shape, Witness, words};

/// The bytes of a product of two embeddings.
const PROD_BYTES: usize = PROD_BITS.div_ceil(8);

struct Layer<'a> {
    witness: &'a Witness,
    /// The round whose `chi` each segment's claim is on.
    rounds: Vec<usize>,
}

/// A row of a table: a value per position.
const ROW: usize = BITS;

impl Layer<'_> {
    /// The blocks a segment's tasks walk: those written, then the padding block once, standing
    /// for every block after them.
    fn held(&self) -> usize {
        let written = self.witness.written();
        written + usize::from(written < self.witness.shape.n_blocks())
    }

    /// Task `held * segment + g`, as `(segment, g, block)`.
    fn block(&self, task: usize) -> (usize, usize, &[u64]) {
        let (segment, g) = (task / self.held(), task % self.held());
        (segment, g, self.witness.layer(self.rounds[segment], g))
    }

    fn n_tasks(&self) -> usize {
        self.rounds.len() * self.held()
    }

    /// Each task's weight in `eq`, a table over the blocks then the segment: the padding block's
    /// is the sum over the blocks it stands for.
    fn task_weights(&self, eq: &[F128]) -> Vec<F128> {
        let nb = self.witness.shape.n_blocks();
        (0..self.n_tasks())
            .map(|task| {
                let (segment, g) = (task / self.held(), task % self.held());
                let eq = &eq[nb * segment..][..nb];
                if g < self.witness.written() {
                    eq[g]
                } else {
                    eq[g..].iter().sum()
                }
            })
            .collect()
    }

    /// The product polynomial `U`: the coefficients of
    /// `sum over packs, segments and positions of eq(point, (pack, segment)) * weights[j] * product(pack, j)`,
    /// where the product is `ones * u[j] + (ones + u[j + 1]) * u[j + 2]` on embeddings, the
    /// unprojected `chi`.
    ///
    /// Nothing here knows where the polynomials will be evaluated, so each product meets its
    /// weight bit by bit: byte `b` of a product picks one of 256 buckets of that byte, which the
    /// weight goes to, and coefficient `8 b + t` sums byte `b`'s buckets whose value has bit `t`.
    /// The buckets of a block meet its weight once, at its end.
    fn product(&self, claim: &Claim) -> [F128; PROD_BITS] {
        // Per position, its weight times each pack's of a block.
        let packs = eq_table(&claim.point[..SKIP + 1]);
        let weights: Vec<[F128; PACKS]> = claim
            .weights
            .iter()
            .map(|&w| std::array::from_fn(|q| packs[q] * w))
            .collect();
        let tasks = self.task_weights(&eq_table(&claim.point[SKIP + 1..]));
        let buckets = parallel::map_reduce_with_state(
            self.n_tasks(),
            || vec![[F128::ZERO; 256]; PROD_BYTES],
            || vec![[F128Unreduced::ZERO; 256]; PROD_BYTES],
            |block_buckets, buckets, task| {
                let (_, _, block) = self.block(task);
                block_buckets.fill([F128::ZERO; 256]);
                for r in 0..5 {
                    for z in 0..64 {
                        let js = row_positions(r, z);
                        let e: [[u32; PACKS]; 5] = std::array::from_fn(|x| embed(words(block, js[x])));
                        for x in 0..5 {
                            let p = products(&e[x], &e[(x + 1) % 5], &e[(x + 2) % 5]);
                            for (&p, &w) in p.iter().zip(&weights[js[x]]) {
                                for (b, bucket) in block_buckets.iter_mut().enumerate() {
                                    bucket[(p >> (8 * b)) as usize & 0xff] += w;
                                }
                            }
                        }
                    }
                }
                for (total, local) in buckets.iter_mut().zip(block_buckets.iter()) {
                    for (total, &local) in total.iter_mut().zip(local) {
                        *total ^= local.mul_unreduced(tasks[task]);
                    }
                }
            },
            |mut a, b| {
                for (a, b) in a.as_flattened_mut().iter_mut().zip(b.as_flattened()) {
                    *a ^= *b;
                }
                a
            },
        );
        std::array::from_fn(|c| {
            (0..256)
                .filter(|v| v >> (c % 8) & 1 == 1)
                .map(|v| buckets[c / 8][v].reduce())
                .sum()
        })
    }

    /// A round over a variable of the packs of a group, from the witness: its values at `0` and
    /// at infinity. `fold` folds the variables already bound, and `inner` is `eq` of the claim's
    /// later variables of the group (pair `c` of group half `h` at `c + pairs * h`), `tasks` each
    /// task's weight in `eq` of the rest.
    fn group_round(&self, summand: &Summand, fold: &PackFold, inner: &[F128], tasks: &[F128]) -> (F128, F128) {
        let pairs = inner.len() / 2;
        let (zero, infinity) = parallel::map_reduce_with_state(
            self.n_tasks(),
            || (vec![F128::ZERO; BITS], vec![F128::ZERO; BITS]),
            || (F128Unreduced::ZERO, F128Unreduced::ZERO),
            |(low, high), acc, task| {
                let (_, _, block) = self.block(task);
                let (mut zero, mut infinity) = (F128Unreduced::ZERO, F128Unreduced::ZERO);
                for half in 0..2 {
                    for c in 0..pairs {
                        for j in 0..BITS {
                            low[j] = fold.value(block, half, j, 2 * c);
                            high[j] = fold.value(block, half, j, 2 * c + 1);
                        }
                        let (z, i) = summand.pair(low, high);
                        let weight = inner[c + pairs * half];
                        zero ^= z.reduce().mul_unreduced(weight);
                        infinity ^= i.reduce().mul_unreduced(weight);
                    }
                }
                acc.0 ^= zero.reduce().mul_unreduced(tasks[task]);
                acc.1 ^= infinity.reduce().mul_unreduced(tasks[task]);
            },
            |a, b| (a.0 ^ b.0, a.1 ^ b.1),
        );
        (zero.reduce(), infinity.reduce())
    }

    /// The table the remaining rounds fold, a row per group: `T[j]`, the value at `s` of position
    /// `j`'s embeddings, folded over the group's packs by `fold`. A block's two groups are the
    /// first of those rounds' pairs, so its round values are summed while the rows are at hand.
    /// The padding block's groups are one row, its segment's entry of `pads`.
    fn table(
        &self,
        summand: &Summand,
        fold: &PackFold,
        eq: &[F128],
        layout: Rows,
        table: &mut [F128],
        pads: &mut [F128],
    ) -> (F128, F128) {
        let weights = self.task_weights(eq);
        // Rows of segments that do not exist are zero, and so is their product.
        table[self.rounds.len() * layout.live * ROW..layout.len() * ROW].fill(F128::ZERO);
        pads[self.rounds.len() * ROW..].fill(F128::ZERO);
        let (ptr, pads) = (
            parallel::SendPtr(table.as_mut_ptr()),
            parallel::SendPtr(pads.as_mut_ptr()),
        );
        let sums = parallel::map_reduce_with_state(
            self.n_tasks(),
            || vec![F128::ZERO; 2 * ROW],
            || (F128Unreduced::ZERO, F128Unreduced::ZERO),
            |rows, sums, task| {
                let (segment, g, block) = self.block(task);
                // SAFETY: each task owns its rows: a written block's two, or its segment's padding row.
                let out = unsafe {
                    if 2 * g < layout.live {
                        ptr.slice((layout.live * segment + 2 * g) * ROW, 2 * ROW)
                    } else {
                        pads.slice(segment * ROW, ROW)
                    }
                };
                let rows = &mut rows[..out.len()];
                for (half, row) in rows.as_chunks_mut::<ROW>().0.iter_mut().enumerate() {
                    for (j, t) in row.iter_mut().enumerate() {
                        *t = fold.value(block, half, j, 0);
                    }
                }
                summand.add_pair(sums, &rows[..ROW], &rows[rows.len() - ROW..], weights[task]);
                // Built in cache for the round values, then published: the next round reads them.
                primitives::stream::Stream::new().copy(out, rows);
            },
            merge,
        );
        finish(sums)
    }
}

/// The packs of a group folded at the challenges bound so far: a pack's value at `s` is the sum of
/// the instance weights of its set bits, so a folded one is a sum of byte lookups.
struct PackFold {
    /// Per assignment `a` of the bound variables, its `eq` weight times each instance weight, as
    /// subset sums of a pack's low byte and of its high byte.
    tables: Vec<[[F128; 256]; 2]>,
}

impl PackFold {
    fn new(mu: &[F128; PACK], challenges: &[F128]) -> Self {
        let tables = eq_table(challenges)
            .iter()
            .map(|&e| [0, 1].map(|k| byte_sums(&std::array::from_fn(|t| e * mu[8 * k + t]))))
            .collect();
        Self { tables }
    }

    /// Entry `b` of position `j` of group `half` of a block: the sum over the bound assignments
    /// `a` of pack `a + 2^bound * b`, weighted.
    fn value(&self, block: &[u64], half: usize, j: usize, b: usize) -> F128 {
        let words = words(block, j);
        let bound = self.tables.len();
        let mut acc = F128::ZERO;
        for (a, tables) in self.tables.iter().enumerate() {
            let q = GROUP * half + a + bound * b;
            let pack = (words[q / 4] >> (16 * (q % 4))) as usize & 0xffff;
            acc += tables[0][pack & 0xff] + tables[1][pack >> 8];
        }
        acc
    }
}

/// What the rounds over packs and segments need of a claim: the position weights, `kappa`, and
/// each position's `kappa * weights[j + 2]`.
struct Summand {
    weights: Vec<F128>,
    constant: Vec<F128>,
    kappa: F128,
}

impl Summand {
    fn new(claim: &Claim, kappa: F128) -> Self {
        Self {
            weights: claim.weights.clone(),
            constant: (0..BITS).map(|j| kappa * claim.weights[along(j, 2)]).collect(),
            kappa,
        }
    }

    /// For rows `low` and `high`, the values at the two points of the variable being bound,
    /// `sum over positions of B[j] * T[j + 2]` at `0` and at infinity, unreduced, where
    /// `B[j] = weights[j] * (kappa + T[j + 1]) + kappa * weights[j + 2]`.
    fn pair(&self, low: &[F128], high: &[F128]) -> (F128Unreduced, F128Unreduced) {
        let (mut zero, mut infinity) = (F128Unreduced::ZERO, F128Unreduced::ZERO);
        for lane in 0..BITS / 64 {
            let (a, b, c) = (64 * lane, along(64 * lane, 1), along(64 * lane, 2));
            for z in 0..64 {
                let w = self.weights[a + z];
                let factor = w * (self.kappa + low[b + z]) + self.constant[a + z];
                zero ^= factor.mul_unreduced(low[c + z]);
                infinity ^= (w * (low[b + z] + high[b + z])).mul_unreduced(low[c + z] + high[c + z]);
            }
        }
        (zero, infinity)
    }
}

/// The sums a round accumulates, unreduced: its values at `0` and at infinity.
type RoundSums = (F128Unreduced, F128Unreduced);

fn merge(a: RoundSums, b: RoundSums) -> RoundSums {
    (a.0 ^ b.0, a.1 ^ b.1)
}

fn finish(sums: RoundSums) -> (F128, F128) {
    (sums.0.reduce(), sums.1.reduce())
}

impl Summand {
    /// Add one pair of rows to a round's sums, weighted by `eq`.
    fn add_pair(&self, sums: &mut RoundSums, low: &[F128], high: &[F128], eq: F128) {
        let (zero, infinity) = self.pair(low, high);
        sums.0 ^= zero.reduce().mul_unreduced(eq);
        sums.1 ^= infinity.reduce().mul_unreduced(eq);
    }

    /// Fold the rows of `src`, laid out as `from`, in pairs into `dst`, and sum the next round's
    /// values over the pairs of what was just written, weighted by `eq`.
    fn fold(
        &self,
        src: &[F128],
        from: Rows,
        dst: &mut [F128],
        pads: &[F128],
        challenge: F128,
        eq: &[F128],
    ) -> (F128, F128) {
        let to = from.next();
        let ptr = parallel::SendPtr(dst.as_mut_ptr());
        let fold = |out: &mut [F128], segment: usize, r: usize| {
            let (low, high) = if from.m == 1 {
                (
                    from.row(src, pads, 2 * segment, 0),
                    from.row(src, pads, 2 * segment + 1, 0),
                )
            } else {
                (
                    from.row(src, pads, segment, 2 * r),
                    from.row(src, pads, segment, 2 * r + 1),
                )
            };
            for (out, (&l, &h)) in out.iter_mut().zip(low.iter().zip(high)) {
                *out = interp(l, h, challenge);
            }
        };
        if to.m == 1 {
            // A row per segment, few enough to fold in place.
            for (segment, out) in dst[..to.len() * ROW].as_chunks_mut::<ROW>().0.iter_mut().enumerate() {
                fold(out, segment, 0);
            }
            let mut sums = (F128Unreduced::ZERO, F128Unreduced::ZERO);
            for (pair, &eq) in dst[..to.len() * ROW].as_chunks::<{ 2 * ROW }>().0.iter().zip(eq) {
                self.add_pair(&mut sums, &pair[..ROW], &pair[ROW..], eq);
            }
            return finish(sums);
        }
        // A task per pair of rows written, the second of a ragged one being the padding row.
        let (pairs, half) = (to.live.div_ceil(2), to.m / 2);
        let mut sums = parallel::map_reduce_with_state(
            to.segments * pairs,
            || vec![F128::ZERO; 2 * ROW],
            || (F128Unreduced::ZERO, F128Unreduced::ZERO),
            |rows, sums, task| {
                let (segment, t) = (task / pairs, task % pairs);
                let n = (to.live - 2 * t).min(2);
                let rows = &mut rows[..n * ROW];
                for (i, row) in rows.as_chunks_mut::<ROW>().0.iter_mut().enumerate() {
                    fold(row, segment, 2 * t + i);
                }
                let high = if n == 2 {
                    &rows[ROW..]
                } else {
                    &pads[segment * ROW..][..ROW]
                };
                self.add_pair(sums, &rows[..ROW], high, eq[half * segment + t]);
                // SAFETY: each task owns its rows of `dst`.
                let out = unsafe { ptr.slice((to.live * segment + 2 * t) * ROW, n * ROW) };
                // Built in cache for the round values, then published: the next round reads them.
                primitives::stream::Stream::new().copy(out, rows);
            },
            merge,
        );
        self.add_padding(&mut sums, to, pads, eq);
        finish(sums)
    }

    /// Add the pairs of two padding rows of a table laid out as `layout`, weighted by `eq`: each
    /// segment's padding row, once, at the sum of their weights.
    fn add_padding(&self, sums: &mut RoundSums, layout: Rows, pads: &[F128], eq: &[F128]) {
        let (first, half) = (layout.live.div_ceil(2), layout.m / 2);
        if first == half {
            return;
        }
        for (pad, eq) in pads.as_chunks::<ROW>().0.iter().zip(eq.chunks_exact(half)) {
            self.add_pair(sums, pad, pad, eq[first..].iter().sum());
        }
    }
}

/// The rows of the table the tail folds: per segment, the first `live` of `m`, then, if there are
/// fewer, the padding row every later one equals, kept apart. Once `m` is one, a row per segment.
#[derive(Clone, Copy)]
struct Rows {
    m: usize,
    live: usize,
    segments: usize,
}

impl Rows {
    fn len(&self) -> usize {
        self.segments * self.live
    }

    /// The layout once the next variable is bound: the group, the block's, then the segment's.
    fn next(&self) -> Self {
        match self.m {
            1 => Self {
                segments: self.segments / 2,
                ..*self
            },
            // The fold writes every segment's row, a padding one included.
            2 => Self { m: 1, live: 1, ..*self },
            m => Self {
                m: m / 2,
                live: self.live.div_ceil(2),
                ..*self
            },
        }
    }

    fn row<'t>(&self, table: &'t [F128], pads: &'t [F128], segment: usize, r: usize) -> &'t [F128] {
        if r < self.live {
            &table[(self.live * segment + r) * ROW..][..ROW]
        } else {
            &pads[segment * ROW..][..ROW]
        }
    }
}

/// A round of the sumcheck over bit positions, on small tables: the
/// coefficients of `sum_j w (kappa t0 + (kappa + t1) t2)` in the variable being bound.
fn local_round(w: &[F128], t: &[Vec<F128>; 3], kappa: F128) -> [F128; 4] {
    let mut h = [F128::ZERO; 4];
    for i in 0..w.len() / 2 {
        let line = |v: &[F128]| (v[2 * i], v[2 * i] + v[2 * i + 1]);
        let (w, t0, t1, t2) = (line(w), line(&t[0]), line(&t[1]), line(&t[2]));
        let u = (kappa + t1.0, t1.1);
        let a = [
            kappa * t0.0 + u.0 * t2.0,
            kappa * t0.1 + u.0 * t2.1 + u.1 * t2.0,
            u.1 * t2.1,
        ];
        h[0] += w.0 * a[0];
        h[1] += w.0 * a[1] + w.1 * a[0];
        h[2] += w.0 * a[2] + w.1 * a[1];
        h[3] += w.1 * a[2];
    }
    h
}

/// The table the rounds after the bit-level ones fold, and the half they fold it into: reused
/// from layer to layer.
pub struct Scratch {
    table: Vec<F128>,
    /// Each segment's padding row.
    pads: Vec<F128>,
}

impl Scratch {
    pub fn new(shape: Shape) -> Self {
        let rows = 1usize << (shape.y_vars() - SKIP);
        // SAFETY: every pass writes the rows it reads.
        let table = unsafe { primitives::uninit_vec(rows * ROW + rows * ROW / 2) };
        let pads = vec![F128::ZERO; ROW << shape.seg_log()];
        Self { table, pads }
    }
}

/// Prove one layer, as `crates/verifier`'s `keccak.rs` checks it: a claim on the states `step`
/// layers below the outputs becomes one on the states a layer further down.
pub fn prove_layer(
    ps: &mut ProverState,
    witness: &Witness,
    scratch: &mut Scratch,
    step: usize,
    claim: &Claim,
) -> Claim {
    let shape = witness.shape;
    let layer = Layer {
        witness,
        rounds: (0..shape.segments())
            .map(|segment| shape.round(segment, step))
            .collect(),
    };

    let product = tracing::info_span!("Product").in_scope(|| layer.product(claim));
    ps.add_scalars(&product);
    // `s`: the product polynomial has degree PROD_BITS - 1.
    ps.grind(fiat_shamir::grinding_bits(PROD_BITS as u128 - 1));
    let s = ps.sample();
    let kappa = mu_at(s).iter().sum();
    let mut value = poly_eval(&product, s);

    // The packs of a group, a pass over the witness per round.
    let mu = mu_at(s);
    let summand = Summand::new(claim, kappa);
    let tasks = layer.task_weights(&eq_table(&claim.point[SKIP + 1..]));
    let mut scale = F128::ONE;
    let mut point = Vec::with_capacity(claim.point.len());
    let skip = tracing::info_span!("Skip").entered();
    for i in 0..SKIP {
        let fold = PackFold::new(&mu, &point);
        let (zero, infinity) = layer.group_round(&summand, &fold, &eq_table(&claim.point[i + 1..=SKIP]), &tasks);
        let coeffs = round_coefficients(scale, zero, infinity, value, claim.point[i]);
        bind(ps, &coeffs, claim.point[i], &mut value, &mut scale, &mut point);
    }
    drop(skip);

    // The groups, blocks and segments, on a table. Each pass over it writes the rows of one round
    // and sums that round's values over them.
    let mut layout = Rows {
        m: 2 * shape.n_blocks(),
        live: 2 * witness.written(),
        segments: 1 << shape.seg_log(),
    };
    let (mut src, mut dst) = scratch.table.split_at_mut(layout.m * layout.segments * ROW);
    let pads = &mut scratch.pads;
    let mut values = tracing::info_span!("Tables").in_scope(|| {
        let eq = eq_table(&claim.point[SKIP + 1..]);
        layer.table(&summand, &PackFold::new(&mu, &point), &eq, layout, src, pads)
    });
    let tail = tracing::info_span!("Tail").entered();
    for i in SKIP..claim.point.len() {
        let coeffs = round_coefficients(scale, values.0, values.1, value, claim.point[i]);
        let challenge = bind(ps, &coeffs, claim.point[i], &mut value, &mut scale, &mut point);
        let later = eq_table(claim.point.get(i + 2..).unwrap_or(&[]));
        values = summand.fold(src, layout, dst, pads, challenge, &later);
        layout = layout.next();
        (src, dst) = (dst, src);
    }
    let table = &src[..ROW];
    drop(tail);

    // The bit positions.
    let cube = 1usize << LOCAL_VARS;
    let mut t0 = table.to_vec();
    t0.resize(cube, F128::ZERO);
    let shift = |k: usize| -> Vec<F128> {
        (0..cube)
            .map(|j| if j < BITS { t0[along(j, k)] } else { F128::ZERO })
            .collect()
    };
    let (t1, t2) = (shift(1), shift(2));
    let mut t = [t0, t1, t2];
    let mut w = claim.weights.clone();
    w.resize(cube, F128::ZERO);
    let mut local = Vec::with_capacity(LOCAL_VARS);
    for _ in 0..LOCAL_VARS {
        let coeffs = local_round(&w, &t, kappa).map(|c| scale * c);
        ps.add_round_poly(&coeffs, false);
        let challenge = ps.sample();
        local.push(challenge);
        w = fold(&w, 1, challenge);
        t = t.map(|v| fold(&v, 1, challenge));
    }
    let t = [t[0][0], t[1][0], t[2][0]];
    ps.add_scalars(&t);
    // `beta`: the next claim is quadratic in it.
    ps.grind(fiat_shamir::grinding_bits(2));
    let beta = ps.sample();
    Claim {
        value: t[0] + beta * (t[1] + beta * t[2]),
        mu: mu_at(s),
        point,
        weights: linear_transpose(&chi_weights(&eq_table(&local), beta)),
    }
}

/// Send a round of the sumcheck over the packs and segments and bind its variable, whose point
/// in the claim is `at`: the claim's `eq` factor on it moves into `scale`.
fn bind(
    ps: &mut ProverState,
    coeffs: &[F128; 3],
    at: F128,
    value: &mut F128,
    scale: &mut F128,
    point: &mut Vec<F128>,
) -> F128 {
    ps.add_round_poly(coeffs, true);
    let challenge = ps.sample();
    let eq = F128::ONE + at + challenge;
    *value = eq * poly_eval(coeffs, challenge);
    *scale *= eq;
    point.push(challenge);
    challenge
}

/// The coefficients of a round polynomial `h`, scaled, from its values at `0` and infinity:
/// `(1 + r) h(0) + r h(1) = value` gives the value at one.
fn round_coefficients(scale: F128, zero: F128, infinity: F128, value: F128, r: F128) -> [F128; 3] {
    let (c0, c2) = (scale * zero, scale * infinity);
    // value = c0 + r (c1 + c2).
    let c1 = (value + c0) * r.inv() + c2;
    [c0, c1, c2]
}
