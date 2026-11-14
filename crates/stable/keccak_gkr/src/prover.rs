//! The layer prover.
//!
//! One layer passes over the bits of the states it reduces to:
//!
//! 1. once for the product polynomial, before its evaluation point `s` is known;
//! 2. once per sumcheck round over the packs of half a block, folding them at the challenges so
//!    far;
//! 3. once for a table of one field element per half block and position, which the remaining
//!    rounds fold.
//!
//! At `s`, a pack's value is the sum of the instance weights of its set bits, so a folded pack is
//! a sum of byte lookups ([`PackFold`]).

use fiat_shamir::transcript::ProverState;
use primitives::field::{F128, F128Unreduced};
use primitives::multilinear::{eq_table, interp, poly_eval};

use crate::keccak::{BITS, LOCAL_VARS, along, linear_transpose, row_positions};
use crate::kernels::{GROUP, PACKS, SKIP, byte_sums, embed, products};
use crate::open::fold;
use crate::protocol::{Claim, chi_weights, mu_at};
use crate::rmfe::{PACK, PROD_BITS};
use crate::witness::{Witness, words};

/// The bytes of a product of two embeddings.
const PROD_BYTES: usize = PROD_BITS.div_ceil(8);

struct Layer<'a> {
    witness: &'a Witness,
    /// The round whose `chi` each segment's claim is on.
    rounds: Vec<usize>,
}

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

    /// The table the remaining rounds fold: row `half + 2 * (g + n_blocks * segment)` holds, per
    /// position, the value at `s` of group `half` of block `g`'s packs, folded by `fold`. Rows of
    /// segments that do not exist are zero. The padding blocks' rows are those of the padding
    /// block, folded once.
    fn table(&self, fold: &PackFold) -> Vec<F128> {
        let shape = self.witness.shape;
        let (nb, written) = (shape.n_blocks(), self.witness.written());
        let rows = |block: &[u64], out: &mut [F128]| {
            for (half, row) in out.as_chunks_mut::<BITS>().0.iter_mut().enumerate() {
                for (j, t) in row.iter_mut().enumerate() {
                    *t = fold.value(block, half, j, 0);
                }
            }
        };
        let padding: Vec<Vec<F128>> = self
            .rounds
            .iter()
            .map(|&round| {
                let mut out = vec![F128::ZERO; 2 * BITS];
                if written < nb {
                    rows(self.witness.layer(round, written), &mut out);
                }
                out
            })
            .collect();
        let mut table = parallel::filled((2 * BITS * nb) << shape.seg_log(), F128::ZERO);
        parallel::chunks_mut(&mut table, 2 * BITS, |i, out| {
            let (segment, g) = (i / nb, i % nb);
            if segment >= self.rounds.len() {
                return;
            }
            if g < written {
                rows(self.witness.layer(self.rounds[segment], g), out);
            } else {
                out.copy_from_slice(&padding[segment]);
            }
        });
        table
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

/// A round over the leading variable of a table of rows of positions: its values at `0` and at
/// infinity, the pair of rows `p` weighted by `eq[p]`.
fn table_round(summand: &Summand, table: &[F128], eq: &[F128]) -> (F128, F128) {
    let (zero, infinity) = parallel::map_reduce(
        table.len() / (2 * BITS),
        || (F128Unreduced::ZERO, F128Unreduced::ZERO),
        |p| {
            let pair = &table[2 * BITS * p..][..2 * BITS];
            let (zero, infinity) = summand.pair(&pair[..BITS], &pair[BITS..]);
            (
                zero.reduce().mul_unreduced(eq[p]),
                infinity.reduce().mul_unreduced(eq[p]),
            )
        },
        |a, b| (a.0 ^ b.0, a.1 ^ b.1),
    );
    (zero.reduce(), infinity.reduce())
}

/// Bind the leading variable of a table of rows of positions at `challenge`.
fn fold_rows(table: &[F128], challenge: F128) -> Vec<F128> {
    let mut out = parallel::filled(table.len() / 2, F128::ZERO);
    parallel::chunks_mut(&mut out, BITS, |r, row| {
        let (low, high) = table[2 * BITS * r..][..2 * BITS].split_at(BITS);
        for (out, (&l, &h)) in row.iter_mut().zip(low.iter().zip(high)) {
            *out = interp(l, h, challenge);
        }
    });
    out
}

/// A round of the sumcheck over bit positions, on small tables: the coefficients of
/// `sum_j w (kappa t0 + (kappa + t1) t2)` in the variable being bound.
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

/// Prove one layer, as `crates/verifier`'s `keccak.rs` checks it: a claim on the states `step`
/// layers below the outputs becomes one on the states a layer further down.
pub fn prove_layer(ps: &mut ProverState, witness: &Witness, step: usize, claim: &Claim) -> Claim {
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
    let mu = mu_at(s);
    let kappa = mu.iter().sum();
    let mut value = poly_eval(&product, s);

    // The packs of a group, a pass over the witness per round.
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

    // The groups, blocks and segments, on a table.
    let mut table = tracing::info_span!("Tables").in_scope(|| layer.table(&PackFold::new(&mu, &point)));
    let tail = tracing::info_span!("Tail").entered();
    for i in SKIP..claim.point.len() {
        let (zero, infinity) = table_round(&summand, &table, &eq_table(&claim.point[i + 1..]));
        let coeffs = round_coefficients(scale, zero, infinity, value, claim.point[i]);
        let challenge = bind(ps, &coeffs, claim.point[i], &mut value, &mut scale, &mut point);
        table = fold_rows(&table, challenge);
    }
    drop(tail);

    // The bit positions.
    let cube = 1usize << LOCAL_VARS;
    let mut t0 = table;
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
        mu,
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
