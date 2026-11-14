//! The layer prover.
//!
//! One layer passes over the bits of the states it reduces to:
//!
//! 1. once for the product polynomial, before its evaluation point `s` is known;
//! 2. once for the four sumcheck rounds over the packs of half a block, as the summand at every
//!    point of `{0, 1, infinity}^4` they read;
//! 3. once for a table of one field element per half block and position, which the remaining
//!    rounds fold.
//!
//! At `s`, a pack's value is the sum of the instance weights of its set bits, so a folded pack is
//! the `eq`-weighted sum of byte lookups ([`PackFold`]).

use fiat_shamir::transcript::ProverState;
use primitives::field::lanes::{ByteMap, transpose_bytes};
use primitives::field::{Acc8, F128, F128Unreduced, F128x8};
use primitives::multilinear::{eq_table, poly_eval};

use crate::keccak::{BITS, LOCAL_VARS, along, linear_transpose};
use crate::kernels::{
    COLUMNS, GROUP, MIXED, MIXED_POINTS, PROD_BYTES, ProductBlock, ProductMaps, SKIP, SkipBlock, TERNARY, element_maps,
    map_sums, ternary,
};
use crate::open::fold;
use crate::poly::AtS;
use crate::protocol::{Claim, chi_weights, mu_at};
use crate::rmfe::{PACK, PROD_BITS};
use crate::witness::{BLOCK_WORDS, Shape, Witness};

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
    /// weight bit by bit: a block's sums over positions, per pack and coefficient, are sums of
    /// weights ([`ProductBlock`]), which meet the block's weight once. The pack weights come last,
    /// so the sums per pack are returned too.
    fn product(&self, claim: &Claim) -> ([F128; PROD_BITS], Vec<[F128; PROD_BITS]>) {
        let maps = ProductMaps::new(&claim.weights);
        let tasks = self.task_weights(&eq_table(&claim.point[SKIP + 1..]));
        let sums = parallel::map_reduce_with_state(
            self.n_tasks(),
            || (ProductBlock::new(), Box::new([0u128; COLUMNS])),
            || vec![Acc8::ZERO; COLUMNS / 8],
            |(kernel, values), sums, task| {
                let (_, _, block) = self.block(task);
                kernel.run(&maps, block, values);
                let weight = F128x8::splat(tasks[task]);
                for (sum, values) in sums.iter_mut().zip(values.as_chunks::<8>().0) {
                    *sum += F128x8::from_array(&values.map(F128::from)).mul_unreduced(weight);
                }
            },
            |mut a, b| {
                for (a, b) in a.iter_mut().zip(b) {
                    *a += b;
                }
                a
            },
        );
        let sums: Vec<F128> = sums.into_iter().flat_map(|s| s.reduce().to_array()).collect();
        let per_pack: Vec<[F128; PROD_BITS]> = sums
            .as_chunks::<{ 8 * PROD_BYTES }>()
            .0
            .iter()
            .map(|s| s[..PROD_BITS].try_into().expect("a product's coefficients"))
            .collect();
        let packs = eq_table(&claim.point[..SKIP + 1]);
        let total = std::array::from_fn(|c| packs.iter().zip(&per_pack).map(|(&e, p)| e * p[c]).sum());
        (total, per_pack)
    }

    /// The layer's summand at `s` at every point `p` of `{0, 1, infinity}^SKIP`, summed over the
    /// groups: `sum over groups of eq(point[SKIP..], group) * Q(p, group)`, indexed by `p`'s
    /// ternary digits.
    ///
    /// At a mixed point, every product of a group's extended packs ([`SkipBlock`]) meets its
    /// position's weight as a polynomial in `s` ([`AtS`]), so a block's sums are carry-less products,
    /// evaluated at `s` once per slot. At a binary one, a pack's, the sum is its product polynomial's
    /// value at `s`.
    fn skip_sums(&self, claim: &Claim, at: &AtS, per_pack: &[[F128; PROD_BITS]]) -> Vec<F128> {
        let polys: Vec<[u64; 2]> = claim.weights.iter().map(|&w| at.poly(w).to_limbs()).collect();
        let weights = [0, 1].map(|k| polys.iter().map(|p| p[k]).collect::<Vec<u64>>());
        let eq = eq_table(&claim.point[SKIP..]);
        let groups: [Vec<F128>; 2] =
            [0, 1].map(|half| self.task_weights(&eq.iter().skip(half).step_by(2).copied().collect::<Vec<_>>()));
        let mixed = parallel::map_reduce_with_state(
            self.n_tasks(),
            SkipBlock::new,
            || [F128Unreduced::ZERO; TERNARY],
            |acc, sums, task| {
                let (_, _, block) = self.block(task);
                acc.run(block, &weights);
                for (half, groups) in groups.iter().enumerate() {
                    let weight = groups[task];
                    for (i, &[t, ..]) in MIXED_POINTS.iter().enumerate() {
                        sums[t] ^= at.eval(acc.get(MIXED * half + i)).mul_unreduced(weight);
                    }
                }
            },
            |mut a, b| {
                for (a, b) in a.iter_mut().zip(b) {
                    *a ^= b;
                }
                a
            },
        );
        let mut sums: Vec<F128> = mixed.iter().map(|s| s.reduce()).collect();
        // A pack's sum is its product polynomial's value, weighted by `eq` of the group's half.
        let half = claim.point[SKIP];
        for q in 0..GROUP {
            sums[ternary(q)] =
                (F128::ONE + half) * poly_eval(&per_pack[q], at.s) + half * poly_eval(&per_pack[GROUP + q], at.s);
        }
        sums
    }

    /// The table the remaining rounds fold, and the first of those rounds' values, the pair of
    /// rows `p` weighted by `eq[p]`: row `half + 2 * (g + n_blocks * segment)` holds, per
    /// position, the value at `s` of group `half` of block `g`'s packs, folded by `fold`. Rows of
    /// segments that do not exist are zero. The padding blocks' rows are those of the padding
    /// block, folded and summed once.
    fn table(&self, summand: &Summand, fold: &PackFold, eq: &[F128], table: &mut [F128]) -> (F128, F128) {
        let shape = self.witness.shape;
        let (nb, written) = (shape.n_blocks(), self.witness.written());
        let rows = |block: &[u64], out: &mut [F128]| {
            fold.rows(block, out);
            summand.pair(&out[..BITS], &out[BITS..])
        };
        let padding: Vec<(Vec<F128>, (F128, F128))> = self
            .rounds
            .iter()
            .map(|&round| {
                let mut out = vec![F128::ZERO; 2 * BITS];
                let values = if written < nb {
                    rows(self.witness.layer(round, written), &mut out)
                } else {
                    (F128::ZERO, F128::ZERO)
                };
                (out, values)
            })
            .collect();
        let values = parallel::map_reduce_chunks_mut(
            [table],
            [2 * BITS],
            || (),
            || (F128Unreduced::ZERO, F128Unreduced::ZERO),
            |_, acc, p, [out]| {
                let (segment, g) = (p / nb, p % nb);
                if segment >= self.rounds.len() {
                    out.fill(F128::ZERO);
                    return;
                }
                let (zero, infinity) = if g < written {
                    rows(self.witness.layer(self.rounds[segment], g), out)
                } else {
                    out.copy_from_slice(&padding[segment].0);
                    padding[segment].1
                };
                acc.0 ^= zero.mul_unreduced(eq[p]);
                acc.1 ^= infinity.mul_unreduced(eq[p]);
            },
            |a, b| (a.0 ^ b.0, a.1 ^ b.1),
        );
        (values.0.reduce(), values.1.reduce())
    }
}

/// The packs of a group folded at the skip's challenges: a pack's value at `s` is the sum of the
/// instance weights of its set bits, so a folded group is a linear map of its 32 bytes, a byte map
/// per byte of the input and of the value ([`map_sums`]), applied to 64 positions at a time.
struct PackFold {
    /// Per byte `t` of a position's 64, its share of its group's value: pack `t / 2`'s `eq` weight
    /// times the instance weights of its low or its high byte.
    maps: Vec<[ByteMap; 16]>,
}

impl PackFold {
    fn new(mu: &[F128; PACK], challenges: &[F128]) -> Self {
        let eq = eq_table(challenges);
        let maps = (0..8 * BLOCK_WORDS)
            .map(|t| element_maps(&std::array::from_fn(|c| eq[t / 2 % GROUP] * mu[8 * (t % 2) + c])))
            .collect();
        Self { maps }
    }

    /// Both groups of a block, folded: entry `BITS * half + j` of `out` is position `j` of group
    /// `half`.
    fn rows(&self, block: &[u64], out: &mut [F128]) {
        for j in (0..BITS).step_by(64) {
            // Byte `t` of each of the 64 positions from `j`.
            let mut bytes = [[0u64; 8]; 64];
            let positions = block[j * BLOCK_WORDS..][..64 * BLOCK_WORDS]
                .as_chunks::<BLOCK_WORDS>()
                .0;
            for (k, positions) in positions.as_chunks::<16>().0.iter().enumerate() {
                for (bytes, t) in bytes.iter_mut().zip(transpose_bytes(positions)) {
                    bytes[2 * k..][..2].copy_from_slice(&[t as u64, (t >> 64) as u64]);
                }
            }
            for (half, maps) in self.maps.chunks(32).enumerate() {
                let values = map_sums(maps, |t| bytes[32 * half + t]);
                for (out, v) in out[BITS * half + j..][..64].iter_mut().zip(values) {
                    *out = F128::from(v);
                }
            }
        }
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
    /// `sum over positions of B[j] * T[j + 2]` at `0` and at infinity, where
    /// `B[j] = weights[j] * (kappa + T[j + 1]) + kappa * weights[j + 2]`.
    fn pair(&self, low: &[F128], high: &[F128]) -> (F128, F128) {
        let kappa = F128x8::splat(self.kappa);
        let (mut zero, mut infinity) = (Acc8::ZERO, Acc8::ZERO);
        for lane in 0..BITS / 64 {
            let (a, b, c) = (64 * lane, along(64 * lane, 1), along(64 * lane, 2));
            for z in (0..64).step_by(8) {
                let at = |v: &[F128], j: usize| F128x8::load(&v[j + z..][..8]);
                let (w, lb, lc) = (at(&self.weights, a), at(low, b), at(low, c));
                zero += (w * (kappa + lb) + at(&self.constant, a)).mul_unreduced(lc);
                infinity += (w * (lb + at(high, b))).mul_unreduced(lc + at(high, c));
            }
        }
        (zero.sum(), infinity.sum())
    }
}

/// Bind the leading variable of a table of rows of positions at `challenge`, into `out`, half its
/// length, and sum the next round's values over the rows written while they are at hand, the pair
/// of rows `p` weighted by `eq[p]`: zero once a single row is left.
fn fold_rows(summand: &Summand, table: &[F128], out: &mut [F128], challenge: F128, eq: &[F128]) -> (F128, F128) {
    let challenge = F128x8::splat(challenge);
    // Pair `p` of the rows written, from four rows of `table`.
    let pair = |acc: &mut (F128Unreduced, F128Unreduced), p: usize, rows: &mut [F128]| {
        let src = &table[4 * BITS * p..][..2 * rows.len()];
        for (row, src) in rows
            .as_chunks_mut::<BITS>()
            .0
            .iter_mut()
            .zip(src.as_chunks::<{ 2 * BITS }>().0)
        {
            let (low, high) = src.split_at(BITS);
            for (i, out) in row.as_chunks_mut::<8>().0.iter_mut().enumerate() {
                let (l, h) = (F128x8::load(&low[8 * i..][..8]), F128x8::load(&high[8 * i..][..8]));
                (l + challenge * (l + h)).store(out);
            }
        }
        if rows.len() == 2 * BITS {
            let (zero, infinity) = summand.pair(&rows[..BITS], &rows[BITS..]);
            acc.0 ^= zero.mul_unreduced(eq[p]);
            acc.1 ^= infinity.mul_unreduced(eq[p]);
        }
    };
    let zero = (F128Unreduced::ZERO, F128Unreduced::ZERO);
    let values = if table.len() <= SERIAL_ROWS * BITS {
        // Waking the pool would cost more than the work.
        let mut values = zero;
        for (p, rows) in out.chunks_mut(2 * BITS).enumerate() {
            pair(&mut values, p, rows);
        }
        values
    } else {
        parallel::map_reduce_chunks_mut(
            [out],
            [2 * BITS],
            || (),
            || zero,
            |_, acc, p, [rows]| pair(acc, p, rows),
            |a, b| (a.0 ^ b.0, a.1 ^ b.1),
        )
    };
    (values.0.reduce(), values.1.reduce())
}

/// The tables a tail round folds on the calling thread, in rows.
const SERIAL_ROWS: usize = 64;

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

/// The two tables the rounds over packs and segments fold between, allocated once for every layer:
/// a row per group of each block and segment, and half as many.
pub(crate) struct Tables([Vec<F128>; 2]);

impl Tables {
    pub fn new(shape: Shape) -> Self {
        let len = (2 * BITS * shape.n_blocks()) << shape.seg_log();
        Self([len, len / 2].map(|len| parallel::filled(len, F128::ZERO)))
    }
}

/// Prove one layer, as `crates/verifier`'s `keccak.rs` checks it: a claim on the states `step`
/// layers below the outputs becomes one on the states a layer further down.
pub fn prove_layer(ps: &mut ProverState, witness: &Witness, step: usize, claim: &Claim, tables: &mut Tables) -> Claim {
    let shape = witness.shape;
    let layer = Layer {
        witness,
        rounds: (0..shape.segments())
            .map(|segment| shape.round(segment, step))
            .collect(),
    };

    let (product, per_pack) = tracing::info_span!("Product").in_scope(|| layer.product(claim));
    ps.add_scalars(&product);
    // `s`: the product polynomial has degree PROD_BITS - 1.
    ps.grind(fiat_shamir::grinding_bits(PROD_BITS as u128 - 1));
    let s = ps.sample();
    let mu = mu_at(s);
    let kappa = mu.iter().sum();
    let mut value = poly_eval(&product, s);

    // The packs of a group, from one pass over the witness: the summand at every point the four
    // rounds read, folded at each challenge.
    let mut sums = tracing::info_span!("Skip").in_scope(|| layer.skip_sums(claim, &AtS::new(s), &per_pack));
    let mut scale = F128::ONE;
    let mut point = Vec::with_capacity(claim.point.len());
    for i in 0..SKIP {
        let later = eq_table(&claim.point[i + 1..SKIP]);
        let mut h = [F128::ZERO; 3];
        for (b, &eq) in later.iter().enumerate() {
            for (d, h) in h.iter_mut().enumerate() {
                *h += eq * sums[d + 3 * ternary(b)];
            }
        }
        let coeffs = [scale * h[0], scale * (h[0] + h[1] + h[2]), scale * h[2]];
        let challenge = bind(ps, &coeffs, claim.point[i], &mut value, &mut scale, &mut point);
        sums = sums
            .as_chunks::<3>()
            .0
            .iter()
            .map(|v| v[0] + challenge * (v[0] + v[1]) + (challenge.square() + challenge) * v[2])
            .collect();
    }
    let summand = Summand::new(claim, kappa);

    // The groups, blocks and segments, on a table. Each pass over it writes the rows of one round
    // and sums that round's values over them.
    let [table, half] = &mut tables.0;
    let mut values = tracing::info_span!("Tables").in_scope(|| {
        let eq = eq_table(&claim.point[SKIP + 1..]);
        layer.table(&summand, &PackFold::new(&mu, &point), &eq, table)
    });
    let tail = tracing::info_span!("Tail").entered();
    // Each round folds one table into the other.
    let (mut src, mut dst) = (&mut table[..], &mut half[..]);
    for i in SKIP..claim.point.len() {
        let coeffs = round_coefficients(scale, values.0, values.1, value, claim.point[i]);
        let challenge = bind(ps, &coeffs, claim.point[i], &mut value, &mut scale, &mut point);
        let eq = eq_table(claim.point.get(i + 2..).unwrap_or(&[]));
        let len = src.len() / 2;
        values = fold_rows(&summand, src, &mut dst[..len], challenge, &eq);
        (src, dst) = (&mut dst[..len], src);
    }
    let mut t0 = src.to_vec();
    drop(tail);

    // The bit positions.
    let cube = 1usize << LOCAL_VARS;
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
