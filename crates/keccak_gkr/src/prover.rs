//! The layer prover.
//!
//! One layer makes three passes over the bits of the states it reduces to:
//!
//! 1. the product polynomial, before its evaluation point `s` is known;
//! 2. the first sumcheck rounds, over the packs of half a block, as sums of bit-level products;
//! 3. one field element per half block and position, for the rounds that remain.
//!
//! From `s` on, everything stays in the power basis of `s` ([`crate::power`]) until the tables
//! are down to one row.

use fiat_shamir::transcript::ProverState;
use primitives::field::gf2_64::mul_wide;
use primitives::field::{F192, F192Unreduced};
use primitives::multilinear::{eq_table, poly_eval};

use crate::basis::{PolyEval, carry};
use crate::keccak::{BITS, LOCAL_VARS, along, linear_transpose};
use crate::kernels::{
    GROUP, MIXED, PACKS, SKIP, SLOTS, SkipAcc, TERNARY, embed, embed_extend, fold_group, mixed_points, products,
    skip_row, slot,
};
use crate::power::{Element, PowerField, get, set};
use crate::protocol::{Claim, chi_weights, mu_at, sum};
use crate::rmfe::PROD_BITS;
use crate::witness::{BLOCK_WORDS, Shape, Witness, transpose64};

/// The pattern index of a binary assignment.
fn ternary(b: usize) -> usize {
    (0..SKIP).fold(0, |acc, k| acc + (b >> k & 1) * 3usize.pow(k as u32))
}

/// The five positions of a row and slice, which `chi` mixes.
#[inline(always)]
fn row_positions(row: usize, z: usize) -> [usize; 5] {
    std::array::from_fn(|x| 64 * (x + 5 * row) + z)
}

#[inline(always)]
fn words(block: &[u64], j: usize) -> &[u64; BLOCK_WORDS] {
    block[j * BLOCK_WORDS..][..BLOCK_WORDS].try_into().expect("eight words")
}

/// Digits a weight splits into, and the values of one.
const DIGIT_BITS: usize = 8;
const DIGITS: usize = 192 / DIGIT_BITS;
/// The bits of a block position's products, 48 to each pack.
const PAYLOAD_BITS: usize = 48 * PACKS;
/// The packs of a quarter of a block position, and the words of their products.
const QUARTER: usize = 8;
const QUARTER_WORDS: usize = 48 * QUARTER / 64;

/// The products of a quarter of a block position's packs, 48 bits each: a block's worth stays in
/// cache while every digit of the weights groups it.
#[derive(Clone, Copy)]
#[repr(C, align(16))]
struct Quarter([u64; QUARTER_WORDS]);

impl Quarter {
    const ZERO: Self = Self([0; QUARTER_WORDS]);

    /// Product `q` at bits `48 * q ..`: four products to three words.
    #[inline(always)]
    fn pack(products: &[u64; QUARTER]) -> Self {
        let mut out = [0u64; QUARTER_WORDS];
        for (out, p) in out.as_chunks_mut::<3>().0.iter_mut().zip(products.as_chunks::<4>().0) {
            *out = [p[0] | p[1] << 48, p[1] >> 16 | p[2] << 32, p[2] >> 32 | p[3] << 16];
        }
        Self(out)
    }

    #[inline(always)]
    fn add(&mut self, other: &Self) {
        #[cfg(all(target_arch = "x86_64", target_feature = "avx2"))]
        // SAFETY: both quarters are six words, and AVX2 is enabled at compile time.
        unsafe {
            use core::arch::x86_64::*;
            let (dst, src) = (self.0.as_mut_ptr(), other.0.as_ptr());
            let (d, s) = (dst.cast::<__m256i>(), src.cast::<__m256i>());
            _mm256_storeu_si256(d, _mm256_xor_si256(_mm256_loadu_si256(d), _mm256_loadu_si256(s)));
            let (d, s) = (dst.add(4).cast::<__m128i>(), src.add(4).cast::<__m128i>());
            _mm_storeu_si128(d, _mm_xor_si128(_mm_loadu_si128(d), _mm_loadu_si128(s)));
        }
        // Left to itself, the compiler XORs the words in general registers.
        #[cfg(target_arch = "aarch64")]
        // SAFETY: both quarters are six words, and aarch64 always has NEON.
        unsafe {
            use core::arch::aarch64::*;
            let (dst, src) = (self.0.as_mut_ptr(), other.0.as_ptr());
            for i in (0..QUARTER_WORDS).step_by(2) {
                vst1q_u64(dst.add(i), veorq_u64(vld1q_u64(dst.add(i)), vld1q_u64(src.add(i))));
            }
        }
        #[cfg(not(any(all(target_arch = "x86_64", target_feature = "avx2"), target_arch = "aarch64")))]
        for (x, y) in self.0.iter_mut().zip(&other.0) {
            *x ^= y;
        }
    }
}

/// Digit `d` of a weight.
#[inline(always)]
fn digit(weight: F192, d: usize) -> usize {
    let w = [weight.c0, weight.c1, weight.c2];
    (w[d / 8] >> (DIGIT_BITS * (d % 8))) as usize & ((1 << DIGIT_BITS) - 1)
}

/// The positions grouped by each digit of their weight: those whose digit `d` is `v` are
/// `order[d][starts[d][v]..starts[d][v + 1]]`.
struct Groups {
    order: Vec<[u16; BITS]>,
    starts: Vec<[u16; (1 << DIGIT_BITS) + 1]>,
}

impl Groups {
    fn new(weights: &[F192]) -> Self {
        let mut order = vec![[0u16; BITS]; DIGITS];
        let mut starts = vec![[0u16; (1 << DIGIT_BITS) + 1]; DIGITS];
        for (d, (order, starts)) in order.iter_mut().zip(&mut starts).enumerate() {
            let digits: Vec<usize> = weights[..BITS].iter().map(|&w| digit(w, d)).collect();
            for &v in &digits {
                starts[v + 1] += 1;
            }
            for v in 0..1 << DIGIT_BITS {
                starts[v + 1] += starts[v];
            }
            let mut next = *starts;
            for (p, &v) in digits.iter().enumerate() {
                order[next[v] as usize] = p as u16;
                next[v] += 1;
            }
        }
        Self { order, starts }
    }

    /// `sum over positions of weight[j] (x) payloads[j]` into `rows`: row `DIGIT_BITS * d + i`
    /// sums the payloads whose weight has that bit set. Each group is summed in registers, so
    /// the payloads are only read.
    fn add_rows(&self, payloads: &[Quarter; BITS], rows: &mut [Quarter; 192], sums: &mut [Quarter; 1 << DIGIT_BITS]) {
        for (rows, (order, starts)) in rows
            .as_chunks_mut::<DIGIT_BITS>()
            .0
            .iter_mut()
            .zip(self.order.iter().zip(&self.starts))
        {
            for (v, sum) in sums.iter_mut().enumerate() {
                let mut acc = Quarter::ZERO;
                for &p in &order[starts[v] as usize..starts[v + 1] as usize] {
                    // SAFETY: `order` holds positions.
                    acc.add(unsafe { payloads.get_unchecked(p as usize) });
                }
                *sum = acc;
            }
            // Bit `i` of the digit: the sums whose value has it, then fold it away.
            for (i, row) in rows.iter_mut().enumerate().rev() {
                let (low, high) = sums[..2 << i].split_at_mut(1 << i);
                let mut acc = Quarter::ZERO;
                for (low, high) in low.iter_mut().zip(&*high) {
                    acc.add(high);
                    low.add(high);
                }
                *row = acc;
            }
        }
    }
}

struct Layer<'a> {
    witness: &'a Witness,
    /// The round whose `chi` each segment's claim is on.
    rounds: Vec<usize>,
}

/// A row of a table in the power basis: three words per position, laid out by word.
const ROW: usize = 3 * BITS;

impl Layer<'_> {
    /// The blocks that hold data, as `(index among all blocks, block)`.
    fn block(&self, task: usize) -> (usize, &[u64]) {
        let nb = self.witness.shape.n_blocks();
        let (segment, g) = (task / nb, task % nb);
        (g + nb * segment, self.witness.layer(self.rounds[segment], g))
    }

    fn n_tasks(&self) -> usize {
        self.rounds.len() * self.witness.shape.n_blocks()
    }

    /// Per pack `q` of a block, the coefficients of
    /// `sum over blocks and positions of eq(point[5..], block) * weights[j] * product(q, j)`,
    /// where the product is `ones * u[j] + (ones + u[j + 1]) * u[j + 2]` on embeddings, the
    /// unprojected `chi`.
    ///
    /// Nothing here knows where the polynomials will be evaluated, so each product meets its
    /// weight bit by bit. The position weights are the same in every block, so a block's sum
    /// over positions is grouped by their digits ([`Groups`]), a quarter of the packs at a time;
    /// only that sum meets the block's weight, as field elements.
    fn pack_products(&self, claim: &Claim) -> Vec<[F192; PROD_BITS]> {
        let blocks = eq_table(&claim.point[SKIP + 1..]);
        let groups = Groups::new(&claim.weights);
        let sums = parallel::map_reduce_with_state(
            self.n_tasks(),
            || {
                (
                    vec![[Quarter::ZERO; BITS]; PACKS / QUARTER],
                    vec![[Quarter::ZERO; 192]; PACKS / QUARTER],
                    Box::new([Quarter::ZERO; 1 << DIGIT_BITS]),
                )
            },
            || vec![F192Unreduced::ZERO; PAYLOAD_BITS],
            |(payloads, rows, digit_sums), sums, task| {
                let (row, block) = self.block(task);
                for r in 0..5 {
                    for z in 0..64 {
                        let js = row_positions(r, z);
                        let e: [[u32; PACKS]; 5] = std::array::from_fn(|x| embed(words(block, js[x])));
                        for x in 0..5 {
                            let p = products(&e[x], &e[(x + 1) % 5], &e[(x + 2) % 5]);
                            for (q, quarter) in payloads.iter_mut().enumerate() {
                                quarter[js[x]] = Quarter::pack(p[QUARTER * q..][..QUARTER].try_into().unwrap());
                            }
                        }
                    }
                }
                for (payloads, rows) in payloads.iter().zip(rows.iter_mut()) {
                    groups.add_rows(payloads, rows, digit_sums);
                }
                // Row `r` holds bit `r` of each payload bit's weighted sum: transposed, they are
                // field elements, which the block's weight multiplies.
                let mut columns = [[0u64; 64]; 3];
                for m in 0..PAYLOAD_BITS / 64 {
                    let (q, w) = (m / QUARTER_WORDS, m % QUARTER_WORDS);
                    for (k, column) in columns.iter_mut().enumerate() {
                        for (b, word) in column.iter_mut().enumerate() {
                            *word = rows[q][64 * k + b].0[w];
                        }
                        transpose64(column);
                    }
                    for (t, sum) in sums[64 * m..][..64].iter_mut().enumerate() {
                        *sum ^= blocks[row].mul_unreduced(F192::new(columns[0][t], columns[1][t], columns[2][t]));
                    }
                }
            },
            |mut a, b| {
                for (x, y) in a.iter_mut().zip(b) {
                    *x ^= y;
                }
                a
            },
        );
        (0..PACKS)
            .map(|q| std::array::from_fn(|c| sums[48 * q + c].reduce()))
            .collect()
    }

    /// The layer's summand at `s`, extended over the packs of a group and summed over the groups:
    /// for every point `p` of `{0, 1, infinity}^SKIP`,
    /// `sum over groups of eq(point[SKIP..], group) * Q(p, group)`.
    ///
    /// A point at infinity in some variable keeps only the product `u[j + 1] * u[j + 2]`, summed
    /// here. A binary one is a pack, whose sum `binary` already holds.
    fn skip_sums(&self, claim: &Claim, field: &PowerField, s: F192, binary: &[F192; GROUP]) -> Vec<F192> {
        let weights: Vec<Element> = claim.weights.iter().map(|&w| field.from_field(w)).collect();
        let groups: Vec<Element> = eq_table(&claim.point[SKIP..])
            .iter()
            .map(|&e| field.from_field(e))
            .collect();
        let mixed = parallel::map_reduce_with_state(
            self.n_tasks(),
            SkipAcc::new,
            || vec![[0u64; 7]; MIXED],
            |acc, total, task| {
                let (row, block) = self.block(task);
                acc.clear();
                let mut extended = [[0u32; SLOTS]; 5];
                for r in 0..5 {
                    for z in 0..64 {
                        let js = row_positions(r, z);
                        for x in 0..5 {
                            embed_extend(words(block, js[x]), &mut extended[x]);
                        }
                        skip_row(acc, &extended, std::array::from_fn(|x| &weights[js[x]]));
                    }
                }
                for half in 0..2 {
                    for (i, total) in total.iter_mut().enumerate() {
                        add_mul(total, &carry(&acc.get(slot(half, i))), &groups[2 * row + half]);
                    }
                }
            },
            |mut a, b| {
                for (x, y) in a.iter_mut().zip(b) {
                    for (x, y) in x.iter_mut().zip(y) {
                        *x ^= y;
                    }
                }
                a
            },
        );
        let eval = PolyEval::new(s, 56);
        let mut sums = vec![F192::ZERO; TERNARY];
        for (slot, p) in mixed_points().into_iter().enumerate() {
            sums[p] = eval.eval(&mixed[slot]);
        }
        for (q, &value) in binary.iter().enumerate() {
            sums[ternary(q)] = value;
        }
        sums
    }

    /// The table the remaining rounds fold, a row per group: `T[j]`, the value at `s` of position
    /// `j`'s embeddings, folded over the group's packs at `challenges`. A block's two groups are
    /// the first of those rounds' pairs, so its round values are summed while the rows are at hand.
    fn table(&self, round: &Round, challenges: &[F192], eq: &[F192], table: &mut [u64]) -> (F192, F192) {
        let field = round.field;
        let fold: Vec<Element> = eq_table(challenges).iter().map(|&e| field.from_field(e)).collect();
        let fold: [[u64; GROUP]; 3] = std::array::from_fn(|k| std::array::from_fn(|q| fold[q][k]));
        // Rows of segments that do not exist are zero, and so is their product.
        table[2 * self.n_tasks() * ROW..].fill(0);
        let ptr = parallel::SendPtr(table.as_mut_ptr());
        let sums = parallel::map_reduce_with_state(
            self.n_tasks(),
            || (vec![0u64; 4 * ROW], vec![0u64; 8 * BITS]),
            RoundSums::default,
            |(scratch, wide), sums, task| {
                let (row, block) = self.block(task);
                // SAFETY: each task owns its two rows.
                let rows = unsafe { ptr.slice(2 * row * ROW, 2 * ROW) };
                // Both groups' unreduced sums, four words each and laid out by word.
                for j in 0..BITS {
                    let e = embed(words(block, j));
                    for (half, wide) in wide.as_chunks_mut::<{ 4 * BITS }>().0.iter_mut().enumerate() {
                        let group: &[u32; GROUP] = e[GROUP * half..][..GROUP].try_into().expect("half a block");
                        let sum: [u64; 4] = carry(&fold_group(group, &fold));
                        for (k, &word) in sum.iter().enumerate() {
                            wide[k * BITS + j] = word;
                        }
                    }
                }
                for (t, wide) in rows
                    .as_chunks_mut::<ROW>()
                    .0
                    .iter_mut()
                    .zip(wide.as_chunks::<{ 4 * BITS }>().0)
                {
                    field.reduce_row(t, wide, BITS);
                }
                round.add_pair(sums, scratch, rows, eq[row]);
            },
            RoundSums::merge,
        );
        round.finish(&sums)
    }
}

/// The sums a round accumulates, unreduced: its values at `0` and at infinity.
#[derive(Clone, Copy, Default)]
struct RoundSums([u64; 9], [u64; 9]);

impl RoundSums {
    fn merge(mut self, other: Self) -> Self {
        for i in 0..9 {
            self.0[i] ^= other.0[i];
            self.1[i] ^= other.1[i];
        }
        self
    }
}

/// What a round needs of the claim, by word as a table row is: the position weights, and each
/// position's constant `kappa * weights[j + 2]`.
struct Round<'a> {
    field: &'a PowerField,
    eval: PolyEval,
    kappa: Element,
    weights: Vec<u64>,
    constant: Vec<u64>,
}

impl<'a> Round<'a> {
    fn new(field: &'a PowerField, claim: &Claim, s: F192, kappa: F192) -> Self {
        let (mut weights, mut constant) = (vec![0u64; ROW], vec![0u64; ROW]);
        for j in 0..BITS {
            set(&mut weights, BITS, j, &field.from_field(claim.weights[j]));
            set(
                &mut constant,
                BITS,
                j,
                &field.from_field(kappa * claim.weights[along(j, 2)]),
            );
        }
        Self {
            field,
            eval: PolyEval::new(s, 72),
            kappa: field.from_field(kappa),
            weights,
            constant,
        }
    }

    /// `B[j] = weights[j] * (kappa + T[j + 1]) + kappa * weights[j + 2]` and `T[j + 2]`, for a
    /// row `T`.
    fn factors(&self, t: &[u64], b: &mut [u64], shifted: &mut [u64]) {
        // `T[j + 1] + kappa`, then `T[j + 2]`: a lane is 64 positions, five lanes to a row.
        for k in 0..3 {
            let (src, next) = (&t[k * BITS..][..BITS], &mut shifted[k * BITS..][..BITS]);
            for lane in 0..BITS / 64 {
                let at = |shift: usize| 64 * ((lane % 5 + shift) % 5 + 5 * (lane / 5));
                for z in 0..64 {
                    next[64 * lane + z] = src[at(1) + z] ^ self.kappa[k];
                }
            }
        }
        self.field.mul_row(b, &self.weights, shifted, &self.constant, BITS);
        for k in 0..3 {
            let (src, dst) = (&t[k * BITS..][..BITS], &mut shifted[k * BITS..][..BITS]);
            for lane in 0..BITS / 64 {
                let at = 64 * ((lane % 5 + 2) % 5 + 5 * (lane / 5));
                dst[64 * lane..][..64].copy_from_slice(&src[at..][..64]);
            }
        }
    }

    /// Add one pair of rows to a round's sums: the values at `0` and at infinity of
    /// `sum over positions of B[j] * T[j + 2]`, weighted by `eq`.
    fn add_pair(&self, sums: &mut RoundSums, scratch: &mut [u64], pair: &[u64], eq: F192) {
        let (b, shifted) = scratch.split_at_mut(2 * ROW);
        for half in 0..2 {
            self.factors(
                &pair[half * ROW..][..ROW],
                &mut b[half * ROW..][..ROW],
                &mut shifted[half * ROW..][..ROW],
            );
        }
        let (zero, infinity) = self
            .field
            .dot_pair([&b[..ROW], &b[ROW..]], [&shifted[..ROW], &shifted[ROW..]], BITS);
        let weight = self.field.from_field(eq);
        for (acc, dot) in [(&mut sums.0, zero), (&mut sums.1, infinity)] {
            for (i, &x) in dot.iter().enumerate() {
                for (k, &y) in weight.iter().enumerate() {
                    let p = mul_wide(x, y);
                    acc[i + k] ^= p as u64;
                    acc[i + k + 1] ^= (p >> 64) as u64;
                }
            }
        }
    }

    fn finish(&self, sums: &RoundSums) -> (F192, F192) {
        (self.eval.eval(&sums.0), self.eval.eval(&sums.1))
    }

    /// Fold the rows of `src` in pairs into `dst`, and sum the next round's values over the
    /// pairs of what was just written.
    fn fold(&self, src: &[u64], dst: &mut [u64], challenge: &Element, eq: &[F192]) -> (F192, F192) {
        let rows = src.len() / (2 * ROW);
        if rows == 1 {
            self.field
                .fold_row(&mut dst[..ROW], &src[..ROW], &src[ROW..], challenge, BITS);
            return (F192::ZERO, F192::ZERO);
        }
        let ptr = parallel::SendPtr(dst.as_mut_ptr());
        let sums = parallel::map_reduce_with_state(
            rows / 2,
            || vec![0u64; 4 * ROW],
            RoundSums::default,
            |scratch, sums, t| {
                // SAFETY: each task owns its two rows of `dst`.
                let pair = unsafe { ptr.slice(2 * t * ROW, 2 * ROW) };
                for (half, out) in pair.as_chunks_mut::<ROW>().0.iter_mut().enumerate() {
                    let quad = &src[(4 * t + 2 * half) * ROW..][..2 * ROW];
                    self.field.fold_row(out, &quad[..ROW], &quad[ROW..], challenge, BITS);
                }
                self.add_pair(sums, scratch, pair, eq[t]);
            },
            RoundSums::merge,
        );
        self.finish(&sums)
    }
}

/// A round of the sumcheck over bit positions, on small tables in the standard basis: the
/// coefficients of `sum_j w (kappa t0 + (kappa + t1) t2)` in the variable being bound.
fn local_round(w: &[F192], t: &[Vec<F192>; 3], kappa: F192) -> [F192; 4] {
    let mut h = [F192::ZERO; 4];
    for i in 0..w.len() / 2 {
        let line = |v: &[F192]| (v[2 * i], v[2 * i] + v[2 * i + 1]);
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

fn local_fold(table: &[F192], challenge: F192) -> Vec<F192> {
    table
        .as_chunks::<2>()
        .0
        .iter()
        .map(|p| p[0] + challenge * (p[0] + p[1]))
        .collect()
}

/// The table the rounds after the bit-level ones fold, and the half they fold it into: reused
/// from layer to layer.
pub struct Scratch(Vec<u64>);

impl Scratch {
    pub fn new(shape: Shape) -> Self {
        let rows = 1usize << (shape.y_vars() - SKIP);
        // SAFETY: every pass writes the rows it reads.
        Self(unsafe { primitives::uninit_vec(rows * ROW + rows * ROW / 2) })
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

    let per_pack = tracing::info_span!("Product").in_scope(|| layer.pack_products(claim));
    let pack_weights = eq_table(&claim.point[..SKIP + 1]);
    let product: [F192; PROD_BITS] =
        std::array::from_fn(|c| (0..PACKS).fold(F192::ZERO, |acc, q| acc + pack_weights[q] * per_pack[q][c]));
    ps.add_scalars(&product);
    let s = ps.sample();
    let kappa = sum(&mu_at(s));
    let mut value = poly_eval(&product, s);
    let field = PowerField::new(s).expect("the challenge lies in no proper subfield");

    // The packs of a group, from sums of bit-level products. A pack's own sum is its product
    // polynomial at `s`, over both groups of the block.
    let binary: [F192; GROUP] = std::array::from_fn(|q| {
        let half = claim.point[SKIP];
        (F192::ONE + half) * poly_eval(&per_pack[q], s) + half * poly_eval(&per_pack[GROUP + q], s)
    });
    let mut sums = tracing::info_span!("Skip").in_scope(|| layer.skip_sums(claim, &field, s, &binary));
    let mut scale = F192::ONE;
    let mut point = Vec::with_capacity(claim.point.len());
    for i in 0..SKIP {
        let later = eq_table(&claim.point[i + 1..SKIP]);
        let mut h = [F192::ZERO; 3];
        for (b, &eq) in later.iter().enumerate() {
            for (d, h) in h.iter_mut().enumerate() {
                *h += eq * sums[d + 3 * ternary(b)];
            }
        }
        let coeffs = [scale * h[0], scale * (h[0] + h[1] + h[2]), scale * h[2]];
        ps.add_round_poly(&coeffs, true);
        let challenge = ps.sample();
        let eq = F192::ONE + claim.point[i] + challenge;
        value = eq * poly_eval(&coeffs, challenge);
        scale *= eq;
        point.push(challenge);
        sums = sums
            .as_chunks::<3>()
            .0
            .iter()
            .map(|v| v[0] + challenge * (v[0] + v[1]) + (challenge.square() + challenge) * v[2])
            .collect();
    }

    // The groups, blocks and segments, on a table in the power basis. Each pass over it writes
    // the rows of one round and sums that round's values over them.
    let round = Round::new(&field, claim, s, kappa);
    let rows = 1usize << (shape.y_vars() - SKIP);
    let (mut src, mut dst) = scratch.0.split_at_mut(rows * ROW);
    let mut values = tracing::info_span!("Tables")
        .in_scope(|| layer.table(&round, &point, &eq_table(&claim.point[SKIP + 1..]), src));
    let tail = tracing::info_span!("Tail").entered();
    for i in SKIP..claim.point.len() {
        let coeffs = round_coefficients(scale, values.0, values.1, value, claim.point[i]);
        ps.add_round_poly(&coeffs, true);
        let challenge = ps.sample();
        let eq = F192::ONE + claim.point[i] + challenge;
        value = eq * poly_eval(&coeffs, challenge);
        scale *= eq;
        point.push(challenge);
        let live = ROW << (claim.point.len() - i);
        let later = eq_table(claim.point.get(i + 2..).unwrap_or(&[]));
        values = round.fold(&src[..live], &mut dst[..live / 2], &field.from_field(challenge), &later);
        (src, dst) = (dst, src);
    }
    let table = &src[..ROW];
    drop(tail);

    // The bit positions, in the standard basis.
    let cube = 1usize << LOCAL_VARS;
    let standard = |row: &[u64]| -> Vec<F192> {
        let mut out: Vec<F192> = (0..BITS).map(|j| field.to_field(&get(row, BITS, j))).collect();
        out.resize(cube, F192::ZERO);
        out
    };
    let t0 = standard(table);
    let shift = |k: usize| -> Vec<F192> {
        (0..cube)
            .map(|j| if j < BITS { t0[along(j, k)] } else { F192::ZERO })
            .collect()
    };
    let (t1, t2) = (shift(1), shift(2));
    let mut t = [t0, t1, t2];
    let mut w = claim.weights.clone();
    w.resize(cube, F192::ZERO);
    let mut local = Vec::with_capacity(LOCAL_VARS);
    for _ in 0..LOCAL_VARS {
        let coeffs = local_round(&w, &t, kappa).map(|c| scale * c);
        ps.add_round_poly(&coeffs, false);
        let challenge = ps.sample();
        local.push(challenge);
        w = local_fold(&w, challenge);
        t = t.map(|v| local_fold(&v, challenge));
    }
    let t = [t[0][0], t[1][0], t[2][0]];
    ps.add_scalars(&t);
    let beta = ps.sample();
    Claim {
        value: t[0] + beta * (t[1] + beta * t[2]),
        mu: mu_at(s),
        point,
        weights: linear_transpose(&chi_weights(&eq_table(&local), beta)),
    }
}

/// The coefficients of a round polynomial `h`, scaled, from its values at `0` and infinity:
/// `(1 + r) h(0) + r h(1) = value` gives the value at one.
fn round_coefficients(scale: F192, zero: F192, infinity: F192, value: F192, r: F192) -> [F192; 3] {
    let (c0, c2) = (scale * zero, scale * infinity);
    // value = c0 + r (c1 + c2).
    let c1 = (value + c0) * r.inv() + c2;
    [c0, c1, c2]
}

/// `total += a * b`, on binary polynomials.
#[inline(always)]
fn add_mul(total: &mut [u64; 7], a: &[u64; 4], b: &[u64; 3]) {
    for (i, &a) in a.iter().enumerate() {
        for (k, &b) in b.iter().enumerate() {
            let p = mul_wide(a, b);
            total[i + k] ^= p as u64;
            total[i + k + 1] ^= (p >> 64) as u64;
        }
    }
}
