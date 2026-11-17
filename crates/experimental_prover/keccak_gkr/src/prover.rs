//! The layer prover.
//!
//! One layer makes three passes over the bits of the states it reduces to:
//!
//! 1. the product polynomial, before its evaluation point `s` is known;
//! 2. the first sumcheck rounds, over the packs of half a block, as sums of bit-level products;
//! 3. one field element per half block and position, for the rounds that remain.
//!
//! From `s` on, everything stays in the power basis of `s` ([`crate::power`]) until the tables
//! are down to one row, which takes a pass over them per two rounds ([`Round::pass`]).

use primitives::field::{F128, F128Unreduced};
use primitives::hash::positions::row_positions;
use primitives::multilinear::{eq_table, interp, poly_eval};
use primitives::transcript::ProverState;
use verifier::keccak::{BITS, LOCAL_BITS, along, linear_transpose};

use crate::basis::{PolyEval, add_mul};
use crate::kernels::{GROUP, MIXED, PACKS, SKIP, SkipBlock, TERNARY, embed, mixed_points, products, slot};
use crate::power::{Element, PowerField, get, set};
use crate::protocol::{Claim, chi_weights, mu_at};
use crate::witness::{Shape, Witness, transpose64, words};
use verifier::keccak::PRODUCT_BITS;

/// The pattern index of a binary assignment.
fn ternary(b: usize) -> usize {
    (0..SKIP).fold(0, |acc, k| acc + (b >> k & 1) * 3usize.pow(k as u32))
}

/// Digits a weight splits into, and the values of one.
const DIGIT_BITS: usize = 8;
const DIGITS: usize = 128 / DIGIT_BITS;
/// The bits of a block position's products, 48 to each pack.
pub(crate) const PAYLOAD_BITS: usize = 48 * PACKS;
/// The packs of a part of a block position, and the words of their products: with AVX-512 the
/// whole position, three registers; with AVX2 half, three registers; elsewhere a quarter, a
/// block's worth of which stays in cache.
#[cfg(all(target_arch = "x86_64", target_feature = "avx512f"))]
const PART: usize = PACKS;
#[cfg(all(target_arch = "x86_64", target_feature = "avx2", not(target_feature = "avx512f")))]
const PART: usize = PACKS / 2;
#[cfg(not(all(target_arch = "x86_64", target_feature = "avx2")))]
const PART: usize = 8;
const PART_WORDS: usize = 48 * PART / 64;
// `pack` reads four products to three words and `add` XORs whole vectors, so `PART` divides by four
// and `PART_WORDS` by each arm's lane count. A `PART` that broke either would drop products or store
// past the array rather than fail to build.
const _: () = assert!(PART.is_multiple_of(4));
#[cfg(all(target_arch = "x86_64", target_feature = "avx512f"))]
const _: () = assert!(PART_WORDS.is_multiple_of(8));
#[cfg(all(target_arch = "x86_64", target_feature = "avx2", not(target_feature = "avx512f")))]
const _: () = assert!(PART_WORDS.is_multiple_of(4));
#[cfg(target_arch = "aarch64")]
const _: () = assert!(PART_WORDS.is_multiple_of(2));

/// The products of a part of a block position's packs, 48 bits each, grouped while every digit
/// of the weights groups the block's positions.
#[derive(Clone, Copy)]
#[cfg_attr(all(target_arch = "x86_64", target_feature = "avx512f"), repr(C, align(64)))]
#[cfg_attr(not(all(target_arch = "x86_64", target_feature = "avx512f")), repr(C, align(16)))]
struct Part([u64; PART_WORDS]);

impl Part {
    const ZERO: Self = Self([0; PART_WORDS]);

    /// Product `q` at bits `48 * q ..`: four products to three words.
    #[inline(always)]
    fn pack(products: &[u64; PART]) -> Self {
        let mut out = [0u64; PART_WORDS];
        for (out, p) in out.as_chunks_mut::<3>().0.iter_mut().zip(products.as_chunks::<4>().0) {
            *out = [p[0] | p[1] << 48, p[1] >> 16 | p[2] << 32, p[2] >> 32 | p[3] << 16];
        }
        Self(out)
    }

    #[inline(always)]
    fn add(&mut self, other: &Self) {
        #[cfg(all(target_arch = "x86_64", target_feature = "avx512f"))]
        // SAFETY: both parts are three registers, aligned to 64, and AVX-512 is enabled at compile time.
        unsafe {
            use core::arch::x86_64::*;
            let (dst, src) = (
                self.0.as_mut_ptr().cast::<__m512i>(),
                other.0.as_ptr().cast::<__m512i>(),
            );
            for i in 0..PART_WORDS / 8 {
                let x = _mm512_xor_si512(
                    _mm512_load_si512(dst.add(i).cast()),
                    _mm512_load_si512(src.add(i).cast()),
                );
                _mm512_store_si512(dst.add(i).cast(), x);
            }
        }
        #[cfg(all(target_arch = "x86_64", target_feature = "avx2", not(target_feature = "avx512f")))]
        // SAFETY: both parts are three registers, and AVX2 is enabled at compile time.
        unsafe {
            use core::arch::x86_64::*;
            let (dst, src) = (self.0.as_mut_ptr(), other.0.as_ptr());
            for i in (0..PART_WORDS).step_by(4) {
                let (d, s) = (dst.add(i).cast::<__m256i>(), src.add(i).cast::<__m256i>());
                _mm256_storeu_si256(d, _mm256_xor_si256(_mm256_loadu_si256(d), _mm256_loadu_si256(s)));
            }
        }
        // Left to itself, the compiler XORs the words in general registers.
        #[cfg(target_arch = "aarch64")]
        // SAFETY: both parts are six words, and aarch64 always has NEON.
        unsafe {
            use core::arch::aarch64::*;
            let (dst, src) = (self.0.as_mut_ptr(), other.0.as_ptr());
            for i in (0..PART_WORDS).step_by(2) {
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
fn digit(weight: F128, d: usize) -> usize {
    let w = weight.to_limbs();
    (w[d / 8] >> (DIGIT_BITS * (d % 8))) as usize & ((1 << DIGIT_BITS) - 1)
}

/// The positions grouped by each digit of their weight: those whose digit `d` is `v` are
/// `order[d][starts[d][v]..starts[d][v + 1]]`.
struct Groups {
    order: Vec<[u16; BITS]>,
    starts: Vec<[u16; (1 << DIGIT_BITS) + 1]>,
}

impl Groups {
    fn new(weights: &[F128]) -> Self {
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
    fn add_rows(&self, payloads: &[Part; BITS], rows: &mut [Part; 128], sums: &mut [Part; 1 << DIGIT_BITS]) {
        for (rows, (order, starts)) in rows
            .as_chunks_mut::<DIGIT_BITS>()
            .0
            .iter_mut()
            .zip(self.order.iter().zip(&self.starts))
        {
            for (v, sum) in sums.iter_mut().enumerate() {
                let mut acc = Part::ZERO;
                for &p in &order[starts[v] as usize..starts[v + 1] as usize] {
                    // SAFETY: `order` holds positions.
                    acc.add(unsafe { payloads.get_unchecked(p as usize) });
                }
                *sum = acc;
            }
            // Bit `i` of the digit: the sums whose value has it, then fold it away.
            for (i, row) in rows.iter_mut().enumerate().rev() {
                let (low, high) = sums[..2 << i].split_at_mut(1 << i);
                let mut acc = Part::ZERO;
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

/// A row of a table in the power basis: two words per position, laid out by word.
const ROW: usize = 2 * BITS;

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

    /// Per pack `q` of a block, the coefficients of
    /// `sum over blocks and positions of eq(point[5..], block) * weights[j] * product(q, j)`,
    /// where the product is `ones * u[j] + (ones + u[j + 1]) * u[j + 2]` on embeddings, the
    /// unprojected `chi`.
    ///
    /// Nothing here knows where the polynomials will be evaluated, so each product meets its
    /// weight bit by bit. The position weights are the same in every block, so a block's sum
    /// over positions is taken bit by bit, by GFNI outer products where they are compiled
    /// (`products_gfni`) and by digit buckets elsewhere ([`Groups`]); only that sum meets
    /// the block's weight, as field elements.
    fn pack_products(&self, claim: &Claim) -> Vec<[F128; PRODUCT_BITS]> {
        cfg_select! {
            all(target_arch = "x86_64", target_feature = "avx2", target_feature = "gfni") => {
                self.pack_products_gfni(claim)
            }
            _ => { self.pack_products_buckets(claim) }
        }
    }

    /// [`Self::pack_products`] by GFNI outer products (`products_gfni`): the same sums.
    #[cfg(all(target_arch = "x86_64", target_feature = "avx2", target_feature = "gfni"))]
    fn pack_products_gfni(&self, claim: &Claim) -> Vec<[F128; PRODUCT_BITS]> {
        use crate::products_gfni::ProductSums;
        let weights = self.task_weights(&eq_table(&claim.point[SKIP + 1..]));
        let kernel = ProductSums::new(&claim.weights);
        let sums = parallel::map_reduce_with_state(
            self.n_tasks(),
            || kernel.scratch(),
            || vec![F128Unreduced::ZERO; PAYLOAD_BITS],
            |scratch, sums, task| {
                let (_, _, block) = self.block(task);
                kernel.block_sums(scratch, block);
                for (sum, v) in sums.iter_mut().zip(scratch.out.iter()) {
                    *sum ^= weights[task].mul_unreduced(F128::from_limbs(*v));
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

    /// [`Self::pack_products`] by digit buckets: the block's positions grouped by each digit of
    /// their weight ([`Groups`]), a part of the packs at a time. The GFNI form's test oracle.
    #[cfg_attr(
        all(target_arch = "x86_64", target_feature = "avx2", target_feature = "gfni"),
        allow(dead_code)
    )]
    fn pack_products_buckets(&self, claim: &Claim) -> Vec<[F128; PRODUCT_BITS]> {
        let weights = self.task_weights(&eq_table(&claim.point[SKIP + 1..]));
        let groups = Groups::new(&claim.weights);
        let sums = parallel::map_reduce_with_state(
            self.n_tasks(),
            || {
                (
                    vec![[Part::ZERO; BITS]; PACKS / PART],
                    vec![[Part::ZERO; 128]; PACKS / PART],
                    Box::new([Part::ZERO; 1 << DIGIT_BITS]),
                )
            },
            || vec![F128Unreduced::ZERO; PAYLOAD_BITS],
            |(payloads, rows, digit_sums), sums, task| {
                let (_, _, block) = self.block(task);
                for r in 0..5 {
                    for z in 0..64 {
                        let js = row_positions(r, z);
                        let e: [[u32; PACKS]; 5] = std::array::from_fn(|x| embed(words(block, js[x])));
                        for x in 0..5 {
                            let p = products(&e[x], &e[(x + 1) % 5], &e[(x + 2) % 5]);
                            for (q, part) in payloads.iter_mut().enumerate() {
                                part[js[x]] = Part::pack(p[PART * q..][..PART].try_into().unwrap());
                            }
                        }
                    }
                }
                for (payloads, rows) in payloads.iter().zip(rows.iter_mut()) {
                    groups.add_rows(payloads, rows, digit_sums);
                }
                // Row `r` holds bit `r` of each payload bit's weighted sum: transposed, they are
                // field elements, which the block's weight multiplies.
                let mut columns = [[0u64; 64]; 2];
                for m in 0..PAYLOAD_BITS / 64 {
                    let (q, w) = (m / PART_WORDS, m % PART_WORDS);
                    for (k, column) in columns.iter_mut().enumerate() {
                        for (b, word) in column.iter_mut().enumerate() {
                            *word = rows[q][64 * k + b].0[w];
                        }
                        transpose64(column);
                    }
                    for (t, sum) in sums[64 * m..][..64].iter_mut().enumerate() {
                        *sum ^= weights[task].mul_unreduced(F128::new(columns[0][t], columns[1][t]));
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
    /// here. A binary one is a pack, whose sum `binary` already holds. The packs of the padding
    /// block are all equal, so their extension vanishes there.
    fn skip_sums(
        &self,
        claim: &Claim,
        weights: &[Element],
        field: &PowerField,
        s: F128,
        binary: &[F128; GROUP],
    ) -> Vec<F128> {
        let groups: Vec<Element> = eq_table(&claim.point[SKIP..])
            .iter()
            .map(|&e| field.to_poly(e))
            .collect();
        let (nb, written) = (self.witness.shape.n_blocks(), self.witness.written());
        let mixed = parallel::map_reduce_with_state(
            self.rounds.len() * written,
            || SkipBlock::new(weights),
            || vec![[0u64; 5]; MIXED],
            |skip, total, task| {
                let (segment, g) = (task / written, task % written);
                let (row, block) = (g + nb * segment, self.witness.layer(self.rounds[segment], g));
                skip.run(block);
                for half in 0..2 {
                    for (i, total) in total.iter_mut().enumerate() {
                        add_mul(total, &skip.get(slot(half, i)), &groups[2 * row + half]);
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
        let eval = PolyEval::new(s, 40);
        let mut sums = vec![F128::ZERO; TERNARY];
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
    /// the first of those rounds' pairs, so the pass that builds the rows sums over them ([`Round::pass`], which
    /// `point` is for). The padding block's groups are one row, its segment's entry of `pads`.
    fn table(
        &self,
        round: &Round,
        challenges: &[F128],
        point: &[F128],
        layout: Rows,
        table: &mut [u64],
        pads: &mut [u64],
    ) -> ((F128, F128), Option<Quad>) {
        let field = round.field;
        let fold: Vec<Element> = eq_table(challenges).iter().map(|&e| field.to_poly(e)).collect();
        let fold: [[u64; GROUP]; 2] = std::array::from_fn(|k| std::array::from_fn(|q| fold[q][k]));
        #[cfg(all(
            target_arch = "x86_64",
            target_feature = "avx512f",
            target_feature = "avx512bw",
            target_feature = "gfni"
        ))]
        let row_maps = crate::table_gfni::RowMaps::new(field, &fold);
        // Rows of segments that do not exist are zero, and so is their product.
        table[self.rounds.len() * layout.live * ROW..layout.len() * ROW].fill(0);
        pads[self.rounds.len() * ROW..].fill(0);
        // The GFNI rows need no wide scratch.
        let gfni = cfg!(all(
            target_arch = "x86_64",
            target_feature = "avx512f",
            target_feature = "avx512bw",
            target_feature = "gfni"
        ));
        let scratch = || vec![0u64; if gfni { 0 } else { 6 * BITS }];
        // A block's rows: both groups', or the padding block's one.
        let build = |wide: &mut Vec<u64>, block: &[u64], rows: &mut [u64]| {
            let halves = rows.len() / ROW;
            cfg_select! {
                all(target_arch = "x86_64", target_feature = "avx512f", target_feature = "avx512bw", target_feature = "gfni") => {
                    // Each group's value by affine byte maps (`table_gfni`).
                    let _ = wide;
                    row_maps.rows(block, rows, halves);
                }
                _ => {
                    // Both groups' unreduced sums, three words each and laid out by word, then reduced.
                    for j in 0..BITS {
                        let sums = crate::kernels::fold_groups(&embed(words(block, j)), &fold);
                        for (wide, sum) in wide.as_chunks_mut::<{ 3 * BITS }>().0[..halves].iter_mut().zip(&sums) {
                            let sum: [u64; 3] = crate::basis::carry(sum);
                            for (k, &word) in sum.iter().enumerate() {
                                wide[k * BITS + j] = word;
                            }
                        }
                    }
                    for (t, wide) in rows.as_chunks_mut::<ROW>().0.iter_mut().zip(wide.as_chunks::<{ 3 * BITS }>().0) {
                        field.reduce_row(t, wide, BITS);
                    }
                }
            }
        };
        let written = self.witness.written();
        if written < self.witness.shape.n_blocks() {
            let mut wide = scratch();
            for (pad, &r) in pads.as_chunks_mut::<ROW>().0.iter_mut().zip(&self.rounds) {
                build(&mut wide, self.witness.layer(r, written), pad);
            }
        }
        // The pass writes the segments that exist, two rows a block.
        let layout = Rows {
            segments: self.rounds.len(),
            ..layout
        };
        round.pass(layout, table, pads, point, scratch, |wide, rows, segment, r| {
            for (g, rows) in rows.as_chunks_mut::<{ 2 * ROW }>().0.iter_mut().enumerate() {
                build(wide, self.witness.layer(self.rounds[segment], r / 2 + g), rows);
            }
        })
    }
}

/// The sums a pass accumulates over quads of rows, unreduced ([`Round::add`]).
#[derive(Clone, Copy, Default)]
struct Sums([[u64; 6]; 8]);

impl Sums {
    fn merge(mut self, other: Self) -> Self {
        for (x, y) in self.0.as_flattened_mut().iter_mut().zip(other.0.as_flattened()) {
            *x ^= y;
        }
        self
    }
}

/// The round after a pass's next one, summed over the quads of rows `R0..R3` its pairs fold from, before the next
/// round's challenge is known: `F(R0)`, `F(R1)`, `Q(R0 + R1)`, `Q(R0 + R2)`, `Q(R1 + R3)` and
/// `Q(R0 + R1 + R2 + R3)`, with `F` a row's value at `0` and `Q` the quadratic part of `F`, the value at infinity
/// of a pair whose rows sum to its argument.
struct Quad([F128; 6]);

impl Quad {
    /// The round's values at `0` and at infinity once the round before it binds `r`.
    ///
    /// Its pairs are `A = R0 + r (R0 + R1)` and `B = R2 + r (R2 + R3)`. `F` is quadratic, so
    /// `F(X + r Y) = F(X) + r (F(X + Y) + F(X) + Q(Y)) + r^2 Q(Y)`, and likewise `Q` with `Q` for `F`: `F(A)` is
    /// that at `X = R0`, `Y = R0 + R1`, and `Q(A + B)` at `X = R0 + R2`, `Y = R0 + R1 + R2 + R3`.
    fn at(&self, r: F128) -> (F128, F128) {
        let [f0, f1, q01, q02, q13, q0123] = self.0;
        let r2 = r.square();
        (
            f0 + r * (f0 + f1 + q01) + r2 * q01,
            q02 + r * (q02 + q13 + q0123) + r2 * q0123,
        )
    }
}

/// What a round needs of the claim, by word as a table row is: the position weights, as the split constants a row
/// is multiplied by, and each position's constant `kappa * (weights[j] + weights[j + 2])`.
struct Round<'a> {
    field: &'a PowerField,
    eval: PolyEval,
    weights: Vec<u64>,
    constant: Vec<u64>,
}

impl<'a> Round<'a> {
    /// `polys` are the claim's weights in the power basis.
    fn new(field: &'a PowerField, claim: &Claim, polys: &[Element], s: F128, kappa: F128) -> Self {
        let w = &claim.weights;
        let (mut weights, mut constant) = (vec![0u64; ROW], vec![0u64; ROW]);
        for j in 0..BITS {
            set(&mut weights, BITS, j, &polys[j]);
            set(&mut constant, BITS, j, &field.to_poly(kappa * (w[j] + w[along(j, 2)])));
        }
        Self {
            field,
            eval: PolyEval::new(s, 48),
            weights: field.split_row(&weights, BITS),
            constant,
        }
    }

    /// Add a quad of rows to a pass's sums, weighted by `eq`. With `F` a row's value at `0`,
    /// `sum over positions of B[j] * T[j + 2]`, where
    /// `B[j] = weights[j] * (kappa + T[j + 1]) + kappa * weights[j + 2]`, which is
    /// `weights[j] * T[j + 1] + constant[j]`, and `Q` its quadratic part, the value at infinity of a pair whose
    /// rows sum to its argument, they are [`PowerField::quad_sums`]'s: the values of the quad's two pairs, then
    /// what the round after takes ([`Quad`]).
    fn add(&self, sums: &mut Sums, rows: [&[u64]; 4], eq: F128) {
        // A lane is 64 positions, five lanes to a row.
        let shifted: [_; BITS / 64] = std::array::from_fn(|i| (along(64 * i, 1), along(64 * i, 2)));
        let terms = self
            .field
            .quad_sums(&self.weights, &self.constant, rows, BITS, 64, &shifted);
        let weight = self.field.to_poly(eq);
        for (sum, term) in sums.0.iter_mut().zip(&terms) {
            add_mul(sum, term, &weight);
        }
    }

    /// One pass over the table: write the rows laid out as `to` into `dst`, `write(scratch, rows, segment, r)`
    /// giving a segment's rows from `r` on, and sum over them, while they are in cache, the round that binds
    /// their first variable, `point` the claim's coordinates after it.
    ///
    /// Where a segment holds quads of rows, a quad's weight is `eq` at the coordinates after the first, which
    /// splits it between the quad's two pairs. Its sums then give the round after's values too ([`Quad`]), so the
    /// next pass binds both variables and reads the rows once. Elsewhere a pair is summed as the quad of its rows
    /// twice, and so is the last row, whose sums nothing reads.
    fn pass<S: Send>(
        &self,
        to: Rows,
        dst: &mut [u64],
        pads: &[u64],
        point: &[F128],
        scratch: impl Fn() -> S + Sync,
        write: impl Fn(&mut S, &mut [u64], usize, usize) + Sync,
    ) -> ((F128, F128), Option<Quad>) {
        let group = to.m.min(4);
        let eq = eq_table(if group == 4 { &point[1..] } else { point });
        // A task per group of rows written, the last of a segment filled with its padding row.
        let (tasks, groups) = (to.live.div_ceil(group), to.m / group);
        let ptr = parallel::SendPtr(dst[..to.len() * ROW].as_mut_ptr());
        let mut sums = parallel::map_reduce_with_state(
            to.segments * tasks,
            || (scratch(), vec![0u64; group * ROW]),
            Sums::default,
            |(scratch, rows), sums, task| {
                let (segment, t) = (task / tasks, task % tasks);
                let n = (to.live - group * t).min(group);
                write(scratch, &mut rows[..n * ROW], segment, group * t);
                let row = |k: usize| {
                    if k % group < n {
                        &rows[k % group * ROW..][..ROW]
                    } else {
                        &pads[segment * ROW..][..ROW]
                    }
                };
                self.add(sums, std::array::from_fn(row), eq[groups * segment + t]);
                // SAFETY: each task owns its rows of `dst`, among the `to.len()` it holds.
                let out = unsafe { ptr.slice((to.live * segment + group * t) * ROW, n * ROW) };
                // Built in cache for the round values, then published: the next round reads them.
                primitives::stream::Stream::new().copy(out, &rows[..n * ROW]);
            },
            Sums::merge,
        );
        // The groups of padding rows alone: each segment's padding row, once, at the sum of their weights.
        if tasks < groups {
            for (pad, eq) in pads.as_chunks::<ROW>().0.iter().zip(eq.chunks_exact(groups)) {
                self.add(&mut sums, [pad; 4], eq[tasks..].iter().sum());
            }
        }
        let [f0, q01, f2, q23, f1, q02, q13, q0123] = sums.0.map(|sum| self.eval.eval(&sum));
        if group < 4 {
            return ((f0, q01), None);
        }
        (
            (interp(f0, f2, point[0]), interp(q01, q23, point[0])),
            Some(Quad([f0, f1, q01, q02, q13, q0123])),
        )
    }

    /// Bind one or two variables, at `challenges`, on the rows of `src`, laid out as `from`, into `dst`, and
    /// sum over what was written ([`Self::pass`]). Rows are in the order their variables bind them, so a row
    /// written is the two or four it folds from, weighted by `eq` of the challenges.
    fn fold(
        &self,
        src: &[u64],
        from: Rows,
        dst: &mut [u64],
        pads: &[u64],
        challenges: &[F128],
        point: &[F128],
    ) -> ((F128, F128), Option<Quad>) {
        let to = challenges.iter().fold(from, |layout, _| layout.next());
        let eq: Vec<Element> = eq_table(challenges).iter().map(|&e| self.field.to_poly(e)).collect();
        let write = |_: &mut (), rows: &mut [u64], segment: usize, r: usize| {
            for (v, out) in (to.m * segment + r..).zip(rows.as_chunks_mut::<ROW>().0) {
                let row = |b: usize| {
                    let u = eq.len() * v + b;
                    from.row(src, pads, u / from.m, u % from.m)
                };
                let other = |b: usize| (row(b + 1), &eq[b + 1]);
                match eq.len() {
                    2 => self.field.fold_row(out, row(0), [other(0)], BITS),
                    _ => self.field.fold_row(out, row(0), [other(0), other(1), other(2)], BITS),
                }
            }
        };
        self.pass(to, dst, pads, point, || (), write)
    }
}

/// The rows of the table the tail folds: per segment, the first `live` of `m`, then, if there are
/// fewer, the padding row every later one equals, kept apart. Once a segment is down to one row, the segments'
/// rows are those of one segment.
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
            // The fold writes every segment's row, a padding one included.
            2 => Self {
                m: self.segments,
                live: self.segments,
                segments: 1,
            },
            m => Self {
                m: m / 2,
                live: self.live.div_ceil(2),
                ..*self
            },
        }
    }

    fn row<'t>(&self, table: &'t [u64], pads: &'t [u64], segment: usize, r: usize) -> &'t [u64] {
        if r < self.live {
            &table[(self.live * segment + r) * ROW..][..ROW]
        } else {
            &pads[segment * ROW..][..ROW]
        }
    }
}

/// A round of the sumcheck over bit positions, on small tables in the standard basis, entry `j`
/// holding `w, t0, t1, t2` there: the coefficients of `sum_j w (kappa t0 + (kappa + t1) t2)` in
/// the variable being bound.
fn local_round(tables: &[[F128; 4]], kappa: F128) -> [F128; 4] {
    let mut h = [F128::ZERO; 4];
    for pair in tables.as_chunks::<2>().0 {
        let [w, t0, t1, t2] = std::array::from_fn(|k| (pair[0][k], pair[0][k] + pair[1][k]));
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
    table: Vec<u64>,
    /// Each segment's padding row.
    pads: Vec<u64>,
}

impl Scratch {
    pub fn new(shape: Shape) -> Self {
        let rows = 1usize << (shape.y_vars() - SKIP);
        // SAFETY: every pass writes the rows it reads.
        let table = unsafe { primitives::uninit_vec(rows * ROW + rows * ROW / 2) };
        let pads = vec![0u64; ROW << shape.seg_log()];
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

    let per_pack = tracing::info_span!("Product").in_scope(|| layer.pack_products(claim));
    let pack_weights = eq_table(&claim.point[..SKIP + 1]);
    let product: [F128; PRODUCT_BITS] =
        std::array::from_fn(|c| (0..PACKS).map(|q| pack_weights[q] * per_pack[q][c]).sum());
    ps.add_scalars(&product);
    // `s`: the product polynomial has degree PRODUCT_BITS - 1.
    // Bad event, probability `2^-64`: `s` in `K` (which holds every proper subfield) has no power basis. A verifier
    // accepts any passing nonce, so the prover grinds on.
    let bits = fiat_shamir::grinding_bits(PRODUCT_BITS as u128 - 1);
    let s = ps.grind_sample(bits, |s| s.to_limbs()[1] != 0);
    let kappa = mu_at(s).iter().sum();
    let mut value = poly_eval(&product, s);
    let field = PowerField::new(s).expect("an `s` outside `K` has a power basis");

    // The packs of a group, from sums of bit-level products. A pack's own sum is its product
    // polynomial at `s`, over both groups of the block.
    let binary: [F128; GROUP] = std::array::from_fn(|q| {
        let half = claim.point[SKIP];
        (F128::ONE + half) * poly_eval(&per_pack[q], s) + half * poly_eval(&per_pack[GROUP + q], s)
    });
    // The claim's weights in the power basis, which Skip and the later rounds share.
    let polys: Vec<Element> = claim.weights.iter().map(|&w| field.to_poly(w)).collect();
    let mut sums = tracing::info_span!("Skip").in_scope(|| layer.skip_sums(claim, &polys, &field, s, &binary));
    let mut point = Vec::with_capacity(claim.point.len());
    for i in 0..SKIP {
        let later = eq_table(&claim.point[i + 1..SKIP]);
        let mut h = [F128::ZERO; 3];
        for (b, &eq) in later.iter().enumerate() {
            for (d, h) in h.iter_mut().enumerate() {
                *h += eq * sums[d + 3 * ternary(b)];
            }
        }
        let coeffs = [h[0], h[0] + h[1] + h[2], h[2]];
        let challenge = bind(ps, &coeffs, &mut value, &mut point);
        sums = sums
            .as_chunks::<3>()
            .0
            .iter()
            .map(|v| v[0] + challenge * (v[0] + v[1]) + (challenge.square() + challenge) * v[2])
            .collect();
    }

    // The groups, blocks and segments, on a table in the power basis. Each pass over it writes the rows after the
    // one or two variables bound since the last one, and sums the next round's values over them, or the next
    // two rounds'.
    let round = Round::new(&field, claim, &polys, s, kappa);
    let mut layout = Rows {
        m: 2 * shape.n_blocks(),
        live: 2 * witness.written(),
        segments: 1 << shape.seg_log(),
    };
    let (mut src, mut dst) = scratch.table.split_at_mut(layout.m * layout.segments * ROW);
    let pads = &mut scratch.pads;
    let (mut values, mut quad) = tracing::info_span!("Tables")
        .in_scope(|| layer.table(&round, &point, &claim.point[SKIP + 1..], layout, src, pads));
    let tail = tracing::info_span!("Tail").entered();
    // The challenges bound since the table was last written.
    let mut bound = Vec::with_capacity(2);
    for i in SKIP..claim.point.len() {
        let coeffs = round_coefficients(values.0, values.1, value, claim.point[i]);
        let challenge = bind(ps, &coeffs, &mut value, &mut point);
        bound.push(challenge);
        if let Some(quad) = quad.take() {
            // The next round's values are known: its variable is bound in the same pass.
            values = quad.at(challenge);
            continue;
        }
        let later = claim.point.get(i + 2..).unwrap_or(&[]);
        (values, quad) = round.fold(src, layout, dst, pads, &bound, later);
        layout = bound.drain(..).fold(layout, |layout, _| layout.next());
        (src, dst) = (dst, src);
    }
    let table = &src[..ROW];
    drop(tail);

    // The bit positions, in the standard basis. The cube's entries past the positions are zero,
    // so the tables hold only the positions, and a zero where a round's last pair needs one.
    let t0: Vec<F128> = (0..BITS).map(|j| field.to_field(&get(table, BITS, j))).collect();
    let mut tables: Vec<[F128; 4]> = (0..BITS)
        .map(|j| [claim.weights[j], t0[j], t0[along(j, 1)], t0[along(j, 2)]])
        .collect();
    let mut local = Vec::with_capacity(LOCAL_BITS);
    for _ in 0..LOCAL_BITS {
        if tables.len() % 2 == 1 {
            tables.push([F128::ZERO; 4]);
        }
        let coeffs = local_round(&tables, kappa);
        ps.add_round_poly(&coeffs, false);
        let challenge = ps.sample();
        local.push(challenge);
        tables = tables
            .as_chunks::<2>()
            .0
            .iter()
            .map(|[lo, hi]| std::array::from_fn(|k| interp(lo[k], hi[k], challenge)))
            .collect();
    }
    let t = [1, 2, 3].map(|k| tables[0][k]);
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

/// Send a normalized round of the sumcheck over the packs and segments and bind its variable.
fn bind(ps: &mut ProverState, coeffs: &[F128; 3], value: &mut F128, point: &mut Vec<F128>) -> F128 {
    ps.add_round_poly(coeffs, true);
    let challenge = ps.sample();
    *value = poly_eval(coeffs, challenge);
    point.push(challenge);
    challenge
}

/// The coefficients of a round polynomial `h` from its values at `0` and infinity:
/// `(1 + r) h(0) + r h(1) = value` gives the value at one.
fn round_coefficients(zero: F128, infinity: F128, value: F128, r: F128) -> [F128; 3] {
    let (c0, c2) = (zero, infinity);
    // value = c0 + r (c1 + c2).
    let c1 = (value + c0) * r.inv() + c2;
    [c0, c1, c2]
}

#[cfg(all(test, target_arch = "x86_64", target_feature = "avx2", target_feature = "gfni"))]
mod gfni_tests {
    use primitives::test_rng::Rng;

    use super::*;
    use crate::protocol::first_claim;
    use primitives::hash::STATE_LANES;

    /// The GFNI outer products give the digit buckets' sums, on dense, sparse and zero weights,
    /// with and without a padding block.
    #[test]
    fn gfni_pack_products_equal_the_buckets() {
        // 1100 instances: three blocks written, a padding block for the fourth.
        {
            let (n, depth, seed) = (1100, 12, 2);
            let mut rng = Rng::new(seed);
            let inputs: Vec<[u64; STATE_LANES]> = (0..n).map(|_| std::array::from_fn(|_| rng.next_u64())).collect();
            let shape = Shape::new(n, depth);
            let mut committed = vec![primitives::field::F64(0); 1 << shape.stack_log()];
            let witness = Witness::generate(shape, &inputs, &mut committed);
            assert!(witness.written() < shape.n_blocks(), "a padding block");
            for (step, mode) in [(0, "dense"), (depth - 1, "sparse"), (depth / 2, "lanes"), (1, "zero")] {
                let layer = Layer {
                    witness: &witness,
                    rounds: (0..shape.segments()).map(|m| shape.round(m, step)).collect(),
                };
                let mut claim = first_claim(shape, &rng.ext_vec(4), rng.ext_vec(shape.y_vars()), &rng.ext_vec(5));
                claim.weights = (0..BITS)
                    .map(|j| {
                        // Sparse: whole lane bytes and some single positions are zero. Lanes: only
                        // lanes 0..3 weigh, so rows with no active lane at all are skipped.
                        if mode == "zero"
                            || (mode == "sparse" && ((j / 8) % 3 == 1 || j % 7 == 0))
                            || (mode == "lanes" && j >= 4 * 64)
                        {
                            F128::ZERO
                        } else {
                            rng.ext()
                        }
                    })
                    .collect();
                assert!(
                    layer.pack_products_gfni(&claim) == layer.pack_products_buckets(&claim),
                    "n {n} depth {depth} step {step} {mode}"
                );
            }
        }
    }
}
