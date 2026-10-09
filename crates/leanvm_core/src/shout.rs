//! The memory and bytecode lookups, by Shout over binary fields (§sec:shout).
//!
//! A read is a row of a table naming an address `a ∈ K` and an entry, and holds
//! when `a = g^k` and the entry is `array[k]`. The prover commits, per read, the
//! one-hot encoding of `k` cut into [`N_CHUNKS`] chunks of `chunk_bits` bits: bits,
//! packed 64 to a committed word along the table's rows. Then:
//!
//! 1. **Read-checking** ([`prove_reads`]), one sumcheck per array over its
//!    addresses: every read's fingerprint `π_α(1, a, 0, entry)`, a degree-2 form in
//!    its table's columns summed against `eq(ζ, ·)`, equals the array's own
//!    fingerprint read through the one-hot rows. The forms' side is the table
//!    sumcheck's; this side leaves one value `ra(r, ζ)` per read, plus the array at
//!    `r`.
//! 2. **The cycle sumcheck** ([`prove_cycles`]), over each table's rows: `ra` is the
//!    product of its chunks, and every chunk row is one-hot, a row `f` being so
//!    exactly when `f(X)·f(1 + X) = ∏ X_h·(1 + X_h)`. The leading `1` of a read's
//!    tuple then keeps the index it names inside the array. A table's reads and chunk tables
//!    are weighted by `eq(r_sel, ·)`, so the sumcheck goes on over the chunk
//!    tables and ends on `N_CHUNKS + 2` values a table.
//! 3. **Opening.** Those values are all the table's chunk cube against a weight, so
//!    a sumcheck over the chunk cube reduces them to one evaluation of the table's
//!    packed bits, and the tables' evaluations share their packing prefix, so one
//!    ring-switched claim over all of them binds them to the commitment.
//!
//! A table's chunk tables are stacked into one committed column: with row
//! `x = b + 64·y`, bit `b` of word `u + 2^m·(y + 2^(τ-6)·c)` is chunk table `c`'s
//! bit at row `x` and position `u`, with `c = N_CHUNKS·read + chunk`. The position
//! sits below the rows so that every table's packed column starts with the same
//! coordinates, read at the same point: a verifier evaluating the opening's weight
//! shares that work across the tables.

use crate::PAR_THRESHOLD;
use crate::leaf::{BusForm, accumulate_form};
use crate::tables::{Array, N_TABLES, Read};
use crate::transcript::{Challenger, ProverState, Receiver, Transmitter, VerifierState};
use ::pcs::stack_open::{RingSwitchClaim, RingSwitchPart};
use primitives::field::{F64, F192, F192Unreduced, g_powers, index_mle, powers};
use primitives::multilinear::{eq_eval, eq_table, fold_high_inplace, mle_eval_par, poly_eval, shrink_eq_high};

pub use ::pcs::LOG_PACKING;

/// Chunks an address is cut into: `d` in §sec:shout. The cycle sumcheck's summand
/// has degree `max(d, 3) + 1`, and a read commits `d·2^m` bits per row for chunks of
/// `m = ⌈κ/d⌉` bits, so this trades committed bits against that degree. A power
/// of two, a chunk table's index holding the chunk in its low bits.
pub const N_CHUNKS: usize = 8;
/// Widest chunk: the largest array has `2^32` entries.
pub const MAX_CHUNK_BITS: usize = 32usize.div_ceil(N_CHUNKS);
/// Most reads one row makes (`BLAKE2S`: its bytecode entry and nine cells).
pub const MAX_READS: usize = 10;
/// Degree of the cycle sumcheck's summand, its `eq` factor aside: the product of a
/// read's chunks, or the one-hot test's two factors.
const DEGREE: usize = if N_CHUNKS > 2 { N_CHUNKS } else { 2 };
/// A chunk table's index is `N_CHUNKS·read + chunk`, the chunk in its low bits.
const LOG_N_CHUNKS: usize = N_CHUNKS.trailing_zeros() as usize;
const _: () = assert!(N_CHUNKS.is_power_of_two());
/// Coefficients of a cycle sumcheck round polynomial, the `eq` factor included.
pub const CYCLE_COEFFS: usize = DEGREE + 2;

/// Slot of the first entry coordinate in a read's tuple, after the leading `1`, the
/// address and one unused slot. A bytecode column's slot IS its tuple coordinate,
/// which is what makes a bytecode read's entry one evaluation of the stacked
/// polynomial at `(r, α⃗)` (§sec:e2e-bc).
pub const ENTRY_SLOT: usize = 3;
/// Selector bits of the stacked bytecode polynomial: its eight columns sit at
/// their tuple slots, among `2^N_BYTECODE_SELECTORS`.
pub const N_BYTECODE_SELECTORS: usize = crate::leaf::N_TUPLE_BITS;

/// Columns of the bytecode's encoding: the opcode and seven operand slots.
pub const BYTECODE_COLUMNS: usize = 8;

/// The stacked bytecode polynomial as a dense table: the public encoding columns at
/// their tuple slots, padded to sixteen. This is the polynomial [`BytecodeClaim`]s
/// are claims about; the outermost verifier evaluates it.
pub fn stacked_bytecode_table(columns: &[Vec<F64>; BYTECODE_COLUMNS]) -> Vec<F64> {
    let len = columns[0].len();
    let mut table = vec![F64::ZERO; len << N_BYTECODE_SELECTORS];
    for (i, vals) in columns.iter().enumerate() {
        let slot = ENTRY_SLOT + i;
        assert!(slot < 1 << N_BYTECODE_SELECTORS, "a public slot is a tuple coordinate");
        assert_eq!(vals.len(), len);
        table[slot * len..(slot + 1) * len].copy_from_slice(vals);
    }
    table
}

/// One reduced claim on the stacked bytecode polynomial `B̃`, in `κ_bc + 4`
/// variables: what the bytecode's read-checking leaves. The native verifier
/// evaluates it; the recursive verifier defers it to its public input.
#[derive(Clone, Debug)]
pub struct BytecodeClaim {
    /// `r ++ α⃗`.
    pub point: Vec<F192>,
    /// `B̃(point)`.
    pub value: F192,
}

impl BytecodeClaim {
    /// Evaluate the stacked bytecode at `(r, α⃗)`: its columns at `r`, each weighted
    /// by its slot's `eq(α⃗, ·)`. The slots around them are zero and are not walked.
    fn evaluate(bytecode: &[F64], r: &[F192], alphas: &[F192], weights: &[F192]) -> Self {
        let len = 1usize << r.len();
        let value = (ENTRY_SLOT..ENTRY_SLOT + BYTECODE_COLUMNS).fold(F192::ZERO, |acc, slot| {
            acc + weights[slot] * mle_eval_par(&bytecode[slot * len..(slot + 1) * len], r)
        });
        Self {
            point: [r, alphas].concat(),
            value,
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Error {
    Truncated,
    ReadCheck(Array),
    Cycle,
    Opening,
    Slices,
}

/// Bits of a table's chunk cube above the chunk position: its chunk tables, padded
/// to a power of two.
fn slab_bits(n_reads: usize) -> usize {
    crate::log2_ceil_usize(N_CHUNKS * n_reads)
}

/// `log2` of the committed words holding a table's one-hot bits.
pub fn hot_kappa(tau: usize, chunk_bits: usize, n_reads: usize) -> usize {
    tau + chunk_bits + slab_bits(n_reads) - LOG_PACKING
}

/// The public shape of the lookups: derived from the announced sizes alone.
pub struct Shape {
    /// `log2` of the memory and of the bytecode, in [`Array`] order.
    pub log_size: [usize; 2],
    /// `m`: bits per address chunk.
    pub chunk_bits: usize,
    pub taus: [usize; N_TABLES],
    /// Each table's reads, their coordinates in GLOBAL column indices.
    pub reads: [Vec<Read>; N_TABLES],
    /// Each table's `(first global column, column count)`.
    pub spans: [(usize, usize); N_TABLES],
    /// Where each table's one-hot bits sit in the committed stack.
    pub hot_offsets: [usize; N_TABLES],
}

impl Shape {
    fn n_reads(&self) -> usize {
        self.reads.iter().map(Vec::len).sum()
    }

    /// Global index of table `t`'s first read; chunk table `(read, chunk)` is then
    /// global chunk table `N_CHUNKS·read + chunk`.
    fn read_base(&self, t: usize) -> usize {
        self.reads[..t].iter().map(Vec::len).sum()
    }

    fn n_chunk_tables(&self, t: usize) -> usize {
        N_CHUNKS * self.reads[t].len()
    }

    /// Variables of table `t`'s chunk cube: position, then chunk table.
    fn cube_bits(&self, t: usize) -> usize {
        self.chunk_bits + slab_bits(self.reads[t].len())
    }

    /// Selector bits of the largest table: the cycle sumcheck's selector rounds run
    /// over every table's chunk tables extended by zeros to this many.
    fn sel_bits(&self) -> usize {
        self.reads.iter().map(|reads| slab_bits(reads.len())).max().unwrap()
    }

    /// Chunk `i` of an address.
    #[inline(always)]
    pub(crate) fn chunk(&self, addr: u32, i: usize) -> usize {
        (addr as usize >> (i * self.chunk_bits)) & ((1 << self.chunk_bits) - 1)
    }

    /// Chunk `i` of an array's read-checking point, as a chunk position: zero past
    /// the array's own address bits, which is where an in-range address has none.
    fn chunk_point(&self, r: &[F192], i: usize) -> Vec<F192> {
        (i * self.chunk_bits..(i + 1) * self.chunk_bits)
            .map(|k| r.get(k).copied().unwrap_or(F192::ZERO))
            .collect()
    }

    /// Per table, its reads' batched fingerprints as one form over its columns:
    /// `Σ_p λ^p·π_α(tuple_p)`.
    fn forms(&self, weights: &[F192], lambda_rd: &[F192]) -> Vec<BusForm> {
        (0..N_TABLES)
            .map(|t| {
                let (base, n_cols) = self.spans[t];
                let mut form = BusForm::new(n_cols);
                for (j, read) in self.reads[t].iter().enumerate() {
                    let lambda = lambda_rd[self.read_base(t) + j];
                    for (i, c) in read.tuple.iter().enumerate() {
                        accumulate_form(c, lambda * weights[i], base, &mut form);
                    }
                }
                form
            })
            .collect()
    }

    /// The reads of `array`, as `(table, local read, global read)`.
    fn reads_of(&self, array: Array) -> impl Iterator<Item = (usize, usize, usize)> + '_ {
        (0..N_TABLES).flat_map(move |t| {
            let base = self.read_base(t);
            self.reads[t]
                .iter()
                .enumerate()
                .filter(move |(_, read)| read.array == array)
                .map(move |(j, _)| (t, j, base + j))
        })
    }
}

/// What the prover reads beside the table columns.
pub struct Witness<'a> {
    /// The memory's three limbs.
    pub mem: [&'a [F64]; 3],
    /// The stacked bytecode ([`stacked_bytecode_table`]).
    pub bytecode: &'a [F64],
    /// `addrs[t][row][read]`: the entry each read looks up.
    pub addrs: &'a [Vec<[u32; MAX_READS]>; N_TABLES],
}

/// What read-checking leaves, the same on both sides.
pub struct Reads {
    /// Per table, its reads' batched fingerprint, for the table sumcheck to sum.
    pub forms: Vec<BusForm>,
    /// What those forms sum to over all tables. Transmitted, and pinned twice: by
    /// the table sumcheck's target and by the read-checking sumchecks.
    pub total: F192,
    /// The read-checking points, in [`Array`] order.
    points: [Vec<F192>; 2],
    /// `ra_p(r, ζ)` per global read, for the cycle sumcheck to settle.
    evals: Vec<F192>,
    /// The memory's limbs at its point: claims on committed columns.
    pub mem_point: Vec<F192>,
    pub mem_evals: [F192; 3],
    pub bytecode_claim: BytecodeClaim,
}

const ARRAYS: [Array; 2] = [Array::Memory, Array::Bytecode];

// ---- the plain product sumcheck ---------------------------------------------

/// `table[i] = interp(table[i], table[i + half], r)` across the pool.
fn fold_high(table: &mut Vec<F192>, r: F192) {
    let half = table.len() / 2;
    if half < PAR_THRESHOLD {
        return fold_high_inplace(table, r);
    }
    let (lo, hi) = table.split_at_mut(half);
    parallel::chunks_mut2(lo, hi, PAR_THRESHOLD, |_, lo, hi| {
        for (l, h) in lo.iter_mut().zip(hi.iter()) {
            *l += r * (*l + *h);
        }
    });
    table.truncate(half);
}

/// Prove `Σ_x Σ_i a_i(x)·b_i(x) = claim` over tables of one size, binding the top
/// variable first. Returns the point, indexed by variable; the tables are left
/// folded to their evaluations there.
fn prove_products(pairs: &mut [(Vec<F192>, Vec<F192>)], mut claim: F192, ps: &mut ProverState) -> Vec<F192> {
    let n = crate::log2_strict_usize(pairs[0].0.len());
    let mut point = vec![F192::ZERO; n];
    for m in (0..n).rev() {
        let half = 1usize << m;
        let mut c = [F192::ZERO; 2];
        for (a, b) in pairs.iter() {
            let term = |i: usize| {
                [
                    a[i].mul_unreduced(b[i]),
                    (a[i] + a[i + half]).mul_unreduced(b[i] + b[i + half]),
                ]
            };
            let xor = |x: [F192Unreduced; 2], y: [F192Unreduced; 2]| [x[0] ^ y[0], x[1] ^ y[1]];
            let zero = || [F192Unreduced::ZERO; 2];
            let sums = if half >= PAR_THRESHOLD {
                parallel::map_reduce(half, zero, term, xor)
            } else {
                (0..half).map(term).fold(zero(), xor)
            };
            c[0] += sums[0].reduce();
            c[1] += sums[1].reduce();
        }
        // `h(0) + h(1) = c_1 + c_2` in characteristic 2.
        let h = [c[0], claim + c[1], c[1]];
        ps.add_round_poly(&h, false);
        let r = ps.sample();
        claim = poly_eval(&h, r);
        point[m] = r;
        for (a, b) in pairs.iter_mut() {
            fold_high(a, r);
            fold_high(b, r);
        }
    }
    point
}

/// Verifier of a plain sumcheck of `n` rounds whose round polynomial has
/// `n_coeffs` coefficients: the point, indexed by variable, and the final claim.
fn verify_rounds(
    n: usize,
    n_coeffs: usize,
    mut claim: F192,
    vs: &mut VerifierState,
) -> Result<(Vec<F192>, F192), Error> {
    let mut point = vec![F192::ZERO; n];
    for m in (0..n).rev() {
        let h = vs
            .next_round_poly(n_coeffs, claim, None)
            .map_err(|_| Error::Truncated)?;
        let r = vs.sample();
        claim = poly_eval(&h, r);
        point[m] = r;
    }
    Ok((point, claim))
}

/// The MLE of an `E`-valued table at a point.
fn mle_eval_e(table: &[F192], point: &[F192]) -> F192 {
    let mut table = table.to_vec();
    for &r in point.iter().rev() {
        fold_high_inplace(&mut table, r);
    }
    table[0]
}

// ---- read-checking ----------------------------------------------------------

/// The array's side of read-checking at `r`: its own fingerprint `π_α(1, g^k, 0,
/// entry_k)` there, from the entry's fingerprint.
fn array_fingerprint(weights: &[F192], r: &[F192], entry: F192) -> F192 {
    weights[0] + weights[1] * index_mle(r) + entry
}

/// Prove every read against its array, down to the claims [`prove_cycles`] and the
/// opening settle. `zeta` is the table sumcheck's eq point and `weights` the
/// fingerprint weights `eq(α⃗, ·)`.
pub fn prove_reads(
    shape: &Shape,
    wit: &Witness<'_>,
    zeta: &[F192],
    alphas: &[F192],
    weights: &[F192],
    ps: &mut ProverState,
) -> Reads {
    let lambda_rd = powers(ps.sample(), shape.n_reads());
    let forms = shape.forms(weights, &lambda_rd);
    let eqs: Vec<Vec<F192>> = shape.taus.iter().map(|&tau| eq_table(&zeta[..tau])).collect();

    // `R(k) = Σ_p λ^p·ra_p(k, ζ)`: each row's weight, scattered to the entry it reads.
    let scatter = |array: Array| -> Vec<F192> {
        let size = 1usize << shape.log_size[array as usize];
        let mut r = vec![F192::ZERO; size];
        // Disjoint address ranges, one a worker, each scanning the rows once for the
        // reads that land in it: the scan is sequential and the writes stay in range.
        let mut reads: [Vec<(usize, F192)>; N_TABLES] = Default::default();
        for (t, j, p) in shape.reads_of(array) {
            reads[t].push((j, lambda_rd[p]));
        }
        let chunk = size.div_ceil(parallel::num_threads()).max(1 << 10);
        parallel::chunks_mut(&mut r, chunk, |ci, part| {
            let lo = ci * chunk;
            for (t, reads) in reads.iter().enumerate() {
                for (row, &e) in wit.addrs[t].iter().zip(&eqs[t]) {
                    for &(j, lambda) in reads {
                        if let Some(slot) = (row[j] as usize).checked_sub(lo).and_then(|a| part.get_mut(a)) {
                            *slot += e * lambda;
                        }
                    }
                }
            }
        });
        r
    };
    // `Φ(k) = π_α(1, g^k, 0, entry_k)`.
    let gpow = g_powers(1usize << shape.log_size[0].max(shape.log_size[1]));
    let entry = |array: Array, k: usize| -> F192Unreduced {
        match array {
            Array::Memory => (0..3).fold(F192Unreduced::ZERO, |acc, i| {
                acc ^ weights[ENTRY_SLOT + i].mul_base_unreduced(wit.mem[i][k])
            }),
            Array::Bytecode => {
                let len = 1usize << shape.log_size[1];
                (ENTRY_SLOT..ENTRY_SLOT + BYTECODE_COLUMNS).fold(F192Unreduced::ZERO, |acc, slot| {
                    acc ^ weights[slot].mul_base_unreduced(wit.bytecode[slot * len + k])
                })
            }
        }
    };
    let mut pairs: Vec<(Vec<F192>, Vec<F192>)> = ARRAYS
        .iter()
        .map(|&array| {
            let phi = parallel::map_collect(1usize << shape.log_size[array as usize], |k| {
                weights[0] + (entry(array, k) ^ weights[1].mul_base_unreduced(gpow[k])).reduce()
            });
            (scatter(array), phi)
        })
        .collect();
    drop(gpow);
    let dot = |(a, b): &(Vec<F192>, Vec<F192>)| {
        parallel::map_reduce(
            a.len(),
            || F192Unreduced::ZERO,
            |k| a[k].mul_unreduced(b[k]),
            |x, y| x ^ y,
        )
        .reduce()
    };
    let sums = [dot(&pairs[0]), dot(&pairs[1])];
    ps.add_scalars(&sums);

    let mut points: [Vec<F192>; 2] = Default::default();
    let mut evals = vec![F192::ZERO; shape.n_reads()];
    let mut mem_evals = [F192::ZERO; 3];
    for &array in &ARRAYS {
        let a = array as usize;
        let point = prove_products(&mut pairs[a..=a], sums[a], ps);
        pairs[a] = Default::default();
        // `ra_p(r, ζ) = Σ_x eq(ζ, x)·eq(r, addr_p(x))`, the second factor split into
        // two tables over the address's halves.
        let split = point.len() / 2;
        let (eq_lo, eq_hi) = (eq_table(&point[..split]), eq_table(&point[split..]));
        for (t, j, p) in shape.reads_of(array) {
            evals[p] = parallel::map_reduce(
                wit.addrs[t].len(),
                || F192Unreduced::ZERO,
                |x| {
                    let addr = wit.addrs[t][x][j] as usize;
                    let ra = eq_lo[addr & ((1 << split) - 1)] * eq_hi[addr >> split];
                    eqs[t][x].mul_unreduced(ra)
                },
                |x, y| x ^ y,
            )
            .reduce();
            ps.add_scalar(evals[p]);
        }
        if array == Array::Memory {
            mem_evals = wit.mem.map(|limb| mle_eval_par(limb, &point));
            ps.add_scalars(&mem_evals);
        }
        points[a] = point;
    }
    Reads {
        forms,
        total: sums[0] + sums[1],
        mem_point: points[0].clone(),
        mem_evals,
        bytecode_claim: BytecodeClaim::evaluate(wit.bytecode, &points[1], alphas, weights),
        points,
        evals,
    }
}

/// Verifier of [`prove_reads`]. `bytecode` is the stacked bytecode polynomial.
pub fn verify_reads(
    shape: &Shape,
    bytecode: &[F64],
    alphas: &[F192],
    weights: &[F192],
    vs: &mut VerifierState,
) -> Result<Reads, Error> {
    let lambda_rd = powers(vs.sample(), shape.n_reads());
    let forms = shape.forms(weights, &lambda_rd);
    let sums = vs.next_scalars(2).map_err(|_| Error::Truncated)?;

    let mut points: [Vec<F192>; 2] = Default::default();
    let mut evals = vec![F192::ZERO; shape.n_reads()];
    let mut mem_evals = [F192::ZERO; 3];
    let mut bytecode_claim = None;
    for &array in &ARRAYS {
        let a = array as usize;
        let (point, claim) = verify_rounds(shape.log_size[a], 3, sums[a], vs)?;
        let mut ra = F192::ZERO;
        for (_, _, p) in shape.reads_of(array) {
            evals[p] = vs.next_scalar().map_err(|_| Error::Truncated)?;
            ra += lambda_rd[p] * evals[p];
        }
        let entry = match array {
            Array::Memory => {
                for e in &mut mem_evals {
                    *e = vs.next_scalar().map_err(|_| Error::Truncated)?;
                }
                (0..3).fold(F192::ZERO, |acc, i| acc + weights[ENTRY_SLOT + i] * mem_evals[i])
            }
            Array::Bytecode => {
                let claim = BytecodeClaim::evaluate(bytecode, &point, alphas, weights);
                let value = claim.value;
                bytecode_claim = Some(claim);
                value
            }
        };
        if claim != ra * array_fingerprint(weights, &point, entry) {
            return Err(Error::ReadCheck(array));
        }
        points[a] = point;
    }
    Ok(Reads {
        forms,
        total: sums[0] + sums[1],
        mem_point: points[0].clone(),
        mem_evals,
        bytecode_claim: bytecode_claim.expect("the bytecode is an array"),
        points,
        evals,
    })
}

// ---- the cycle sumcheck -----------------------------------------------------

/// The one-hot test's second point and right-hand side (Lemma lem:onehot): a
/// multilinear `f` is one-hot exactly when `f(X)·f(1 + X) = ∏ X_h·(1 + X_h)`.
fn one_hot_point(r: &[F192]) -> (Vec<F192>, F192) {
    let flipped: Vec<F192> = r.iter().map(|&x| F192::ONE + x).collect();
    let product = r.iter().zip(&flipped).fold(F192::ONE, |acc, (&x, &y)| acc * x * y);
    (flipped, product)
}

/// The cycle sumcheck's challenges.
struct CycleSetup {
    r_hot: Vec<F192>,
    r_hot_bar: Vec<F192>,
    c_hot: F192,
    /// `eq(r_sel, ·)` over the selector cube: chunk table `c` of a table weighs
    /// `eq(r_sel, c)`, and a read what its chunk 0 does.
    eq_sel: Vec<F192>,
    r_sel: Vec<F192>,
    /// Powers of `λ_cyc`: table `t`'s reads take power `2t`, its one-hot tests `2t + 1`.
    lambda_cyc: Vec<F192>,
    /// Per array, the chunk points of its read-checking point.
    chunk_points: [Vec<Vec<F192>>; 2],
}

impl CycleSetup {
    fn sample(shape: &Shape, reads: &Reads, ch: &mut impl Challenger) -> Self {
        let r_hot: Vec<F192> = (0..shape.chunk_bits).map(|_| ch.sample()).collect();
        let (r_hot_bar, c_hot) = one_hot_point(&r_hot);
        let r_sel: Vec<F192> = (0..shape.sel_bits()).map(|_| ch.sample()).collect();
        let lambda_cyc = powers(ch.sample(), 2 * N_TABLES);
        let chunk_points = [0, 1].map(|a| (0..N_CHUNKS).map(|i| shape.chunk_point(&reads.points[a], i)).collect());
        Self {
            r_hot,
            r_hot_bar,
            c_hot,
            eq_sel: eq_table(&r_sel),
            r_sel,
            lambda_cyc,
            chunk_points,
        }
    }

    /// Weight of read `j` of table `t`'s chunk product.
    fn read_weight(&self, t: usize, j: usize) -> F192 {
        self.lambda_cyc[2 * t] * self.eq_sel[N_CHUNKS * j]
    }

    /// Weight of chunk table `c` of table `t`'s one-hot test.
    fn chunk_weight(&self, t: usize, c: usize) -> F192 {
        self.lambda_cyc[2 * t + 1] * self.eq_sel[c]
    }

    /// What table `t` claims to sum to: its reads' `ra` values, and `c_hot` for
    /// every row of every chunk table.
    fn sigma(&self, shape: &Shape, reads: &Reads, t: usize) -> F192 {
        let base = shape.read_base(t);
        let one_hot = (0..shape.n_chunk_tables(t)).fold(F192::ZERO, |acc, c| acc + self.chunk_weight(t, c));
        (0..shape.reads[t].len()).fold(self.c_hot * one_hot, |acc, j| {
            acc + self.read_weight(t, j) * reads.evals[base + j]
        })
    }

    /// Table `t`'s summand at one point of the selector cube, its `eq(r_sel, ·)`
    /// weight aside: `chunk0` is the indicator of a read's chunk 0 there, `f` its
    /// chunk tables at their chunk points, chunk by chunk, `g` and `h` the chunk
    /// table at `r_hot` and at `1 + r_hot`.
    fn summand(&self, t: usize, chunk0: F192, f: &[F192], g: F192, h: F192) -> F192 {
        let product = f.iter().fold(chunk0, |acc, &v| acc * v);
        self.lambda_cyc[2 * t] * product + self.lambda_cyc[2 * t + 1] * g * h
    }
}

/// The coefficients of the polynomial of degree below `ys.len()` taking the values
/// `ys` at the points `0, 1, 2, …` of `K`.
fn interpolate(ys: &[F192]) -> Vec<F192> {
    let n = ys.len();
    let xs: Vec<F192> = (0..n).map(|j| F192::from(F64(j as u64))).collect();
    let mut coeffs = vec![F192::ZERO; n];
    for i in 0..n {
        let mut num = vec![F192::ONE];
        let mut den = F192::ONE;
        for j in (0..n).filter(|&j| j != i) {
            den *= xs[i] + xs[j];
            num.push(F192::ZERO);
            for k in (1..num.len()).rev() {
                num[k] = num[k - 1] + num[k] * xs[j];
            }
            num[0] *= xs[j];
        }
        let scale = ys[i] * den.inv();
        for (c, &v) in coeffs.iter_mut().zip(&num) {
            *c += scale * v;
        }
    }
    coeffs
}

/// Coefficients of `∏ (lo_i + d_i·Y)` over `lines = [(lo_i, d_i)]`, constant first,
/// into `out`; returns their number. A balanced tree: pairs by Karatsuba, then
/// schoolbook products with one reduction per coefficient. Karatsuba further up
/// lost to it, its sums of wide values costing more than the products they save.
#[inline]
fn line_product(lines: &[(F192, F192)], out: &mut [F192; N_CHUNKS + 1]) -> usize {
    match lines {
        [l] => {
            out[0] = l.0;
            out[1] = l.1;
            2
        }
        [a, b] => {
            let (lo, hi) = (a.0 * b.0, a.1 * b.1);
            out[0] = lo;
            out[1] = (a.0 + a.1) * (b.0 + b.1) + lo + hi;
            out[2] = hi;
            3
        }
        _ => {
            let (left, right) = lines.split_at(lines.len() / 2);
            let (mut pa, mut pb) = ([F192::ZERO; N_CHUNKS + 1], [F192::ZERO; N_CHUNKS + 1]);
            let (na, nb) = (line_product(left, &mut pa), line_product(right, &mut pb));
            let mut acc = [F192Unreduced::ZERO; N_CHUNKS + 1];
            for (i, &x) in pa[..na].iter().enumerate() {
                for (j, &y) in pb[..nb].iter().enumerate() {
                    acc[i + j] ^= x.mul_unreduced(y);
                }
            }
            for (o, v) in out.iter_mut().zip(&acc[..na + nb - 1]) {
                *o = v.reduce();
            }
            na + nb - 1
        }
    }
}

/// XOR the coefficients of `∏ (lo_i + d_i·Y)` into `acc`, the last product of the
/// tree left unreduced: a round reduces its sum of them once.
#[inline]
fn add_line_product(lines: &[(F192, F192)], acc: &mut [F192Unreduced; N_CHUNKS + 1]) {
    if let [line] = lines {
        acc[0] ^= line.0.into();
        acc[1] ^= line.1.into();
        return;
    }
    let (left, right) = lines.split_at(lines.len() / 2);
    let (mut a, mut b) = ([F192::ZERO; N_CHUNKS + 1], [F192::ZERO; N_CHUNKS + 1]);
    let (na, nb) = (line_product(left, &mut a), line_product(right, &mut b));
    for (i, &x) in a[..na].iter().enumerate() {
        for (j, &y) in b[..nb].iter().enumerate() {
            acc[i + j] ^= x.mul_unreduced(y);
        }
    }
}

/// A round's running sums: the chunk products unreduced, then the accumulators.
type RoundAcc = ([F192Unreduced; N_CHUNKS + 1], [F192; N_ACC]);

const ROUND_ZERO: RoundAcc = ([F192Unreduced::ZERO; N_CHUNKS + 1], [F192::ZERO; N_ACC]);

fn xor_round(mut a: RoundAcc, b: RoundAcc) -> RoundAcc {
    for (x, y) in a.0.iter_mut().zip(b.0) {
        *x ^= y;
    }
    (a.0, xor_acc(a.1, b.1))
}

fn finish_round((products, mut acc): RoundAcc) -> [F192; N_ACC] {
    for (slot, v) in acc.iter_mut().zip(products) {
        *slot += v.reduce();
    }
    acc
}

/// Rows below which a round of the cycle sumcheck is not worth dispatching: far
/// under [`PAR_THRESHOLD`], a row being hundreds of products.
const CYCLE_PAR_THRESHOLD: usize = 1 << 5;

/// `table[lo] + r·(table[lo] + table[hi])` over every pair `lo | hi << width` of its
/// entries: the table one round on, its index twice as wide.
fn fold_pairs(table: &[F192], r: F192) -> Vec<F192> {
    let width = table.len().trailing_zeros();
    (0..table.len() * table.len())
        .map(|pair| {
            let (lo, hi) = (table[pair & (table.len() - 1)], table[pair >> width]);
            lo + r * (lo + hi)
        })
        .collect()
}

/// Accumulators of one table's round message, all of them coefficients: of the
/// chunk products, then of the one-hot products.
const N_ACC: usize = N_CHUNKS + 1 + 3;

fn xor_acc(mut a: [F192; N_ACC], b: [F192; N_ACC]) -> [F192; N_ACC] {
    for (x, y) in a.iter_mut().zip(b) {
        *x += y;
    }
    a
}

/// One table's part of the cycle sumcheck.
struct CycleTable {
    /// Per read, its array, its weight, and how many of its chunks an address
    /// reaches. A chunk past them is position 0 on every row, at a chunk point of
    /// zeros: a factor 1 of the product, and a one-hot product that is `c_hot` on
    /// every row, so the prover leaves it out of every round but for `dead`.
    reads: Vec<(usize, F192, usize)>,
    /// Weights of the chunk tables' one-hot tests.
    lambda_chunks: Vec<F192>,
    /// What the chunk tables left out add to a round's constant coefficient.
    dead: F192,
    cols: Cols,
}

/// A table's columns: column `c < n` is chunk table `c` at its chunk point (chunk 0
/// scaled by its read's weight), column `n + c` the same at `r_hot`, and column
/// `2n + c` at `1 + r_hot`, scaled by its weight. The columns of a chunk no address
/// reaches are left empty.
impl CycleTable {
    fn is_live(&self, c: usize) -> bool {
        c % N_CHUNKS < self.reads[c / N_CHUNKS].2
    }
}

enum Cols {
    Lookup(Lookup),
    Dense(Vec<Vec<F192>>),
}

/// The columns before they are worth materializing. A chunk table's column takes
/// `2^m` values, so its first rounds depend on a row only through the positions
/// its `2^depth` cosets read: a round's one-hot products come off a
/// histogram of those tuples at an addition a row, and its chunk products off
/// tables a few entries wide. Only what is left after `depth` rounds is
/// materialized, a quarter the height for `depth = 2`.
struct Lookup {
    /// Rounds answered from tuples: two while a tuple of four positions indexes a
    /// table that stays in cache, else one.
    depth: usize,
    /// Rounds done.
    round: usize,
    chunk_bits: usize,
    n_chunk_tables: usize,
    /// `idx[x·n + c]`: the positions chunk table `c` reads on the `2^depth` rows
    /// `x + j·2^(τ-depth)`, packed in the order the rounds pair them (`j`
    /// bit-reversed), so a round's pairs are adjacent.
    idx: Vec<u16>,
    /// Per chunk table, the `eq` weight of the rows of every tuple.
    hist: Vec<F192>,
    /// The eq tables one entry per element, folded as the rounds go: per array
    /// and chunk at its chunk point, then at `r_hot` and at `1 + r_hot`.
    at_chunk: [Vec<Vec<F192>>; 2],
    at_r_hot: Vec<F192>,
    at_r_hot_bar: Vec<F192>,
}

/// Widest tuple index a histogram is kept for.
const MAX_TUPLE_BITS: usize = 12;

impl Lookup {
    fn new(shape: &Shape, addrs: &[[u32; MAX_READS]], n_chunk_tables: usize, setup: &CycleSetup) -> Self {
        let m = shape.chunk_bits;
        let depth = if 4 * m <= MAX_TUPLE_BITS { 2 } else { 1 };
        assert!(2 * m <= 16, "a pair of positions indexes a u16");
        let step = addrs.len() >> depth;
        let n = n_chunk_tables;
        let mut idx = vec![0u16; step * n];
        parallel::chunks_mut(&mut idx, n, |x, row| {
            for (c, slot) in row.iter_mut().enumerate() {
                *slot = (0..1usize << depth).fold(0, |acc, e| {
                    // Element `e` is the row whose top `depth` bits are `e`'s, reversed.
                    let j = e.reverse_bits() >> (usize::BITS as usize - depth);
                    let u = shape.chunk(addrs[x + j * step][c / N_CHUNKS], c % N_CHUNKS);
                    acc | (u << (e * m)) as u16
                });
            }
        });
        Self {
            depth,
            round: 0,
            chunk_bits: m,
            n_chunk_tables: n,
            idx,
            hist: Vec::new(),
            at_chunk: [0, 1].map(|a| setup.chunk_points[a].iter().map(|p| eq_table(p)).collect()),
            at_r_hot: eq_table(&setup.r_hot),
            at_r_hot_bar: eq_table(&setup.r_hot_bar),
        }
    }

    /// Bits of one element's index this round, and the pairs of elements a tuple holds.
    fn shape(&self) -> (usize, usize) {
        (self.chunk_bits << self.round, 1 << (self.depth - self.round - 1))
    }

    /// Each chunk table's histogram: the `eq` weight of every tuple of positions,
    /// summed over the rows the tuple spans. `eqr` is the eq table of the round the
    /// table joins at, over half its rows.
    fn build_hist(&self, table: &CycleTable, eqr: &[F192]) -> Vec<F192> {
        let n = self.n_chunk_tables;
        let size = 1usize << (self.chunk_bits << self.depth);
        let step = self.idx.len() / n;
        let idx = &self.idx;
        let add = |hist: &mut Vec<F192>, x: usize| {
            let w = (0..eqr.len() / step).fold(F192::ZERO, |acc, k| acc + eqr[x + k * step]);
            for (c, &i) in idx[x * n..(x + 1) * n].iter().enumerate() {
                if table.is_live(c) {
                    hist[c * size + i as usize] += w;
                }
            }
        };
        let zero = || vec![F192::ZERO; n * size];
        if step >= PAR_THRESHOLD {
            parallel::fold_reduce(step, zero, add, xor_slices)
        } else {
            let mut hist = zero();
            (0..step).for_each(|x| add(&mut hist, x));
            hist
        }
    }

    /// The round's accumulators. `zeta_below` is the eq point's coordinate under
    /// the variable being bound, which weighs a tuple's two pairs apart.
    fn accumulate(&self, table: &CycleTable, eqr: &[F192], zeta_below: F192) -> [F192; N_ACC] {
        let n = self.n_chunk_tables;
        let (width, pairs) = self.shape();
        let mask = (1usize << width) - 1;
        let n_pairs = 1usize << (2 * width);
        let step = self.idx.len() / n;
        let pair_weights = match pairs {
            1 => vec![F192::ONE],
            2 => vec![F192::ONE + zeta_below, zeta_below],
            _ => unreachable!("a tuple holds at most four rows"),
        };

        // The one-hot products, off the histograms: every pair of elements a tuple
        // holds, weighted, against what that pair of entries contributes.
        let per_pair: Vec<[F192; 3]> = (0..n_pairs)
            .map(|pair| {
                let (a, b) = (self.at_r_hot[pair & mask], self.at_r_hot[pair >> width]);
                let (c, d) = (self.at_r_hot_bar[pair & mask], self.at_r_hot_bar[pair >> width]);
                // `(a + (a + b)·Y)·(c + (c + d)·Y)`.
                [a * c, a * d + b * c, (a + b) * (c + d)]
            })
            .collect();
        let size = self.hist.len() / n;
        let chunk_table = |c: usize| -> [F192; N_ACC] {
            if !table.is_live(c) {
                return [F192::ZERO; N_ACC];
            }
            let hist = &self.hist[c * size..(c + 1) * size];
            let mut acc = [F192Unreduced::ZERO; 3];
            let mut add = |weight: F192, pair: usize| {
                for (slot, &v) in acc.iter_mut().zip(&per_pair[pair]) {
                    *slot ^= weight.mul_unreduced(v);
                }
            };
            if pairs == 1 {
                hist.iter().enumerate().for_each(|(pair, &w)| add(w, pair));
            } else {
                // Marginalize the tuple onto each of its two pairs.
                let mut marginal = vec![F192::ZERO; n_pairs];
                for (i, &w) in hist.iter().enumerate() {
                    marginal[i & (n_pairs - 1)] += pair_weights[0] * w;
                    marginal[i >> (2 * width)] += pair_weights[1] * w;
                }
                marginal.iter().enumerate().for_each(|(pair, &w)| add(w, pair));
            }
            let mut out = [F192::ZERO; N_ACC];
            for (slot, v) in out[N_CHUNKS + 1..].iter_mut().zip(acc) {
                *slot = table.lambda_chunks[c] * v.reduce();
            }
            out
        };
        let one_hot = parallel::map_reduce(n, || [F192::ZERO; N_ACC], chunk_table, xor_acc);

        // The chunk products, a tuple's pairs at a time.
        let row = |acc: &mut RoundAcc, x: usize| {
            for k in 0..pairs {
                let e = eqr[x + k * step];
                for (j, &(array, lambda, live)) in table.reads.iter().enumerate() {
                    let mut lines = [(F192::ZERO, F192::ZERO); N_CHUNKS];
                    for (i, line) in lines[..live].iter_mut().enumerate() {
                        let tuple = self.idx[x * n + N_CHUNKS * j + i] as usize >> (2 * k * width);
                        let tab = &self.at_chunk[array][i];
                        let lo = tab[tuple & mask];
                        *line = (lo, lo + tab[(tuple >> width) & mask]);
                    }
                    let scale = e * lambda;
                    lines[0] = (scale * lines[0].0, scale * lines[0].1);
                    add_line_product(&lines[..live], &mut acc.0);
                }
            }
        };
        let products = if step >= CYCLE_PAR_THRESHOLD {
            parallel::fold_reduce(step, || ROUND_ZERO, row, xor_round)
        } else {
            let mut acc = ROUND_ZERO;
            (0..step).for_each(|x| row(&mut acc, x));
            acc
        };
        xor_acc(one_hot, finish_round(products))
    }

    /// Bind the round's variable in every eq table; after the last lookup round,
    /// the columns that remain.
    fn fold(&mut self, table: &CycleTable, r: F192) -> Option<Vec<Vec<F192>>> {
        for tab in self.at_chunk.iter_mut().flatten() {
            *tab = fold_pairs(tab, r);
        }
        self.at_r_hot = fold_pairs(&self.at_r_hot, r);
        self.at_r_hot_bar = fold_pairs(&self.at_r_hot_bar, r);
        self.round += 1;
        if self.round < self.depth {
            return None;
        }
        let n = self.n_chunk_tables;
        let step = self.idx.len() / n;
        let idx = |x: usize, c: usize| self.idx[x * n + c] as usize;
        Some(parallel::map_collect(3 * n, |col| {
            let c = col % n;
            if !table.is_live(c) {
                return Vec::new();
            }
            let (array, lambda, _) = table.reads[c / N_CHUNKS];
            let (tab, scale) = match (col / n, c % N_CHUNKS) {
                (0, 0) => (&self.at_chunk[array][0], lambda),
                (0, i) => (&self.at_chunk[array][i], F192::ONE),
                (1, _) => (&self.at_r_hot, F192::ONE),
                _ => (&self.at_r_hot_bar, table.lambda_chunks[c]),
            };
            let scaled: Vec<F192> = tab.iter().map(|&v| scale * v).collect();
            (0..step).map(|x| scaled[idx(x, c)]).collect()
        }))
    }
}

impl CycleTable {
    /// The round polynomial's cofactor `Σ_x eq(x)·p(x, Y)`, as coefficients. `eqr` is
    /// the round's eq table and `zeta_below` the eq point's next coordinate down.
    fn message(&mut self, half: usize, eqr: &[F192], zeta_below: F192) -> [F192; DEGREE + 1] {
        if let Cols::Lookup(lookup) = &self.cols
            && lookup.round == 0
        {
            let hist = lookup.build_hist(self, eqr);
            if let Cols::Lookup(lookup) = &mut self.cols {
                lookup.hist = hist;
            }
        }
        let acc = match &self.cols {
            Cols::Lookup(lookup) => lookup.accumulate(self, eqr, zeta_below),
            Cols::Dense(cols) => self.accumulate(cols, half, eqr),
        };
        let mut coeffs = [F192::ZERO; DEGREE + 1];
        coeffs[..=N_CHUNKS].copy_from_slice(&acc[..=N_CHUNKS]);
        for k in 0..3 {
            coeffs[k] += acc[N_CHUNKS + 1 + k];
        }
        // `eqr` sums to one, and a chunk table left out is `c_hot` on every row.
        coeffs[0] += self.dead;
        coeffs
    }

    fn accumulate(&self, cols: &[Vec<F192>], half: usize, eqr: &[F192]) -> [F192; N_ACC] {
        let n = self.lambda_chunks.len();
        let row = |(products, acc): &mut RoundAcc, x: usize| {
            let line = |col: usize| {
                let lo = cols[col][x];
                (lo, lo + cols[col][x + half])
            };
            let e = eqr[x];
            for (j, &(_, _, live)) in self.reads.iter().enumerate() {
                let mut lines = [(F192::ZERO, F192::ZERO); N_CHUNKS];
                for (i, slot) in lines[..live].iter_mut().enumerate() {
                    *slot = line(N_CHUNKS * j + i);
                }
                lines[0] = (e * lines[0].0, e * lines[0].1);
                add_line_product(&lines[..live], products);
            }
            // `(a + bY)·(c + dY)`, the middle coefficient by Karatsuba, fixed up once.
            let mut one_hot = [F192Unreduced::ZERO; 3];
            for c in (0..n).filter(|&c| self.is_live(c)) {
                let ((a, b), (c, d)) = (line(n + c), line(2 * n + c));
                one_hot[0] ^= a.mul_unreduced(c);
                one_hot[1] ^= (a + b).mul_unreduced(c + d);
                one_hot[2] ^= b.mul_unreduced(d);
            }
            one_hot[1] ^= one_hot[0] ^ one_hot[2];
            for (slot, v) in acc[N_CHUNKS + 1..].iter_mut().zip(one_hot) {
                *slot += e * v.reduce();
            }
        };
        finish_round(if half >= CYCLE_PAR_THRESHOLD {
            parallel::fold_reduce(half, || ROUND_ZERO, row, xor_round)
        } else {
            let mut acc = ROUND_ZERO;
            (0..half).for_each(|x| row(&mut acc, x));
            acc
        })
    }

    fn fold(&mut self, r: F192) {
        match &mut self.cols {
            Cols::Dense(cols) => {
                let view = parallel::Chunks::new(cols, 1);
                parallel::for_each(view.count(), |col| {
                    // SAFETY: column `col` is folded by exactly one task.
                    let column = unsafe { &mut view.get(col)[0] };
                    if !column.is_empty() {
                        fold_high_inplace(column, r);
                    }
                });
            }
            Cols::Lookup(_) => {
                let Cols::Lookup(mut lookup) = std::mem::replace(&mut self.cols, Cols::Dense(Vec::new())) else {
                    unreachable!()
                };
                self.cols = match lookup.fold(self, r) {
                    Some(dense) => Cols::Dense(dense),
                    None => Cols::Lookup(lookup),
                };
            }
        }
    }
}

/// Prove the reads' chunk tables against read-checking's `ra` claims and one-hot,
/// and reduce every opening this takes to ONE ring-switched claim on the committed
/// stack.
pub fn prove_cycles(
    shape: &Shape,
    wit: &Witness<'_>,
    zeta: &[F192],
    reads: &Reads,
    ps: &mut ProverState,
) -> RingSwitchClaim {
    let setup = CycleSetup::sample(shape, reads, ps);
    let m = shape.chunk_bits;
    let eq_r_hot = eq_table(&setup.r_hot);
    let eq_r_hot_bar = eq_table(&setup.r_hot_bar);
    let eq_chunks: [Vec<Vec<F192>>; 2] = [0, 1].map(|a| setup.chunk_points[a].iter().map(|p| eq_table(p)).collect());
    let array_of = |t: usize, c: usize| shape.reads[t][c / N_CHUNKS].array as usize;

    let mut tables: Vec<CycleTable> = (0..N_TABLES)
        .map(|t| {
            let n = shape.n_chunk_tables(t);
            let mut table = CycleTable {
                dead: F192::ZERO,
                reads: (0..shape.reads[t].len())
                    .map(|j| {
                        let array = shape.reads[t][j].array as usize;
                        let live = shape.log_size[array].div_ceil(shape.chunk_bits).clamp(1, N_CHUNKS);
                        (array, setup.read_weight(t, j), live)
                    })
                    .collect(),
                lambda_chunks: (0..n).map(|c| setup.chunk_weight(t, c)).collect(),
                cols: Cols::Dense(Vec::new()),
            };
            let dead = (0..n).filter(|&c| !table.is_live(c));
            table.dead = setup.c_hot * dead.fold(F192::ZERO, |acc, c| acc + table.lambda_chunks[c]);
            table.cols = Cols::Lookup(Lookup::new(shape, &wit.addrs[t], n, &setup));
            table
        })
        .collect();

    // The back-loaded batch of `crate::constraints`, at a higher degree: table `t`
    // joins at round `n − τ_t`, and the tables still waiting ride a line.
    let n = shape.taus.iter().copied().max().unwrap_or(0);
    let sigma: Vec<F192> = (0..N_TABLES).map(|t| setup.sigma(shape, reads, t)).collect();
    let mut claim = sigma.iter().fold(F192::ZERO, |a, &b| a + b);
    let mut weights = [F192::ONE; N_TABLES];
    let mut eqr = eq_table(&zeta[..n.saturating_sub(1)]);
    let mut chi_cyc = vec![F192::ZERO; n];
    let mut k = F192::ONE;
    crate::stage!("Cycle sumcheck", || {
        for mvar in (0..n).rev() {
            let half = 1usize << mvar;
            let waiting = (0..N_TABLES)
                .filter(|&t| shape.taus[t] <= mvar)
                .fold(F192::ZERO, |acc, t| acc + sigma[t]);
            let mut p = [F192::ZERO; DEGREE + 1];
            let zeta_below = if mvar > 0 { zeta[mvar - 1] } else { F192::ZERO };
            for (t, table) in tables.iter_mut().enumerate() {
                if shape.taus[t] > mvar {
                    for (acc, c) in p.iter_mut().zip(table.message(half, &eqr, zeta_below)) {
                        *acc += weights[t] * c;
                    }
                }
            }
            shrink_eq_high(&mut eqr);
            // `h(Y) = eq(ζ_m, Y)·p(Y) + Y·k·waiting`.
            let eq_z = F192::ONE + zeta[mvar];
            let mut h = [F192::ZERO; CYCLE_COEFFS];
            for (d, &c) in p.iter().enumerate() {
                h[d] += eq_z * c;
                h[d + 1] += c;
            }
            h[1] += k * waiting;
            debug_assert_eq!(h[1..].iter().fold(F192::ZERO, |a, &b| a + b), claim);
            ps.add_round_poly(&h, false);
            let rk = ps.sample();
            claim = poly_eval(&h, rk);
            chi_cyc[mvar] = rk;
            k *= rk;
            let eq_k = F192::ONE + zeta[mvar] + rk;
            for (t, table) in tables.iter_mut().enumerate() {
                if shape.taus[t] > mvar {
                    weights[t] *= eq_k;
                    table.fold(rk);
                } else {
                    weights[t] *= rk;
                }
            }
        }
    });

    drop(tables);

    // `T_t(u, c)`: chunk table `c` of table `t` at the cycle point, as a function of
    // the position. Everything from here on reads the chunk tables through it.
    let cubes: Vec<Vec<F192>> = (0..N_TABLES)
        .map(|t| {
            let eq_x = eq_table(&chi_cyc[..shape.taus[t]]);
            let addrs = &wit.addrs[t];
            let n_ct = shape.n_chunk_tables(t);
            // One pass over the rows, a worker's cube being a few cache lines.
            let add = |cube: &mut Vec<F192>, x: usize| {
                for c in 0..n_ct {
                    cube[(c << m) + shape.chunk(addrs[x][c / N_CHUNKS], c % N_CHUNKS)] += eq_x[x];
                }
            };
            parallel::fold_reduce(addrs.len(), || vec![F192::ZERO; n_ct << m], add, xor_slices)
        })
        .collect();
    let at = |t: usize, c: usize, tab: &[F192]| -> F192 {
        cubes[t][c << m..(c + 1) << m]
            .iter()
            .zip(tab)
            .fold(F192::ZERO, |acc, (&v, &w)| acc + v * w)
    };

    // ---- the selector rounds ----
    // What is left is a sum over the chunk tables, weighted by `eq(r_sel, ·)`: the
    // same sumcheck goes on over the selector cube, every table's chunk tables
    // extended by zeros to its size, and ends on `N_CHUNKS + 2` values a table
    // rather than two per chunk table. Column `i` of a table is its reads' chunk
    // `i` at its chunk point, constant across the chunk bits.
    let sel_bits = shape.sel_bits();
    let mut eq_sel = setup.eq_sel.clone();
    let mut chunk0: Vec<F192> = (0..1usize << sel_bits)
        .map(|s| if s % N_CHUNKS == 0 { F192::ONE } else { F192::ZERO })
        .collect();
    let mut sel_cols: Vec<Vec<Vec<F192>>> = (0..N_TABLES)
        .map(|t| {
            let n_ct = shape.n_chunk_tables(t);
            let col = |f: &dyn Fn(usize) -> F192| -> Vec<F192> {
                (0..1usize << sel_bits)
                    .map(|s| if s < n_ct { f(s) } else { F192::ZERO })
                    .collect()
            };
            let mut cols: Vec<Vec<F192>> = (0..N_CHUNKS)
                .map(|i| col(&|s| at(t, s - s % N_CHUNKS + i, &eq_chunks[array_of(t, s)][i])))
                .collect();
            cols.push(col(&|s| at(t, s, &eq_r_hot)));
            cols.push(col(&|s| at(t, s, &eq_r_hot_bar)));
            cols
        })
        .collect();
    let mut chi_sel = vec![F192::ZERO; sel_bits];
    for var in (0..sel_bits).rev() {
        let half = 1usize << var;
        let mut ys = [F192::ZERO; CYCLE_COEFFS];
        for (q, y) in ys.iter_mut().enumerate() {
            let at_q = |tab: &[F192], s: usize| tab[s] + (tab[s] + tab[s + half]).mul_base(F64(q as u64));
            for s in 0..half {
                let inner = (0..N_TABLES).fold(F192::ZERO, |acc, t| {
                    let v: Vec<F192> = sel_cols[t].iter().map(|col| at_q(col, s)).collect();
                    let summand = setup.summand(t, at_q(&chunk0, s), &v[..N_CHUNKS], v[N_CHUNKS], v[N_CHUNKS + 1]);
                    acc + weights[t] * summand
                });
                *y += at_q(&eq_sel, s) * inner;
            }
        }
        let h = interpolate(&ys);
        debug_assert_eq!(h[1..].iter().fold(F192::ZERO, |a, &b| a + b), claim);
        ps.add_round_poly(&h, false);
        let r = ps.sample();
        claim = poly_eval(&h, r);
        chi_sel[var] = r;
        fold_high_inplace(&mut eq_sel, r);
        fold_high_inplace(&mut chunk0, r);
        sel_cols.iter_mut().flatten().for_each(|col| fold_high_inplace(col, r));
    }
    let finals: Vec<Vec<F192>> = sel_cols
        .iter()
        .map(|cols| cols.iter().map(|col| col[0]).collect())
        .collect();
    for values in &finals {
        ps.add_scalars(values);
    }

    // ---- one opening per table ----
    // Every value above is `T_t` against a weight over its chunk cube. A sumcheck
    // over the cube batches them into one evaluation of `T_t`.
    let lambda_cube = powers(ps.sample(), (N_CHUNKS + 2) * N_TABLES);
    let opening = OpeningWeights::new(&lambda_cube, &chi_sel);
    let n_max = (0..N_TABLES).map(|t| shape.cube_bits(t)).max().unwrap();
    let claim = opening.target(&finals);
    let mut pairs: Vec<(Vec<F192>, Vec<F192>)> = (0..N_TABLES)
        .map(|t| {
            let mut weight = vec![F192::ZERO; 1 << n_max];
            for c in 0..shape.n_chunk_tables(t) {
                let [w_f, w_g, w_h] = opening.of(t, c);
                let at_chunk = &eq_chunks[array_of(t, c)][c % N_CHUNKS];
                for u in 0..1 << m {
                    weight[(c << m) + u] = w_f * at_chunk[u] + w_g * eq_r_hot[u] + w_h * eq_r_hot_bar[u];
                }
            }
            let mut cube = cubes[t].clone();
            cube.resize(1 << n_max, F192::ZERO);
            (weight, cube)
        })
        .collect();
    let chi_cube = prove_products(&mut pairs, claim, ps);
    let cube_evals: Vec<F192> = (0..N_TABLES)
        .map(|t| {
            let bits = shape.cube_bits(t);
            let mut cube = cubes[t].clone();
            cube.resize(1 << bits, F192::ZERO);
            mle_eval_e(&cube, &chi_cube[..bits])
        })
        .collect();
    ps.add_scalars(&cube_evals);

    // ---- one ring-switched claim for all tables ----
    // Table `t`'s packed bits at `(chi_cyc, chi_cube)`. Their packing prefix is the
    // cycle point's low coordinates for every table, so the claims share their 64
    // slices once each is scaled into the weight.
    let lambda_hot = powers(ps.sample(), N_TABLES);
    let zero = || vec![F192::ZERO; 1 << LOG_PACKING];
    let slices = (0..N_TABLES)
        .map(|t| {
            let n_ct = shape.n_chunk_tables(t);
            let eq_cube = eq_table(&chi_cube[..shape.cube_bits(t)]);
            let eq_hi: Vec<F192> = eq_table(&chi_cyc[LOG_PACKING..shape.taus[t]])
                .iter()
                .map(|&e| lambda_hot[t] * e)
                .collect();
            let addrs = &wit.addrs[t];
            parallel::fold_reduce(
                eq_hi.len(),
                zero,
                |acc, y| {
                    for (b, slot) in acc.iter_mut().enumerate() {
                        let row = &addrs[(y << LOG_PACKING) + b];
                        let hot = (0..n_ct).fold(F192::ZERO, |acc, c| {
                            acc + eq_cube[(c << m) + shape.chunk(row[c / N_CHUNKS], c % N_CHUNKS)]
                        });
                        *slot += eq_hi[y] * hot;
                    }
                },
                xor_slices,
            )
        })
        .reduce(xor_slices)
        .unwrap();
    ps.add_scalars(&slices);
    ring_claim(shape, &chi_cyc, &chi_cube, &lambda_hot, slices)
}

fn xor_slices(mut a: Vec<F192>, b: Vec<F192>) -> Vec<F192> {
    for (x, y) in a.iter_mut().zip(b) {
        *x += y;
    }
    a
}

/// The opening sumcheck's batching: a table's `N_CHUNKS + 2` values from the
/// selector rounds are its chunk cube against these weights, value `k` of table
/// `t` taking the power `(N_CHUNKS + 2)·t + k` of `λ_cube`.
struct OpeningWeights<'a> {
    lambda_cube: &'a [F192],
    /// `eq` of the selector point against a chunk table's index, and against its read's.
    eq_table: Vec<F192>,
    eq_read: Vec<F192>,
}

impl<'a> OpeningWeights<'a> {
    fn new(lambda_cube: &'a [F192], chi_sel: &[F192]) -> Self {
        Self {
            lambda_cube,
            eq_table: eq_table(chi_sel),
            eq_read: eq_table(&chi_sel[LOG_N_CHUNKS..]),
        }
    }

    /// What the batch claims to sum to.
    fn target(&self, finals: &[Vec<F192>]) -> F192 {
        finals
            .iter()
            .flatten()
            .zip(self.lambda_cube)
            .fold(F192::ZERO, |acc, (&v, &w)| acc + w * v)
    }

    /// The weights of chunk table `c` of table `t`: of its evaluation at its chunk
    /// point, at `r_hot` and at `1 + r_hot`.
    fn of(&self, t: usize, c: usize) -> [F192; 3] {
        let power = |k: usize| self.lambda_cube[(N_CHUNKS + 2) * t + k];
        [
            power(c % N_CHUNKS) * self.eq_read[c / N_CHUNKS],
            power(N_CHUNKS) * self.eq_table[c],
            power(N_CHUNKS + 1) * self.eq_table[c],
        ]
    }
}

/// The one claim binding every table's packed one-hot bits: table `t`'s at
/// `(chi_cyc, chi_cube)`, scaled by `λ_hot^t`. A packed word is indexed by position,
/// then row above the packing prefix, then chunk table.
fn ring_claim(
    shape: &Shape,
    chi_cyc: &[F192],
    chi_cube: &[F192],
    scales: &[F192],
    slices: Vec<F192>,
) -> RingSwitchClaim {
    let (pos, sel) = chi_cube.split_at(shape.chunk_bits);
    RingSwitchClaim {
        parts: (0..N_TABLES)
            .map(|t| RingSwitchPart {
                offset: shape.hot_offsets[t],
                suffix_point: [
                    pos,
                    &chi_cyc[LOG_PACKING..shape.taus[t]],
                    &sel[..shape.cube_bits(t) - shape.chunk_bits],
                ]
                .concat(),
                scale: scales[t],
            })
            .collect(),
        s_hat_v: Some(slices),
    }
}

/// Verifier of [`prove_cycles`]: the ring-switched claim left for the opening.
pub fn verify_cycles(
    shape: &Shape,
    zeta: &[F192],
    reads: &Reads,
    vs: &mut VerifierState,
) -> Result<RingSwitchClaim, Error> {
    let setup = CycleSetup::sample(shape, reads, vs);
    let m = shape.chunk_bits;
    let n = shape.taus.iter().copied().max().unwrap_or(0);
    let target = (0..N_TABLES).fold(F192::ZERO, |acc, t| acc + setup.sigma(shape, reads, t));
    let (chi_cyc, claim) = verify_rounds(n, CYCLE_COEFFS, target, vs)?;
    // The selector rounds: the same sumcheck, on over the chunk tables.
    let (chi_sel, claim) = verify_rounds(shape.sel_bits(), CYCLE_COEFFS, claim, vs)?;

    // Each table's weight, as `crate::constraints::verify` forms it: the eq factor
    // over its own variables, times the challenges it sat out.
    let chunk0 = chi_sel[..LOG_N_CHUNKS]
        .iter()
        .fold(F192::ONE, |acc, &r| acc * (F192::ONE + r));
    let mut finals: Vec<Vec<F192>> = Vec::with_capacity(N_TABLES);
    let mut acc = F192::ZERO;
    for t in 0..N_TABLES {
        let tau = shape.taus[t];
        let weight = chi_cyc[tau..]
            .iter()
            .fold(eq_eval(&zeta[..tau], &chi_cyc[..tau]), |acc, &r| acc * r);
        let v = vs.next_scalars(N_CHUNKS + 2).map_err(|_| Error::Truncated)?;
        acc += weight * setup.summand(t, chunk0, &v[..N_CHUNKS], v[N_CHUNKS], v[N_CHUNKS + 1]);
        finals.push(v);
    }
    if eq_eval(&setup.r_sel, &chi_sel) * acc != claim {
        return Err(Error::Cycle);
    }

    let lambda_cube = powers(vs.sample(), (N_CHUNKS + 2) * N_TABLES);
    let opening = OpeningWeights::new(&lambda_cube, &chi_sel);
    let n_max = (0..N_TABLES).map(|t| shape.cube_bits(t)).max().unwrap();
    let target = opening.target(&finals);
    let (chi_cube, claim) = verify_rounds(n_max, 3, target, vs)?;
    let cube_evals = vs.next_scalars(N_TABLES).map_err(|_| Error::Truncated)?;
    let (pos, sel) = chi_cube.split_at(m);
    let at_r_hot = eq_eval(&setup.r_hot, pos);
    let at_r_hot_bar = eq_eval(&setup.r_hot_bar, pos);
    let at_chunk: [Vec<F192>; 2] = [0, 1].map(|a| setup.chunk_points[a].iter().map(|p| eq_eval(p, pos)).collect());
    let mut acc = F192::ZERO;
    for t in 0..N_TABLES {
        let bits = shape.cube_bits(t) - m;
        // A table's cube is zero past its own variables.
        let pad = sel[bits..].iter().fold(F192::ONE, |acc, &r| acc * (F192::ONE + r));
        let eq_sel = eq_table(&sel[..bits]);
        let mut weight = F192::ZERO;
        for c in 0..shape.n_chunk_tables(t) {
            let [w_f, w_g, w_h] = opening.of(t, c);
            let a = shape.reads[t][c / N_CHUNKS].array as usize;
            weight += eq_sel[c] * (w_f * at_chunk[a][c % N_CHUNKS] + w_g * at_r_hot + w_h * at_r_hot_bar);
        }
        acc += pad.square() * weight * cube_evals[t];
    }
    if acc != claim {
        return Err(Error::Opening);
    }

    let lambda_hot = powers(vs.sample(), N_TABLES);
    let slices = vs.next_scalars(1 << LOG_PACKING).map_err(|_| Error::Truncated)?;
    let prefix = eq_table(&chi_cyc[..LOG_PACKING]);
    let bound = prefix.iter().zip(&slices).fold(F192::ZERO, |acc, (&e, &s)| acc + e * s);
    if bound != (0..N_TABLES).fold(F192::ZERO, |acc, t| acc + lambda_hot[t] * cube_evals[t]) {
        return Err(Error::Slices);
    }
    Ok(ring_claim(shape, &chi_cyc, &chi_cube, &lambda_hot, slices))
}

#[cfg(test)]
mod tests {
    use super::*;

    fn e(i: u64) -> F192 {
        F192::new(0x9e37_79b9_7f4a_7c15 ^ i, 0x1234_5678_9abc_def0 + i, 7 * i + 3)
    }

    /// A chunk row passes the one-hot test exactly when it holds one `1`.
    #[test]
    fn one_hot_test_counts_ones() {
        // Not `e(0..4)`, whose sum is zero: a root of the test for a parity row.
        let r: Vec<F192> = (0..4).map(|i| e(3 * i * i + 1)).collect();
        let (flipped, product) = one_hot_point(&r);
        let (at_r, at_flipped) = (eq_table(&r), eq_table(&flipped));
        for row in 0u32..1 << 16 {
            let hot = (0..16).filter(|u| row >> u & 1 == 1);
            let (a, b) = hot.fold((F192::ZERO, F192::ZERO), |(a, b), u| (a + at_r[u], b + at_flipped[u]));
            assert_eq!(a * b == product, row.count_ones() == 1, "row {row:b}");
        }
    }
}
