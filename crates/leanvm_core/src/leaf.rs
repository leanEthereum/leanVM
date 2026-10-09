//! The bus: a single shared channel balanced by a grand product (§sec:gp through §sec:leafstack). Each
//! interaction wires a table's columns into width-`m` tuples and flushes them in a
//! direction; the bus balances when pushed and pulled tuples form the same
//! multiset, proven by two GKR passes over the leaf vectors `β − π_α(σ)`. Each pass
//! reduces to a leaf claim `Ṽ₀(ζ)`, which the table sumcheck settles. The one
//! interaction left on it is the VM state (§sec:state): the memory and bytecode
//! lookups are [`crate::shout`]'s. Tuple coordinates `σ_i` are `K`-valued; the
//! fingerprint challenges `α, β` are `E`-valued, so a leaf accumulates via the
//! mixed `mul_base` product (2 PMULL per coordinate).

use crate::PAR_THRESHOLD;
use crate::colval::ColVal;
use crate::gkr;
use crate::transcript::{Challenger, ProverState, VerifierState};
use primitives::field::{F64, F192, F192Unreduced, g_pow};
use primitives::multilinear::{eq_eval, eq_table};

/// One tuple coordinate as a function of the block's row `z`.
#[derive(Clone, Debug)]
pub enum Coord {
    /// A public constant (an opcode, a boundary state).
    Const(F64),
    /// A committed column, value `col[z]`.
    Col(usize),
    /// The free increment `g^k · col[z]` (a virtual column, §sec:vm): the state step.
    GCol(usize, u32),
    /// The product `g^k · col_a[z] · col_b[z]` of two committed columns. An address
    /// is `fp·g^o`, so a read carries one without committing it: the
    /// coordinate IS the product, so no column can disagree with it and the binding
    /// constraint that used to say so is unnecessary (§sec:m3).
    Prod(usize, usize, u32),
    /// A sum of `Const`/`Col`/`GCol`/`Prod` terms: any degree-2 form over the
    /// table's columns, which is all §sec:m3 asks of a coordinate. This is what
    /// carries a value a row DERIVES from its columns (an `XOR`/`MUL` result, a
    /// `DEREF` store, a `JUMP` successor) without committing a column for it, and
    /// with it the identity that would have tied the two.
    Sum(Vec<Coord>),
}

/// A flushing rule: `2^kappa` rows, each a tuple of coordinates. Every one of them is a
/// row the program executed, since a table's height is its row count (§sec:e2e-pad), so a
/// block has no padding rows to divide back out of the product.
#[derive(Clone, Debug)]
pub struct Block {
    pub kappa: usize,
    pub coords: Vec<Coord>,
}

/// Placement of each block in the stacked leaf vector (input order).
#[derive(Clone, Debug)]
pub struct Layout {
    pub mu: usize,
    pub offsets: Vec<usize>,
}

/// An evaluation claim on a committed column, settled against the witness.
/// Reconstructed identically by both sides (its value rides the stream).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ColumnClaim {
    pub col: usize,
    pub point: Vec<F192>,
    pub value: F192,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Error {
    Gkr(gkr::GkrError),
}

/// The fingerprint weights `eq(α⃗, x)` over the `2^N_TUPLE_BITS` slots (§sec:gp).
/// A tuple is fingerprinted as `Σ_x eq(α⃗, x)·σ_x`, a MULTILINEAR combination
/// rather than a power chain: each leaf factor is then of total degree
/// `N_TUPLE_BITS` in the challenges instead of the tuple width, and slot `x`'s
/// weight is an `eq` weight, which is what lets a bytecode read's entry be the
/// aligned bytecode polynomial at `α⃗` itself (§sec:e2e-bc).
pub fn fingerprint_weights(alphas: &[F192]) -> Vec<F192> {
    debug_assert_eq!(alphas.len(), N_TUPLE_BITS);
    let mut w = vec![F192::ONE; 1 << N_TUPLE_BITS];
    for (bit, &a) in alphas.iter().enumerate() {
        for (x, wx) in w.iter_mut().enumerate() {
            *wx *= if (x >> bit) & 1 == 1 { a } else { a + F192::ONE };
        }
    }
    w
}

/// Bits indexing a tuple's coordinates, on the bus and in a read: the `m = 11`
/// coordinates of a bytecode read live in the `2^4` slots of the bytecode
/// encoding (§sec:m3, §sec:e2e-bc).
pub const N_TUPLE_BITS: usize = 4;

/// Conservative sum of the degree bounds for every random-challenge failure in
/// the bus argument. A side contains at most `2^mu` leaf factors, each of total
/// degree `N_TUPLE_BITS` in `α⃗` and one in `β`. The second term covers all
/// radix-four GKR batching and sumcheck challenges.
fn soundness_degree_bound(mu: usize) -> u128 {
    assert!(mu < u128::BITS as usize, "bus layout is too large to bound");
    let fingerprint = (N_TUPLE_BITS as u128 + 1) * (1u128 << mu);
    let gkr = 8u128 * (mu as u128 + 1).pow(2);
    fingerprint + gkr
}

fn soundness_bits(mu: usize) -> u32 {
    let degree = soundness_degree_bound(mu);
    192u32.saturating_sub(u128::BITS - degree.leading_zeros())
}

/// Check that the 192-bit challenge field supplies the target bus soundness.
fn assert_grinding_unnecessary(push_blocks: &[Block], pull_blocks: &[Block], push: &Layout, pull: &Layout) {
    assert_eq!(
        push.mu, pull.mu,
        "push/pull bus blocks are paired, so their layouts match"
    );
    let widest = push_blocks
        .iter()
        .chain(pull_blocks)
        .map(|block| block.coords.len())
        .max()
        .unwrap_or(0);
    assert!(widest <= 1 << N_TUPLE_BITS, "a tuple's coordinates index its slots");
    assert!(
        soundness_bits(push.mu) >= crate::SECURITY_BITS,
        "bus layout exceeds the unground F192 soundness budget"
    );
}

/// Stack blocks largest-first at aligned offsets; `μ = ⌈log2 Σ 2^{κ_b}⌉`.
pub fn layout(blocks: &[Block]) -> Layout {
    let kappas: Vec<Option<usize>> = blocks.iter().map(|b| Some(b.kappa)).collect();
    let (offsets, placed) = crate::witness::stack_offsets(&kappas);
    Layout {
        mu: crate::log2_ceil_usize(placed.max(1)),
        offsets,
    }
}

/// A non-constant coordinate as `(source, coefficient)`: its leaf contribution is
/// the mixed product `coeff · source(z)` with `source(z) ∈ K`, `coeff ∈ E`.
/// `GCol` folds the `g^k` factor into the coefficient.
enum Term {
    Col(usize, F192),
    Prod(usize, usize, F192),
}

/// Flatten one coordinate into leaf terms at coefficient `w`. A [`Coord::Sum`]
/// spreads its children over the SAME `w`: they are one coordinate, so they share
/// its `α`-power.
fn push_terms(c: &Coord, w: F192, terms: &mut Vec<Term>, constant: &mut F192) {
    match c {
        Coord::Const(v) => *constant += w.mul_base(*v),
        Coord::Col(i) => terms.push(Term::Col(*i, w)),
        Coord::GCol(i, k) => terms.push(Term::Col(*i, w.mul_base(g_pow(*k as usize)))),
        Coord::Prod(i, j, k) => terms.push(Term::Prod(*i, *j, w.mul_base(g_pow(*k as usize)))),
        Coord::Sum(cs) => {
            for c in cs {
                push_terms(c, w, terms, constant);
            }
        }
    }
}

/// Build one side's leaf vector: block `b` row `z` holds `β − Σ_i w_i c_i(z)` for
/// the fingerprint weights `w = eq(α⃗, ·)`, followed implicitly by the identity `1`
/// up to `2^μ`. The row-invariant weights and constant coordinates are folded once
/// per block into `const_part`.
pub fn build_leaves(blocks: &[Block], lay: &Layout, cols: &[&[F64]], w: &[F192], beta: F192) -> Vec<F192> {
    let explicit = blocks
        .iter()
        .enumerate()
        .map(|(b, block)| lay.offsets[b] + (1usize << block.kappa))
        .max()
        .unwrap_or(1);
    debug_assert!(explicit <= 1usize << lay.mu);
    // `stack_offsets` packs the power-of-two blocks contiguously from zero, so the
    // blocks tile `0..explicit` and every slot below is written by one of them: the
    // identity fill would be overwritten in full, and this is the largest buffer in
    // the proof. The `covered` test is what licenses skipping it, so a layout that
    // ever left a hole falls back to filling rather than reading uninitialized rows.
    // Capacity is rounded to whole four-tuples because `gkr::QuaternaryLayerState`
    // pads this level to that before reading it, and growing it here would copy it.
    let covered: usize = blocks.iter().map(|blk| 1usize << blk.kappa).sum();
    let capacity = explicit.next_multiple_of(4);
    let mut leaves = if covered == explicit {
        // SAFETY: the per-block fills below cover `0..explicit` exactly, and each
        // joins before this function returns.
        let mut values = unsafe { primitives::uninit_vec(capacity) };
        values.truncate(explicit);
        values
    } else {
        let mut values = Vec::with_capacity(capacity);
        values.resize(explicit, F192::ONE);
        values
    };
    for (b, blk) in blocks.iter().enumerate() {
        let mut const_part = beta;
        let mut terms: Vec<Term> = Vec::with_capacity(blk.coords.len());
        for (i, c) in blk.coords.iter().enumerate() {
            push_terms(c, w[i], &mut terms, &mut const_part);
        }
        let row = |z: usize| -> F192 {
            // The α-weighted coordinate sum defers its reductions: each mixed
            // product contributes its three raw limb products (3 PMULL, no
            // reduction tail), one combined reduction per row at the end,
            // bit-identical to summing reduced `mul_base` terms.
            let mut acc = F192Unreduced::ZERO;
            for t in &terms {
                acc ^= match t {
                    Term::Col(i, c) => c.mul_base_unreduced(cols[*i][z]),
                    Term::Prod(i, j, c) => c.mul_base_unreduced(cols[*i][z] * cols[*j][z]),
                };
            }
            const_part + acc.reduce()
        };
        let off = lay.offsets[b];
        // Every row of every block is a real row: a table's height is exactly the
        // number of rows it executed (`cpu::filler`), so no block has padding rows
        // whose tuples would have to be divided back out of the product.
        let dst = &mut leaves[off..off + (1usize << blk.kappa)];
        if dst.len() >= PAR_THRESHOLD {
            parallel::fill(dst, row);
        } else {
            for (z, slot) in dst.iter_mut().enumerate() {
                *slot = row(z);
            }
        }
    }
    leaves
}

/// One table's contribution to one side of the bus, or its reads' fingerprints
/// ([`crate::shout`]), as a form over that table's committed columns:
/// `Σ_c coeffs[c]·col_c(z) + Σ (a,b,c) c·col_a(z)·col_b(z) + constant`.
/// Every coefficient is a public function of the challenges. The table sumcheck
/// sums this against `eq(ζ[..τ], ·)` instead of opening each column at `ζ`.
///
/// The quadratic part comes from [`Coord::Prod`] and is free: the AIR identities are
/// already degree 2, so a degree-2 form does not raise the round-polynomial degree
/// the batch pays for.
#[derive(Clone, Debug)]
pub struct BusForm {
    pub coeffs: Vec<F192>,
    /// `(col_a, col_b, coeff)` in LOCAL column indices.
    pub prods: Vec<(usize, usize, F192)>,
    pub constant: F192,
}

impl BusForm {
    pub(crate) fn new(n_cols: usize) -> Self {
        Self {
            coeffs: vec![F192::ZERO; n_cols],
            prods: Vec::new(),
            constant: F192::ZERO,
        }
    }

    /// The same form scaled by `w`. Every coefficient is `E`-valued already, so
    /// folding the side's `η`-power in here costs three multiplies once per table
    /// instead of one per [`eval`](Self::eval), which the zerocheck calls per row
    /// per round.
    pub fn scaled(&self, w: F192) -> Self {
        Self {
            coeffs: self.coeffs.iter().map(|&c| c * w).collect(),
            prods: self.prods.iter().map(|&(a, b, c)| (a, b, c * w)).collect(),
            constant: self.constant * w,
        }
    }

    /// The pointwise sum of several forms over the same columns.
    ///
    /// Evaluating the sum is evaluating each and adding, and the constraint batch
    /// only ever wants a table's total, so its three forms collapse to one
    /// dot product and one product list: the row loop then reads the column
    /// values once for all three rather than once each.
    pub fn sum(forms: impl IntoIterator<Item = Self>) -> Self {
        let mut forms = forms.into_iter();
        let mut out = forms.next().expect("a table has at least one bus form");
        for form in forms {
            assert_eq!(out.coeffs.len(), form.coeffs.len(), "forms over the same columns");
            for (slot, c) in out.coeffs.iter_mut().zip(form.coeffs) {
                *slot += c;
            }
            out.constant += form.constant;
            for (a, b, c) in form.prods {
                match out.prods.iter_mut().find(|p| (p.0, p.1) == (a, b)) {
                    Some(p) => p.2 += c,
                    None => out.prods.push((a, b, c)),
                }
            }
        }
        out.prods.retain(|p| p.2 != F192::ZERO);
        out
    }

    /// The form at one point, unreduced: `evals` are the columns' values there.
    /// This is what the zerocheck evaluates, per row while a table is unfolded and
    /// at the sumcheck point after, so a table's several forms share one reduction
    /// rather than paying one per term.
    /// `quadratic` selects only degree-two terms, for a sumcheck round coefficient.
    pub fn eval_unreduced<T: ColVal>(&self, evals: &[T], quadratic: bool) -> T::Unreduced {
        self.prods.iter().fold(
            if quadratic {
                T::lift(F192::ZERO)
            } else {
                T::dot_unreduced(&self.coeffs, evals) ^ T::lift(self.constant)
            },
            |acc, &(a, b, c)| acc ^ (evals[a] * evals[b]).mul_e_unreduced(c),
        )
    }

    /// [`eval_unreduced`](Self::eval_unreduced) on its own.
    pub fn eval<T: ColVal>(&self, evals: &[T]) -> F192 {
        T::reduce(self.eval_unreduced(evals, false))
    }

    /// What the form sums to over the table's rows against `eq(ζ, ·)`, the target the
    /// zerocheck settles. The linear part factors through the columns' evaluations at
    /// `ζ`, which is the whole point of a form; a product coordinate does NOT, so
    /// `prod_sums` supplies `Σ_z eq(ζ,z)·col_a(z)·col_b(z)` for each pair it uses.
    fn sum_at(&self, evals: &[F192], prod_sums: &[(usize, usize, F192)]) -> F192 {
        self.prods
            .iter()
            .fold(F192::dot(&self.coeffs, evals, self.constant), |acc, &(a, b, c)| {
                let s = prod_sums
                    .iter()
                    .find(|p| (p.0, p.1) == (a, b))
                    .expect("every pair was summed");
                acc + c * s.2
            })
    }
}

/// Accumulate one coordinate of a table's tuple into that table's form, at
/// coefficient `w`. A [`Coord::Sum`]'s children share `w`, so a derived value
/// lands as the several coefficients and products it is made of. `base` is the
/// table's first global column.
pub(crate) fn accumulate_form(c: &Coord, w: F192, base: usize, form: &mut BusForm) {
    match c {
        Coord::Const(v) => form.constant += w.mul_base(*v),
        Coord::Col(i) => form.coeffs[*i - base] += w,
        Coord::GCol(i, k) => form.coeffs[*i - base] += w.mul_base(g_pow(*k as usize)),
        Coord::Prod(i, j, k) => form.prods.push((*i - base, *j - base, w.mul_base(g_pow(*k as usize)))),
        Coord::Sum(cs) => {
            for c in cs {
                accumulate_form(c, w, base, form);
            }
        }
    }
}

/// Walk one side's blocks. A block owned by table `t` (with column base `base`)
/// accumulates into `forms[t]`; the boundary blocks carry constants alone. Returns
/// the boundary blocks' contribution to `Ṽ₀(ζ)` plus the padding mass, so the
/// caller can settle the side once the table sumcheck has proven the tables' forms.
/// Both sides run this: it reads nothing but the public layout and the challenges.
fn decompose(
    blocks: &[Block],
    lay: &Layout,
    zeta: &[F192],
    w: &[F192],
    beta: F192,
    owners: &[Option<(usize, usize)>],
    forms: &mut [BusForm],
) -> F192 {
    assert_eq!(zeta.len(), lay.mu);
    let mut acc = F192::ZERO;
    let mut sel_sum = F192::ZERO;
    for (b, blk) in blocks.iter().enumerate() {
        let kappa = blk.kappa;
        let sel = lay.offsets[b] >> kappa;
        let sel_bits: Vec<F192> = (0..(lay.mu - kappa))
            .map(|k| F192::new(((sel >> k) & 1) as u64, 0, 0))
            .collect();
        let eq_hi = eq_eval(&sel_bits, &zeta[kappa..]);
        sel_sum += eq_hi;

        if let Some((t, base)) = owners[b] {
            let form = &mut forms[t];
            form.constant += eq_hi * beta;
            for (i, c) in blk.coords.iter().enumerate() {
                accumulate_form(c, eq_hi * w[i], base, form);
            }
            continue;
        }
        let mut inner = F192::ZERO;
        for (i, c) in blk.coords.iter().enumerate() {
            match c {
                Coord::Const(v) => inner += w[i].mul_base(*v),
                _ => unreachable!("a boundary tuple is public"),
            }
        }
        acc += eq_hi * (beta + inner);
    }
    // The padding rows (identity `1`) contribute the leftover mass `1 - Σ_b sel_b`.
    acc + (F192::ONE + sel_sum)
}

/// What the bus hands on, the same on both sides: the fingerprint weights (which
/// the reads share), the shared GKR point (the table sumcheck's eq point), and per
/// side the tables' forms with what they owe.
pub struct Bus {
    /// The fingerprint point `α⃗` and its weights `eq(α⃗, ·)`.
    pub alphas: Vec<F192>,
    pub weights: Vec<F192>,
    /// The GKR point ζ: the table sumcheck reuses it, so no fresh point is sampled.
    pub point: Vec<F192>,
    /// `forms[side][table]`, in `[push, pull]` order.
    pub forms: [Vec<BusForm>; 2],
    /// Per side, what the tables' blocks owe its leaf claim: `Ṽ₀(ζ)` less the
    /// boundary blocks and the padding. DERIVED, never transmitted: a transmitted
    /// total would appear in exactly one check, which it could always be solved to
    /// satisfy. The table sumcheck's target pins it.
    pub totals: [F192; 2],
}

/// Prove the bus balances (§sec:leafstack). `alpha`/`beta` follow the witness
/// commitment (the only ordering the grand product needs), and the block structure
/// is public, so no shape is observed.
pub fn prove_balance(
    push: &[Block],
    pull: &[Block],
    cols: &[&[F64]],
    owners: &[Vec<Option<(usize, usize)>>; 2],
    tables: &[(usize, usize)],
    ps: &mut ProverState,
) -> Bus {
    let lays = [layout(push), layout(pull)];
    assert_grinding_unnecessary(push, pull, &lays[0], &lays[1]);
    let alphas: Vec<F192> = (0..N_TUPLE_BITS).map(|_| ps.sample()).collect();
    let weights = fingerprint_weights(&alphas);
    let beta = ps.sample();
    // Two independent leaf vectors, built one after another: each `build_leaves`
    // already fans its own blocks out across the whole pool.
    let leaves = crate::stage!("Bus leaves", || {
        [
            build_leaves(push, &lays[0], cols, &weights, beta),
            build_leaves(pull, &lays[1], cols, &weights, beta),
        ]
    });
    // Both trees run as ONE RLC-batched GKR, so both claims land on ONE point ζ.
    let bus_gkr = crate::stage!("Bus GKR", || {
        gkr::prove_products(leaves, ps, gkr::RootShape::FirstTwoShared)
    });
    let (forms, totals) = settle([push, pull], &lays, &bus_gkr, &weights, beta, owners, tables);
    Bus {
        alphas,
        weights,
        point: bus_gkr.point,
        forms,
        totals,
    }
}

/// Each side's leaf claim, split into the tables' forms and what they owe it.
fn settle(
    blocks: [&[Block]; 2],
    lays: &[Layout; 2],
    bus_gkr: &gkr::Products<2>,
    weights: &[F192],
    beta: F192,
    owners: &[Vec<Option<(usize, usize)>>; 2],
    tables: &[(usize, usize)],
) -> ([Vec<BusForm>; 2], [F192; 2]) {
    let mut forms = std::array::from_fn(|_| tables.iter().map(|&(_, n)| BusForm::new(n)).collect::<Vec<_>>());
    let totals = std::array::from_fn(|s| {
        let framework = decompose(
            blocks[s],
            &lays[s],
            &bus_gkr.point,
            weights,
            beta,
            &owners[s],
            &mut forms[s],
        );
        framework + bus_gkr.values[s]
    });
    (forms, totals)
}

/// Each form's eq-weighted sum over its table's rows: `sums[side][table]`.
/// Prover-side only, to build the table sumcheck's waiting line each round, which
/// rides inside the round polynomial; none of it travels.
pub(crate) fn form_sums(
    cols: &[&[F64]],
    tables: &[(usize, usize)],
    sides: &[&[BusForm]],
    zeta: &[F192],
) -> Vec<Vec<F192>> {
    let (table_evals, prod_sums) = tables_and_prods_at(cols, tables, sides, zeta);
    sides
        .iter()
        .map(|side| {
            side.iter()
                .zip(&table_evals)
                .zip(&prod_sums)
                .map(|((f, e), p)| f.sum_at(e, p))
                .collect()
        })
        .collect()
}

/// Every table's committed columns at `ζ[..τ_t]`, and, for every column pair its
/// forms multiply, `Σ_z eq(ζ[..τ], z)·col_a(z)·col_b(z)`.
///
/// One eq table per table, streamed once past every column and every pair at
/// the same time. Evaluated apart these are `n_cols + n_pairs` fold ladders
/// over the same table at the same point, and a ladder lifts every `K` word it
/// reads into an `E` it writes and reads again, where a dot against the weights
/// moves the column's own eight bytes. Pairs are deduped across the sides. `tables[t] = (base, n_cols)` in the global
/// schema; a pair names LOCAL column indices.
#[allow(clippy::type_complexity)]
fn tables_and_prods_at(
    cols: &[&[F64]],
    tables: &[(usize, usize)],
    forms: &[&[BusForm]],
    zeta: &[F192],
) -> (Vec<Vec<F192>>, Vec<Vec<(usize, usize, F192)>>) {
    /// Rows per task: the eq slice a task reads stays in L2 while every column
    /// and pair accumulator sweeps past it.
    const ROWS: usize = 1 << 12;

    tables
        .iter()
        .enumerate()
        .map(|(t, &(base, n_cols))| {
            let tau = crate::log2_strict_usize(cols[base].len());
            let mut pairs: Vec<(usize, usize)> = forms
                .iter()
                .flat_map(|side| side[t].prods.iter().map(|&(a, b, _)| (a, b)))
                .collect();
            pairs.sort_unstable();
            pairs.dedup();

            let eq = eq_table(&zeta[..tau]);
            let n_acc = n_cols + pairs.len();
            let sums = parallel::fold_reduce(
                (1usize << tau).div_ceil(ROWS),
                || vec![F192Unreduced::ZERO; n_acc],
                |acc, chunk| {
                    let lo = chunk * ROWS;
                    let weights = &eq[lo..(lo + ROWS).min(1 << tau)];
                    let span = |c: usize| &cols[base + c][lo..lo + weights.len()];
                    for (c, slot) in acc[..n_cols].iter_mut().enumerate() {
                        for (&w, &v) in weights.iter().zip(span(c)) {
                            *slot ^= w.mul_base_unreduced(v);
                        }
                    }
                    for (&(a, b), slot) in pairs.iter().zip(&mut acc[n_cols..]) {
                        for ((&w, &x), &y) in weights.iter().zip(span(a)).zip(span(b)) {
                            *slot ^= w.mul_base_unreduced(x * y);
                        }
                    }
                },
                |mut left, right| {
                    for (slot, part) in left.iter_mut().zip(right) {
                        *slot ^= part;
                    }
                    left
                },
            );
            let evals = sums[..n_cols].iter().map(|s| s.reduce()).collect();
            let prods = pairs
                .iter()
                .zip(&sums[n_cols..])
                .map(|(&(a, b), s)| (a, b, s.reduce()))
                .collect();
            (evals, prods)
        })
        .unzip()
}

/// Verify the bus balances. Every row of every table is a real row (`cpu::filler`),
/// so the two sides balance outright: the GKR sends ONE root for both, so a prover
/// cannot even state an unbalanced bus, and there is nothing to check here beyond
/// the reduction itself.
pub fn verify_balance(
    push: &[Block],
    pull: &[Block],
    owners: &[Vec<Option<(usize, usize)>>; 2],
    tables: &[(usize, usize)],
    vs: &mut VerifierState,
) -> Result<Bus, Error> {
    let lays = [layout(push), layout(pull)];
    assert_grinding_unnecessary(push, pull, &lays[0], &lays[1]);
    let alphas: Vec<F192> = (0..N_TUPLE_BITS).map(|_| vs.sample()).collect();
    let weights = fingerprint_weights(&alphas);
    let beta = vs.sample();
    let bus_gkr = gkr::verify_products(lays[0].mu, vs, gkr::RootShape::FirstTwoShared).map_err(Error::Gkr)?;
    let (forms, totals) = settle([push, pull], &lays, &bus_gkr, &weights, beta, owners, tables);
    Ok(Bus {
        alphas,
        weights,
        point: bus_gkr.point,
        forms,
        totals,
    })
}

#[cfg(test)]
mod tests {
    use super::soundness_bits;

    /// The bound is `(N_TUPLE_BITS + 1)·2^mu` plus the GKR terms: only the bus
    /// DEPTH costs bits now, the multilinear fingerprint having fixed each factor's
    /// degree at four in `α⃗` and one in `β`, whatever the tuple's width.
    #[test]
    fn bus_soundness_tracks_depth_only() {
        assert!(soundness_bits(38) >= crate::SECURITY_BITS);
        assert!(soundness_bits(61) >= crate::SECURITY_BITS);
        assert!(soundness_bits(62) < crate::SECURITY_BITS);
    }
}
