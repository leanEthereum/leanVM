//! A side's leaf claim, decomposed into the tables' forms, the framework blocks' column claims and the producers' weights.

use primitives::{Field, PrimeCharacteristicRing};

use super::{ColumnClaim, Coord, Fingerprint, Openings, Producer, PublicColumn, PublicColumns, Side, SparseColumn};
use crate::colval::ColVal;
#[cfg(all(target_arch = "x86_64", target_feature = "vpclmulqdq", target_feature = "avx512f"))]
use crate::colval::PackedCoeffs;
use fiat_shamir::arith::{Arith, Native};
use fiat_shamir::transcript::{ProverState, Transmitter};
use primitives::multilinear::mle_eval;
use primitives::{F64, F192};
use std::collections::HashSet;
use std::convert::Infallible;
use std::sync::Arc;

/// The producer's public half at `chi`, short of its program columns' share.
///
/// ```text
/// MLE(P_i)(chi) - 1 - D_i   for each bit i,   P_i(x) = beta^(2^i) + sum_s w_s^(2^i) c_s(x)^(2^i)
/// ```
///
/// - `D_i` is the program columns' share, left to a deferred claim.
/// - The Frobenius `a -> a^(2^i)` is additive, so a coordinate's power is as cheap as the coordinate.
/// - A constant stays one, and an integer index column stays affine in the bits.
pub fn producer_affine_evals<A: Arith>(a: &mut A, p: &Producer, w: &[A::E], beta: A::E, chi: &[A::E]) -> Vec<A::E> {
    assert_eq!(chi.len(), p.kappa);
    // Running `2^i`-th powers: the constant, each index coordinate's weight and monomials.
    let mut constant = beta;
    let mut affine: Vec<(A::E, Vec<F64>)> = Vec::new();
    for (c, &weight) in p.coords.iter().zip(w) {
        match c {
            Coord::Const(v) => constant = a.mul_const_add(weight, F192::from(*v), constant),
            Coord::IntIndex { base, shift } => {
                constant = a.mul_const_add(weight, F192::from(*base), constant);
                affine.push((
                    weight,
                    (0..p.kappa).map(|k| F64::new(1 << (k as u32 + shift))).collect(),
                ));
            }
            Coord::Public(_) => {}
            _ => unreachable!("a producer's tuple is public"),
        }
    }
    let mut evals = Vec::with_capacity(p.bits);
    for bit in 0..p.bits {
        let mut eval = constant;
        for (weight, monomials) in &affine {
            let zero = a.zero();
            let x = (chi.iter().zip(monomials)).fold(zero, |s, (&z, &m)| a.mul_const_add(z, F192::from(m), s));
            eval = a.mul_add(*weight, x, eval);
        }
        evals.push(a.add_const(eval, F192::ONE));
        // The last bit's powers are never used.
        if bit + 1 < p.bits {
            constant = a.square(constant);
            for (weight, monomials) in &mut affine {
                *weight = a.square(*weight);
                monomials.iter_mut().for_each(|m| *m = *m * *m);
            }
        }
    }
    evals
}

/// The program columns' share of a producer's public half at `chi`, under the twist `mu`.
///
/// ```text
/// sum_i mu_i D_i,   D_i = sum_x eq(chi, x) c(x)^(2^i),   c(x) = sum_s w_s c_s(x)
/// ```
///
/// The sum over `s` runs over the tuple's public coordinates.
/// Raising to `2^i` is additive, so it splits over the set bits `k` of each `c_s(x)`:
///
/// ```text
/// sum_i mu_i D_i = sum_{s,k} B_{s,k} sum_i mu_i (w_s 2^k)^(2^i),   B_{s,k} = sum_x eq(chi, x) bit_k(c_s(x))
/// ```
///
/// That is one pass over the columns, then a fixed cost per coordinate, bit and power.
pub(crate) fn producer_public_twist(coords: &[Coord], w: &[F192], chi: &[F192], twist: &[F192]) -> F192 {
    let eq = primitives::multilinear::eq_table(chi);
    let mut total = F192::ZERO;
    for (c, &weight) in coords.iter().zip(w) {
        let Coord::Public(PublicColumn { values: vals, .. }) = c else {
            continue;
        };
        assert_eq!(vals.len(), eq.len());
        let mut slices = [F192::ZERO; 64];
        for (&e, v) in eq.iter().zip(vals.iter()) {
            let mut bits = v.to_bits();
            while bits != 0 {
                slices[bits.trailing_zeros() as usize] += e;
                bits &= bits - 1;
            }
        }
        // Running `2^i`-th powers of the weight and of each bit's element.
        let mut weight = weight;
        let mut basis: [F64; 64] = std::array::from_fn(|k| F64::new(1 << k));
        for &mu in twist {
            let sum = (slices.iter().zip(&basis)).fold(F192::ZERO, |s, (b, &g)| s + (*b * g));
            total += mu * weight * sum;
            weight = weight.square();
            basis.iter_mut().for_each(|g| *g = *g * *g);
        }
    }
    total
}

/// One table's bus contribution on one side, as a form over that table's committed
/// columns: `Σ_c coeffs[c]·col_c(z) + Σ (a,b,c) c·col_a(z)·col_b(z) + constant`.
/// Every coefficient is a public function of `α`, `β` and the block selectors at
/// `ζ`, because what a table's bus blocks carry besides `Const`/`Col`/`Prod`
/// coordinates is a top-level `IntIndex` or `Public` one, which the verifier
/// evaluates itself and which stays out of the form. The table sumcheck sums this against `eq(ζ[..τ], ·)` instead of
/// opening each column at `ζ`, which is why those per-column claims no longer reach
/// the PCS.
///
/// The quadratic part comes from [`Coord::Prod`] and is free: the AIR identities are
/// already degree 2, so a degree-2 form does not raise the round-polynomial degree
/// the batch pays for.
#[derive(Clone, Debug)]
pub struct BusForm<E = F192> {
    pub coeffs: Vec<E>,
    /// `(col_a, col_b, coeff)` in LOCAL column indices.
    pub prods: Vec<(usize, usize, E)>,
    pub constant: E,
}

impl<E: Copy> BusForm<E> {
    /// The zero form over `n_cols` columns.
    pub(crate) fn new(n_cols: usize, zero: E) -> Self {
        Self {
            coeffs: vec![zero; n_cols],
            prods: Vec::new(),
            constant: zero,
        }
    }

    /// The form's part linear in the columns `cols`, as a form over them alone, in their order.
    ///
    /// # Panics
    ///
    /// Panics if the form multiplies two columns.
    pub(crate) fn on(&self, cols: &[usize], zero: E) -> Self {
        assert!(self.prods.is_empty(), "a linear form");
        Self {
            coeffs: cols.iter().map(|&c| self.coeffs[c]).collect(),
            prods: Vec::new(),
            constant: zero,
        }
    }

    /// The form at the columns' values `evals`.
    pub fn at<A: Arith<E = E>>(&self, a: &mut A, evals: &[E]) -> E {
        let linear = (self.coeffs.iter().zip(evals)).fold(self.constant, |acc, (&c, &v)| a.mul_add(c, v, acc));
        self.prods.iter().fold(linear, |acc, &(i, j, c)| {
            let p = a.mul(evals[i], evals[j]);
            a.mul_add(c, p, acc)
        })
    }
}

impl BusForm {
    /// The form at the columns' values `evals`, in a verifier's arithmetic: its coefficients are constants.
    pub fn at_constants<A: Arith>(&self, a: &mut A, evals: &[A::E]) -> A::E {
        let constant = a.constant(self.constant);
        let linear = (self.coeffs.iter().zip(evals))
            .filter(|(c, _)| !c.is_zero())
            .fold(constant, |acc, (&c, &v)| a.mul_const_add(v, c, acc));
        self.prods.iter().fold(linear, |acc, &(i, j, c)| {
            let p = a.mul(evals[i], evals[j]);
            a.mul_const_add(p, c, acc)
        })
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
    /// only ever wants a table's total, so its two bus sides collapse to one
    /// dot product and one product list: the row loop then reads the column
    /// values once for both rather than once each.
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

    /// The form at one point: `evals` are the columns' values there.
    /// This is what the zerocheck evaluates, per row while a table is unfolded and
    /// at the sumcheck point after; field products and dot products use Plonky3.
    /// `quadratic` selects only degree-two terms, for a sumcheck round coefficient.
    pub fn eval<T: ColVal>(&self, evals: &[T], quadratic: bool) -> F192 {
        let linear = if quadratic {
            F192::ZERO
        } else {
            T::dot_products(&self.coeffs, evals) + self.constant
        };
        self.add_products(evals, linear)
    }

    /// `acc` plus the form's products at `evals`.
    #[inline(always)]
    fn add_products<T: ColVal>(&self, evals: &[T], acc: F192) -> F192 {
        (self.prods.iter()).fold(acc, |acc, &(a, b, c)| acc + (evals[a] * evals[b]).mul_e(c))
    }

    /// What the form sums to over the table's rows against `eq(ζ, ·)`, the target the
    /// zerocheck settles. The linear part factors through the columns' evaluations at
    /// `ζ`, which is the whole point of a form; a product coordinate does NOT, so
    /// `prod_sums` supplies `Σ_z eq(ζ,z)·col_a(z)·col_b(z)` for each pair it uses.
    pub(super) fn sum_at(&self, evals: &[F192], prod_sums: &[(usize, usize, F192)]) -> F192 {
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

/// A form as the prover's table sumcheck evaluates it per row, on AVX-512 its linear
/// coefficients packed for [`dot_base`].
#[derive(Clone, Debug)]
pub struct PackedForm {
    form: BusForm,
    #[cfg(all(target_arch = "x86_64", target_feature = "vpclmulqdq", target_feature = "avx512f"))]
    packed: PackedCoeffs,
}

impl PackedForm {
    #[cfg_attr(
        not(all(target_arch = "x86_64", target_feature = "vpclmulqdq", target_feature = "avx512f")),
        expect(clippy::missing_const_for_fn, reason = "const only where nothing is packed")
    )]
    pub fn new(form: BusForm) -> Self {
        Self {
            #[cfg(all(target_arch = "x86_64", target_feature = "vpclmulqdq", target_feature = "avx512f"))]
            packed: PackedCoeffs::new(&form.coeffs),
            form,
        }
    }

    /// [`BusForm::eval`], on AVX-512 its linear part one batched dot product
    /// where `evals` is a row padded to the packed width.
    #[inline(always)]
    pub fn eval<T: ColVal>(&self, evals: &[T], quadratic: bool) -> F192 {
        #[cfg(all(target_arch = "x86_64", target_feature = "vpclmulqdq", target_feature = "avx512f"))]
        if !quadratic && evals.len() == self.packed.width() {
            let linear = T::dot_packed(&self.packed, evals) + self.form.constant;
            return self.form.add_products(evals, linear);
        }
        self.form.eval(evals, quadratic)
    }
}

/// Accumulate one coordinate of a table's block, at weight `w`, into that table's form at the block's selector `eq_hi`.
///
/// A constant joins the block's `constant`, which the selector multiplies once.
/// A sum's children share `w`, so a derived value lands as the coefficients and products it is made of.
impl<E: Copy> BusForm<E> {
    fn accumulate<A: Arith<E = E>>(
        &mut self,
        a: &mut A,
        c: &Coord,
        weight: BlockWeight<E>,
        base: usize,
        constant: &mut E,
    ) {
        let BlockWeight { selector, w } = weight;
        match c {
            Coord::Const(v) => *constant = a.mul_const_add(w, F192::from(*v), *constant),
            Coord::Col(i) => self.coeffs[*i - base] = a.mul_add(selector, w, self.coeffs[*i - base]),
            Coord::Prod(i, j) => {
                let product = a.mul(selector, w);
                self.prods.push((*i - base, *j - base, product));
            }
            Coord::Scaled(c, i) => {
                let product = a.mul(selector, w);
                self.coeffs[*i - base] = a.mul_const_add(product, F192::from(*c), self.coeffs[*i - base]);
            }
            Coord::Sum(cs) => {
                for c in cs {
                    self.accumulate(a, c, weight, base, constant);
                }
            }
            Coord::IntIndex { .. } | Coord::Public(_) | Coord::Sparse(_) => {
                unreachable!(
                    "a table's bus block carries a virtual coordinate only at the top level, and no sparse one"
                )
            }
        }
    }
}

/// A coordinate's weight in its side's leaf claim: its block's selector `eq(sel_b, zeta_hi)` times its fingerprint weight `w_i`.
#[derive(Clone, Copy)]
struct BlockWeight<E> {
    selector: E,
    w: E,
}

/// A sparse column's share `weight col(point)` of a side's leaf claim.
///
/// The decomposition leaves it to whoever holds the column: RAM's image is the program's.
#[derive(Clone, Debug)]
pub struct SparseShare<E = F192> {
    /// The column's weight in the leaf claim.
    pub weight: E,
    /// The point at which the column is evaluated.
    pub point: Vec<E>,
    /// The column.
    pub column: Arc<SparseColumn>,
}

impl Side<'_> {
    /// Walk one side's blocks at the GKR point `zeta`, and return the side's known part of its leaf claim.
    ///
    /// - A block owned by table `t` accumulates into `forms[t]`, over the table's local columns (`tables[t]` is its `(base, width)`).
    /// - Its `IntIndex` and `Public` coordinates are no columns: the verifier evaluates them, and they join the known part.
    /// - A producer's bit block leaves its selector in `open.producers`, its air's weight on that bit.
    /// - A framework block decomposes into per-column claims, `fresh` supplying the values not already opened.
    /// - A sparse public column's share is left in `open.sparse`.
    ///
    /// The known part is the framework blocks' contribution to `V_0(zeta)` short of the sparse shares, the tables' virtual coordinates, and the padding mass.
    #[expect(
        clippy::too_many_arguments,
        reason = "the side's fingerprint, point and the claims it extends"
    )]
    pub(super) fn decompose<A: PublicColumns, Er>(
        &self,
        a: &mut A,
        fp: &Fingerprint<A::E>,
        zeta: &[A::E],
        tables: &[(usize, usize)],
        forms: &mut [BusForm<A::E>],
        open: &mut Openings<A::E>,
        mut fresh: impl FnMut(&mut A, usize, &[A::E]) -> Result<A::E, Er>,
    ) -> Result<A::E, Er> {
        let (lay, w, beta) = (&self.lay, &fp.w, fp.beta);
        assert_eq!(zeta.len(), lay.mu);
        // The weight `eq(sel_b, zeta_hi)` block `b`, of `2^kappa` rows, carries in `V_0(zeta)`.
        let selector = |a: &mut A, b: usize, kappa: usize| a.eq_bits(lay.offsets[b] >> kappa, &zeta[kappa..]);
        let mut acc = a.zero();
        let mut sel_sum = a.one();
        let mut b = self.blocks.len();
        for producer in self.producers {
            let selectors: Vec<A::E> = (b..b + producer.bits).map(|b| selector(a, b, producer.kappa)).collect();
            sel_sum = selectors.iter().fold(sel_sum, |s, &e| a.add(s, e));
            open.producers.push(selectors);
            b += producer.bits;
        }
        for (b, blk) in self.blocks.iter().enumerate() {
            let kappa = blk.kappa;
            let zeta_lo = &zeta[..kappa];
            let eq_hi = selector(a, b, kappa);
            sel_sum = a.add(sel_sum, eq_hi);
            open.selectors.push(eq_hi);

            // A table's block becomes a linear form the zerocheck will sum; only the
            // framework blocks (boundary, registers, memory) still open columns at ζ.
            if let Some(t) = blk.owner {
                let form = &mut forms[t];
                let mut constant = beta;
                let mut known = a.zero();
                for (i, c) in blk.coords.iter().enumerate() {
                    match c {
                        Coord::IntIndex { base, shift } => {
                            let x = a.int_index(*base, *shift, zeta_lo);
                            known = a.mul_add(w[i], x, known);
                        }
                        Coord::Public(column) => {
                            let x = open.public(a, column, zeta_lo);
                            known = a.mul_add(w[i], x, known);
                        }
                        _ => form.accumulate(
                            a,
                            c,
                            BlockWeight {
                                selector: eq_hi,
                                w: w[i],
                            },
                            tables[t].0,
                            &mut constant,
                        ),
                    }
                }
                form.constant = a.mul_add(eq_hi, constant, form.constant);
                acc = a.mul_add(eq_hi, known, acc);
                continue;
            }

            // The block's leaf `beta + sum_i w_i c_i` at `zeta_lo`.
            //
            // A column's value is the recorded claim's, else a fresh one, recorded.
            // The push ORDER is the stream order, so every coordinate that needs a column value goes through here.
            let mut leaf = beta;
            for (i, c) in blk.coords.iter().enumerate() {
                leaf = match c {
                    Coord::Const(v) => a.mul_const_add(w[i], F192::from(*v), leaf),
                    Coord::IntIndex { base, shift } => {
                        let x = a.int_index(*base, *shift, zeta_lo);
                        a.mul_add(w[i], x, leaf)
                    }
                    Coord::Col(col) => {
                        let x = match open.known.get(&(*col, kappa)) {
                            Some(&x) => x,
                            None => {
                                let x = fresh(a, *col, zeta_lo)?;
                                open.known.insert((*col, kappa), x);
                                open.claims.push(ColumnClaim {
                                    col: *col,
                                    point: zeta_lo.to_vec(),
                                    value: x,
                                });
                                x
                            }
                        };
                        a.mul_add(w[i], x, leaf)
                    }
                    Coord::Prod(..) | Coord::Scaled(..) | Coord::Sum(..) => {
                        unreachable!("only a table's bus block carries a degree-2 coordinate")
                    }
                    Coord::Public(column) => {
                        let x = open.public(a, column, zeta_lo);
                        a.mul_add(w[i], x, leaf)
                    }
                    Coord::Sparse(column) => {
                        let weight = a.mul(eq_hi, w[i]);
                        open.sparse.push(SparseShare {
                            weight,
                            point: zeta_lo.to_vec(),
                            column: Arc::clone(column),
                        });
                        leaf
                    }
                };
            }
            acc = a.mul_add(eq_hi, leaf, acc);
        }
        // The padding rows (identity `1`) contribute the leftover mass `1 - sum_b sel_b`.
        Ok(a.add(acc, sel_sum))
    }

    /// Prover-side decomposition: reads the real columns, writing each FRESH
    /// committed value onto the stream and recording the matching claim
    /// (block/coord order); duplicates reuse the recorded value.
    ///
    /// The fresh column MLE evaluations run in a parallel first pass: within one
    /// decomposition no challenge is sampled between claims (`zeta`,
    /// `alpha`, `beta` are fixed arguments and each claim's point is
    /// `zeta[..kappa]` of its block), so the values are independent of the
    /// transcript and only their `add_scalar` ORDER matters. The second pass
    /// replays them through the transcript in the original block/coord order,
    /// keeping the stream byte-identical to the serial form.
    #[expect(
        clippy::too_many_arguments,
        reason = "the side's fingerprint, columns, point and the claims it extends"
    )]
    pub(super) fn decompose_prove(
        &self,
        fp: &Fingerprint<F192>,
        cols: &[&[F64]],
        zeta: &[F192],
        tables: &[(usize, usize)],
        forms: &mut [BusForm],
        open: &mut Openings<F192>,
        ps: &mut ProverState,
    ) -> F192 {
        // Pass 1: enumerate the FRESH committed coords exactly as the decomposition
        // visits them (framework blocks in order, coords in order, Col only, first
        // occurrence per `(col, κ)`), then evaluate the column MLEs in parallel.
        let mut jobs: Vec<(usize, usize)> = Vec::new();
        let mut seen = HashSet::new();
        for blk in self.blocks.iter().filter(|b| b.owner.is_none()) {
            for c in &blk.coords {
                if let Coord::Col(i) = c {
                    let key = (*i, blk.kappa);
                    if !open.known.contains_key(&key) && seen.insert(key) {
                        jobs.push(key);
                    }
                }
            }
        }
        let vals: Vec<F192> = parallel::map_collect(jobs.len(), |i| {
            let (col, kappa) = jobs[i];
            mle_eval(cols[col], &zeta[..kappa])
        });

        // Pass 2: replay in the original order; duplicates reuse the recorded claim.
        let mut fresh_iter = jobs.iter().zip(vals.iter());
        let framework = self.decompose(&mut Native, fp, zeta, tables, forms, open, |_, col, zeta_lo| {
            let (&(jc, jk), &v) = fresh_iter
                .next()
                .expect("job enumeration matches the decomposition's column order");
            debug_assert_eq!((jc, jk), (col, zeta_lo.len()), "job/coord order drift");
            debug_assert_eq!(v, mle_eval(cols[col], zeta_lo), "job/coord order drift");
            ps.add_scalar(v);
            Ok::<_, Infallible>(v)
        });
        let Ok(framework) = framework;
        (open.sparse.drain(..)).fold(framework, |acc, s| acc + s.weight * s.column.eval(&s.point))
    }
}
