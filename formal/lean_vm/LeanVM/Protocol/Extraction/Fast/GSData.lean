module

-- CompPoly's division helpers (`lowEq`, `inverseModX_lowEq`, …) are private: `import all` reads them.
import all CompPoly.Univariate.Basic
import all CompPoly.Univariate.Raw.Core
import all CompPoly.Univariate.DivisionCorrectness
public import CompPoly.Univariate.DivisionCorrectness
public import CompPoly.Bivariate.GuruswamiSudan.Interpolation.ApproximantBasis.Basic

/-!
# The Guruswami–Sudan modular data, the moduli's inverses computed once

CompPoly's relation column (`gsRelationColumn`) carries `R^(j−b) mod M_b` from entry to entry: one
product `power · (R mod M_b)` and one monic remainder per entry. The remainder by reversal
(`modByMonicByReversal`, the reduction of `ModContext.reversal`) computes the inverse of the
reversed modulus modulo `X^k` by Newton's iteration at every call, `k = |p| − |M_b| + 1`.

`modByMonicCached M inv K` is that remainder with the inverse supplied: `inv`, the inverse at
precision `K`, is used whenever `k ≤ K` (its low `k` coefficients are the inverse at precision `k`:
an inverse modulo `X^k` is unique), Newton's iteration otherwise. **`modByMonicCached_eq`**: with
`inv = inverseModX M K (rev M_b)` it is `modByMonicByReversal M`, for every `K`.

`gsRelationColumnCached` computes, per column, the inverse once at precision `|R mod M_b|` (each
entry's dividend `power · (R mod M_b)`, `|power| < |M_b|`, needs `k ≤ |R mod M_b| − 1`), and
reduces every entry with it; **`gsRelationColumnCached_eq`**: it is `gsRelationColumn` for every
remainder context. `buildGSModularDataCached` builds the data with it
(**`buildGSModularDataCached_eq`**: it is `buildGSModularDataWithRG`).

The moduli need no change: `gsModuli` builds `G, G², …, G^m` each by one product of the previous
power by `G` (`m − 1` products), then reverses the array.

Credits: CompPoly's remainder by reversal and its correctness lemmas (`Univariate/Raw/Division.lean`,
`Univariate/DivisionCorrectness.lean`, github.com/Verified-zkEVM/CompPoly, Apache-2.0, "Copyright
(c) 2026 CompPoly Contributors").
-/

namespace LeanVM.Extraction.Fast

open CompPoly CompPoly.CPolynomial Polynomial

public section

variable {F : Type*} [Field F] [BEq F] [LawfulBEq F]

/-! ## The remainder with a supplied inverse -/

/-- CompPoly's `Raw.modByMonicByReversal` with the reversed divisor's inverse supplied: `inv`,
meant as the inverse at precision `K`, is used when the precision needed is at most `K`. -/
@[expose] def rawModByMonicCached (M : Raw.MulLowContext F) (inv : Raw F) (K : Nat)
    (p q : Raw F) : Raw F :=
  if p.trim == p && q.trim == q && q.leadingCoeff == 1 then
    if p.size < q.size then
      p
    else
      let k := p.size - q.size + 1
      let remainderLen := q.size - 1
      let revP := Raw.reverse p.size p
      let invRevQ := if k ≤ K then inv else Raw.inverseModX M k (Raw.reverse q.size q)
      let quotientRev := M.mulLow k revP invRevQ
      let quotient := Raw.reverse k quotientRev
      let productLow := M.mulLow remainderLen q quotient
      Raw.truncate remainderLen p - productLow
  else
    Raw.modByMonicRemainderOnly p q

theorem rawModByMonicCached_canonical (M : Raw.MulLowContext F) (inv : Raw F) (K : Nat)
    {p : Raw F} (hp : p.trim = p) (q : Raw F) :
    (rawModByMonicCached M inv K p q).trim = rawModByMonicCached M inv K p q := by
  unfold rawModByMonicCached
  split
  · split
    · exact hp
    · exact Raw.sub_is_trimmed _ _
  · exact Raw.modByMonicRemainderOnly_canonical hp q

/-- **The monic remainder by reversal, the inverse supplied.** -/
@[expose] def modByMonicCached (M : Raw.MulLowContext F) (inv : Raw F) (K : Nat)
    (p q : CPolynomial F) : CPolynomial F :=
  ⟨rawModByMonicCached M inv K p.val q.val,
   Raw.Trim.isCanonical_of_trim_eq
     (rawModByMonicCached_canonical M inv K (Raw.Trim.trim_eq_of_isCanonical p.property) q.val)⟩

omit [BEq F] [LawfulBEq F] in
/-- An inverse modulo `X^k` is unique. -/
private theorem lowEq_inv_unique {k : Nat} {a x y : F[X]} (hx : lowEq k (a * x) 1)
    (hy : lowEq k (a * y) 1) : lowEq k x y := by
  have h1 : lowEq k (x * (a * y)) x := by simpa only [mul_one] using lowEq.mul_left x hy
  have h2 : lowEq k (y * (a * x)) y := by simpa only [mul_one] using lowEq.mul_left y hx
  have h3 : x * (a * y) = y * (a * x) := by ring
  rw [h3] at h1
  exact h1.symm.trans h2

/-- The reversal's quotient, from two inverses agreeing below `k`. -/
private theorem toPoly_reverse_mulLow_congr (M : Raw.MulLowContext F) {k : Nat}
    (revP a b : Raw F) (h : lowEq k a.toPoly b.toPoly) :
    (Raw.reverse k (M.mulLow k revP a)).toPoly = (Raw.reverse k (M.mulLow k revP b)).toPoly := by
  have hl := lowEq.mul_left revP.toPoly h
  ext j
  rw [toPoly_reverse_coeff, toPoly_reverse_coeff]
  split
  · rw [toPoly_mulLow_coeff, toPoly_mulLow_coeff]
    split
    · exact hl _ (by omega)
    · rfl
  · rfl

/-- **The remainder with the inverse supplied is CompPoly's remainder by reversal.** -/
theorem modByMonicCached_eq (M : Raw.MulLowContext F) (K : Nat) (p q : CPolynomial F) :
    modByMonicCached M (Raw.inverseModX M K (Raw.reverse q.val.size q.val)) K p q =
      modByMonicByReversal M p q := by
  apply CPolynomial.toPoly_injective
  show (rawModByMonicCached M _ K p.val q.val).toPoly =
    (Raw.modByMonicByReversal M p.val q.val).toPoly
  unfold rawModByMonicCached Raw.modByMonicByReversal
  split
  · rename_i hg
    split
    · rfl
    · rename_i hs
      simp only []
      split
      · rename_i hk
        -- The guard: `q` canonical and monic, so its reversal has constant coefficient `1`.
        simp only [Bool.and_eq_true, beq_iff_eq] at hg
        obtain ⟨⟨-, hqtrim⟩, hlc⟩ := hg
        have hqpos : 0 < q.val.size := by
          by_contra h0
          have hz : (q.val : Raw F).leadingCoeff = 0 := by
            rw [Raw.leadingCoeff, hqtrim]
            simp [Array.getLastD, show q.val.size = 0 by omega]
          rw [hz] at hlc
          exact zero_ne_one hlc
        have h0 : (Raw.reverse q.val.size q.val).toPoly.coeff 0 ≠ 0 := by
          rw [toPoly_reverse_coeff, ite_eq_left hqpos, Raw.coeff_toPoly, Nat.sub_zero,
            raw_coeff_last_eq_leadingCoeff_of_trim_eq q.val hqtrim hqpos, hlc]
          exact one_ne_zero
        have hK := (inverseModX_lowEq M K _ h0).of_le hk
        have hk' := inverseModX_lowEq M (p.val.size - q.val.size + 1) _ h0
        have hq := toPoly_reverse_mulLow_congr M (Raw.reverse p.val.size p.val) _ _
          (lowEq_inv_unique hK hk')
        ext i
        rw [Raw.toPoly_sub, Raw.toPoly_sub, Polynomial.coeff_sub, Polynomial.coeff_sub,
          toPoly_mulLow_coeff, toPoly_mulLow_coeff, hq]
      · rfl
  · rfl

/-! ## The relation column, the inverse once per column -/

/-- CompPoly's `gsRelationColumn` with the remainder by reversal on `M`, the reversed modulus's
inverse computed once at precision `|R mod M_b|`, and the binomials `C(j, b)` carried along the
column (`C(j + 1, b) = C(j, b)·(j + 1)/(j + 1 − b)`) instead of `Nat.choose`'s recursion, whose
compiled price is the binomial itself. -/
@[expose] def gsRelationColumnCached (mulCtx : CPolynomial.MulContext F) (M : Raw.MulLowContext F)
    (R modulus : CPolynomial F) (width b : Nat) : Array (CPolynomial F) :=
  let reducedR := PolynomialMatrix.modByMonicWith (CPolynomial.ModContext.reversal M) R modulus
  let K := reducedR.val.size
  let inv := Raw.inverseModX M K (Raw.reverse modulus.val.size modulus.val)
  ((List.range' b (width - b)).foldl
    (fun st j ↦
      ((st.1.1.setIfInBounds j (CPolynomial.C ((st.2 : F)) * st.1.2),
        if modulus == 0 then mulCtx.mul st.1.2 reducedR
        else modByMonicCached M inv K (mulCtx.mul st.1.2 reducedR) modulus),
       st.2 * (j + 1) / (j + 1 - b)))
    ((Array.replicate width (0 : CPolynomial F), 1), 1)).1.1

/-- The binomial carried: `C(j + 1, b) = C(j, b)·(j + 1)/(j + 1 − b)` for `b ≤ j`. -/
theorem choose_succ_div {j b : Nat} (h : b ≤ j) :
    j.choose b * (j + 1) / (j + 1 - b) = (j + 1).choose b := by
  rw [Nat.choose_mul_succ_eq]
  exact Nat.mul_div_cancel _ (by omega)

omit [BEq F] [LawfulBEq F] in
/-- Carrying the binomial: the fold with `C(j, b)` carried is the fold with `Nat.choose`. -/
theorem foldl_carry_choose {α : Type*} (f : α → Nat → α) (g : α → Nat → F → α) (b : Nat)
    (hfg : ∀ a j, f a j = g a j ((j.choose b : Nat) : F)) :
    ∀ (n j₀ : Nat) (a : α), b ≤ j₀ →
      (List.range' j₀ n).foldl
          (fun st j ↦ (g st.1 j ((st.2 : Nat) : F), st.2 * (j + 1) / (j + 1 - b)))
          (a, j₀.choose b) =
        ((List.range' j₀ n).foldl f a, (j₀ + n).choose b) := by
  intro n
  induction n with
  | zero => intro j₀ a _; rfl
  | succ n ih =>
    intro j₀ a hb
    rw [List.range'_succ, List.foldl_cons, List.foldl_cons, choose_succ_div hb, ← hfg,
      ih (j₀ + 1) (f a j₀) (by omega)]
    congr 2
    omega

/-- CompPoly's `gsRelationColumn`'s loop, as a fold. -/
private theorem gsRelationColumn_eq_fold (mulCtx : CPolynomial.MulContext F)
    (modCtx : CPolynomial.ModContext F) (R modulus : CPolynomial F) (width b : Nat) :
    GuruswamiSudan.ApproximantBasis.gsRelationColumn mulCtx modCtx R modulus width b =
      ((List.range' b (width - b)).foldl
        (fun st j ↦
          (st.1.setIfInBounds j (CPolynomial.C ((j.choose b : F)) * st.2),
           PolynomialMatrix.modByMonicWith modCtx
             (mulCtx.mul st.2 (PolynomialMatrix.modByMonicWith modCtx R modulus)) modulus))
        (Array.replicate width (0 : CPolynomial F), 1)).1 := by
  rw [GuruswamiSudan.ApproximantBasis.gsRelationColumn]
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.add_sub_cancel, Nat.div_one, List.forIn_pure_yield_eq_foldl,
    bind_pure_comp, map_pure, Id.run_pure]

/-- Every remainder context computes CompPoly's monic remainder. -/
theorem modByMonicWith_congr (A B : CPolynomial.ModContext F) :
    PolynomialMatrix.modByMonicWith A = PolynomialMatrix.modByMonicWith B := by
  funext p modulus
  unfold PolynomialMatrix.modByMonicWith
  rw [A.modByMonic_eq_modByMonic, B.modByMonic_eq_modByMonic]

/-- **The relation column with the inverse computed once is CompPoly's**, for every remainder
context. -/
theorem gsRelationColumnCached_eq (mulCtx : CPolynomial.MulContext F) (M : Raw.MulLowContext F)
    (modCtx : CPolynomial.ModContext F) (R modulus : CPolynomial F) (width b : Nat) :
    gsRelationColumnCached mulCtx M R modulus width b =
      GuruswamiSudan.ApproximantBasis.gsRelationColumn mulCtx modCtx R modulus width b := by
  rw [gsRelationColumn_eq_fold, gsRelationColumnCached,
    modByMonicWith_congr modCtx (CPolynomial.ModContext.reversal M)]
  rw [show ((Array.replicate width (0 : CPolynomial F), (1 : CPolynomial F)), (1 : Nat)) =
      ((Array.replicate width (0 : CPolynomial F), (1 : CPolynomial F)), b.choose b) by
    rw [Nat.choose_self]]
  have h := foldl_carry_choose
    (fun (st : Array (CPolynomial F) × CPolynomial F) j ↦
      (st.1.setIfInBounds j (CPolynomial.C ((j.choose b : Nat) : F) * st.2),
        if (modulus == 0) = true then
          mulCtx.mul st.2 (PolynomialMatrix.modByMonicWith (CPolynomial.ModContext.reversal M) R
            modulus)
        else
          modByMonicCached M (Raw.inverseModX M (PolynomialMatrix.modByMonicWith
              (CPolynomial.ModContext.reversal M) R modulus).val.size
              (Raw.reverse modulus.val.size modulus.val))
            (PolynomialMatrix.modByMonicWith (CPolynomial.ModContext.reversal M) R modulus).val.size
            (mulCtx.mul st.2 (PolynomialMatrix.modByMonicWith (CPolynomial.ModContext.reversal M) R
              modulus)) modulus))
    (fun st j c ↦
      (st.1.setIfInBounds j (CPolynomial.C c * st.2),
        if (modulus == 0) = true then
          mulCtx.mul st.2 (PolynomialMatrix.modByMonicWith (CPolynomial.ModContext.reversal M) R
            modulus)
        else
          modByMonicCached M (Raw.inverseModX M (PolynomialMatrix.modByMonicWith
              (CPolynomial.ModContext.reversal M) R modulus).val.size
              (Raw.reverse modulus.val.size modulus.val))
            (PolynomialMatrix.modByMonicWith (CPolynomial.ModContext.reversal M) R modulus).val.size
            (mulCtx.mul st.2 (PolynomialMatrix.modByMonicWith (CPolynomial.ModContext.reversal M) R
              modulus)) modulus)) b (fun _ _ ↦ rfl) (width - b) b
    (Array.replicate width (0 : CPolynomial F), 1) le_rfl
  rw [h]
  simp only []
  congr 1
  congr 1
  funext st j
  congr 1
  unfold PolynomialMatrix.modByMonicWith
  split
  · rfl
  · exact modByMonicCached_eq M _ _ _

/-! ## The modular data -/

/-- CompPoly's `gsRelationMatrixWithModuli` with `gsRelationColumnCached`. -/
@[expose] def gsRelationMatrixCached (mulCtx : CPolynomial.MulContext F) (M : Raw.MulLowContext F)
    (R : CPolynomial F) (moduli : Array (CPolynomial F))
    (params : GuruswamiSudan.GSInterpParams) : PolynomialMatrix F :=
  let width := GuruswamiSudan.interpolationWidth params
  let columns := (List.range params.multiplicity).map
    (fun b ↦ gsRelationColumnCached mulCtx M R (moduli.getD b 1) width b) |>.toArray
  PolynomialMatrix.ofFn width params.multiplicity fun j b ↦ (columns.getD b #[]).getD j 0

theorem gsRelationMatrixCached_eq (mulCtx : CPolynomial.MulContext F) (M : Raw.MulLowContext F)
    (modCtx : CPolynomial.ModContext F) (R : CPolynomial F) (moduli : Array (CPolynomial F))
    (params : GuruswamiSudan.GSInterpParams) :
    gsRelationMatrixCached mulCtx M R moduli params =
      GuruswamiSudan.ApproximantBasis.gsRelationMatrixWithModuli mulCtx modCtx R moduli params := by
  simp only [gsRelationMatrixCached, GuruswamiSudan.ApproximantBasis.gsRelationMatrixWithModuli,
    gsRelationColumnCached_eq mulCtx M modCtx]

/-- **The Guruswami–Sudan modular data, the moduli's inverses computed once per column**:
CompPoly's `buildGSModularDataWithRG` with `gsRelationMatrixCached`. -/
@[expose] def buildGSModularDataCached [DecidableEq F] (mulCtx : CPolynomial.MulContext F)
    (M : Raw.MulLowContext F) (R G : CPolynomial F) (params : GuruswamiSudan.GSInterpParams) :
    GuruswamiSudan.ApproximantBasis.GSModularData F :=
  let moduli := GuruswamiSudan.ApproximantBasis.gsModuli mulCtx G params.multiplicity
  { G := G
    R := R
    moduli := moduli
    matrix := gsRelationMatrixCached mulCtx M R moduli params
    shift := GuruswamiSudan.interpolationShifts params }

/-- **The data with the inverses computed once is CompPoly's**, for every remainder context. -/
theorem buildGSModularDataCached_eq [DecidableEq F] (mulCtx : CPolynomial.MulContext F)
    (M : Raw.MulLowContext F) (modCtx : CPolynomial.ModContext F) (R G : CPolynomial F)
    (params : GuruswamiSudan.GSInterpParams) :
    buildGSModularDataCached mulCtx M R G params =
      GuruswamiSudan.ApproximantBasis.buildGSModularDataWithRG mulCtx modCtx R G params := by
  simp only [buildGSModularDataCached, GuruswamiSudan.ApproximantBasis.buildGSModularDataWithRG,
    gsRelationMatrixCached_eq mulCtx M modCtx]

end

end LeanVM.Extraction.Fast
