module

public import LeanVM.Cost.Bounds.PMSolve.Remainder
public import LeanVM.Cost.Bounds.PMSolve.Solve
import all CompPoly.Univariate.Raw.Core
import all CompPoly.Univariate.Raw.Ops
import all CompPoly.Univariate.Raw.Division
import all CompPoly.Univariate.Basic
import all CompPoly.Univariate.Context
import all CompPoly.LinearAlgebra.PolynomialMatrix.Basic
import all CompPoly.LinearAlgebra.PolynomialMatrix.Operations
import all LeanVM.Protocol.Extraction.Fast.GSData

public import LeanVM.Cost.Bounds.PMLane.InterpDefs
/-!
# Bounds: a relation column of the GS data, compiled

`gsRelationColumnCached fftMulContext fftRawMulLowContext R M_b width b` (`gsRelationColumnC`):
`R mod M_b` (the first branch: `R` is shorter than the modulus), the reversed modulus's inverse
once (Newton, `InvBound`), then per entry `j ∈ [b, width)`: the binomial `C(j, b)` (carried, a few
limbs), the entry `C(j, b)·power` (a schoolbook product by a constant), the next power
`power·R mod M_b` (a product, `MulBound`, and the cached remainder, `modByMonicCachedC_cost`).

**`gsRelationColumnC_cost`**: at most `colPrice = IB + width·(colStep + 9) + 110·N + 19·width +
174`, `colStep = MB + LB + LBq + 419·N + 4·width + 719`, on a monic modulus of at least `2` and
a dividend `R` shorter than it, `|M| + |R| ≤ N`: the product within `MB` (its result at most `N`
coefficients), the back-product within `LB` (precision `|M| − 1 ≤ Nb`), the quotient within `LBq`
and the inverse within `IB` (precision at most `|R| ≤ Nq`).
-/

namespace LeanVM.Cost.Bounds.PMSolve

open LeanVM.Cost LeanVM.Cost.Bounds LeanVM.Cost.Library LeanVM.Cost.Bounds.Decoder
open LeanVM.Cost.Extractor LeanVM.Parameters CompPoly LeanVM.Extraction.Fast
open CompPoly.PolynomialMatrix CompPoly.PolynomialMatrix.Approximant

open LeanVM.Cost.Auto.CompPoly.PolynomialMatrix

public section

theorem size_C_le (c : K) : (CPolynomial.C c).val.size ≤ 1 := by
  show (CPolynomial.Raw.C c).trim.size ≤ 1
  exact (raw_trim_size_le _).trans (by simp [CPolynomial.Raw.C])

/-- The remainder by a nonzero monic modulus has at most `deg M` coefficients. -/
theorem size_modByMonicCached_le (p M : CPolynomial K) (hM : M.monic = true) (Kp : ℕ) :
    (modByMonicCached FFT.fftRawMulLowContext
      (CPolynomial.Raw.inverseModX FFT.fftRawMulLowContext Kp
        (CPolynomial.Raw.reverse M.val.size M.val)) Kp p M).val.size ≤ M.natDegree := by
  rw [modByMonicCached_eq]
  have h := size_modByMonicWith_le (CPolynomial.ModContext.reversal FFT.fftRawMulLowContext) p hM
  have hM0 : (M == 0) = false := by
    cases h0 : M == 0 with
    | false => rfl
    | true =>
      have : M = 0 := by simpa using h0
      subst this
      simp [CPolynomial.monic, CPolynomial.leadingCoeff] at hM
      exact absurd hM (by decide)
  unfold PolynomialMatrix.modByMonicWith at h
  rw [hM0] at h
  exact h

/-- A product's size: at most the sizes' sum less one, or the product is zero. -/
theorem size_mul_le' (x y : CPolynomial K) :
    (x * y).val.size + 1 ≤ x.val.size + y.val.size ∨ x * y = 0 := by
  by_cases h : x * y = 0
  · exact Or.inr h
  · left
    have hx : x ≠ 0 := fun hx ↦ h (by rw [hx, zero_mul])
    have hy : y ≠ 0 := fun hy ↦ h (by rw [hy, mul_zero])
    have hsz : ∀ p : CPolynomial K, p ≠ 0 → p.natDegree + 1 = p.val.size := by
      intro p hp
      have h1 : p.val.size ≠ 0 := by
        intro h0
        apply hp
        apply CPolynomial.ext
        exact Array.eq_empty_of_size_eq_zero h0
      unfold CPolynomial.natDegree
      generalize p.val.size = s at h1 ⊢
      cases s with
      | zero => omega
      | succ k => rfl
    have hd : (x * y).natDegree ≤ x.natDegree + y.natDegree := by
      rw [CPolynomial.natDegree_toPoly, CPolynomial.natDegree_toPoly x,
        CPolynomial.natDegree_toPoly y, CPolynomial.toPoly_mul]
      exact Polynomial.natDegree_mul_le
    have := hsz _ h
    have := hsz _ hx
    have := hsz _ hy
    omega

variable (P : MachineProgram)

/-- **The column's fold**, from entry `j₀` on, `n` entries: at most `(colStep + 9)·n + 3`. -/
theorem colFoldC_cost (hP : Includes P gsRelationColumnC.costDeps)
    {N Nb Nq MB LB LBq : ℕ} (hMB : MulBound P N MB) (hLB : LowBound P Nb LB)
    (hLq : LowBound P Nq LBq)
    (M R : CPolynomial K) (hM : M.monic = true) (hN : M.val.size + R.val.size ≤ N)
    (hMb : M.val.size ≤ Nb + 1) (hRq : R.val.size ≤ Nq)
    (hN58 : N < 2 ^ 58) (w b : ℕ) (hw : w < 2 ^ 20) (h2 : 2 ≤ M.val.size)
    (inv : CPolynomial.Raw K) (hinvdef : inv = CPolynomial.Raw.inverseModX FFT.fftRawMulLowContext
      R.val.size (CPolynomial.Raw.reverse M.val.size M.val)) :
    ∀ (n j₀ : ℕ) (st : (Array (CPolynomial K) × CPolynomial K) × ℕ), b ≤ j₀ → j₀ + n ≤ w →
      st.2 = j₀.choose b → st.1.1.size = w → st.1.2.val.size + 1 ≤ M.val.size →
      machineCost P Library.listFoldl.costIdx
          [.closure gsRelationColumnC.lam0.costIdx [encodeValue M, encodeValue b, encodeValue inv,
            encodeValue R.val.size, encodeValue R], encodeValue st, encodeValue (List.range' j₀ n)] ≤
        (colStep N w MB LB LBq + 9) * n + 3 := by
  have hf := fun st j ↦ (RunsApp.of_spec (us := [encodeValue M, encodeValue b, encodeValue inv,
    encodeValue R.val.size, encodeValue R]) (vs := [encodeValue st, encodeValue j])
    (gsRelationColumnC.lam0.costSpec P (by includes) M b inv R.val.size R st j) :
      RunsApp P (.closure gsRelationColumnC.lam0.costIdx [encodeValue M, encodeValue b,
        encodeValue inv, encodeValue R.val.size, encodeValue R]) _ _)
  have hM0 : (M == 0) = false := by
    cases h0 : M == 0 with
    | false => rfl
    | true =>
      have : M = 0 := by simpa using h0
      subst this
      rw [size_zero_val] at h2
      omega
  have hMd : M.natDegree + 1 = M.val.size := by
    unfold CPolynomial.natDegree
    generalize M.val.size = s at h2 ⊢
    cases s with
    | zero => omega
    | succ k => rfl
  intro n
  induction n with
  | zero =>
    intro j₀ st _ _ _ _ _
    rw [List.range'_zero, Library.listFoldl.costEq_nil P (by includes) _ _ hf]
    omega
  | succ n ih =>
    intro j₀ st hb hj hc hs hpow
    rw [List.range'_succ, Library.listFoldl.costEq_cons P (by includes) _ _ hf]
    simp only [appCost_fn, List.cons_append, List.nil_append]
    rw [gsRelationColumnC.lam0.costEq P (by includes)]
    obtain ⟨⟨col, pow⟩, c⟩ := st
    simp only at hc hs hpow ⊢
    subst hc
    -- the binomial and its limbs
    have hcw : j₀.choose b < 2 ^ w :=
      lt_of_le_of_lt (Nat.choose_le_two_pow _ _) (Nat.pow_lt_pow_right (by norm_num) (by omega))
    have hw1 : 1 ≤ w := by omega
    have hL1 : limbCount (j₀.choose b) ≤ w := limbCount_le_of_lt hw1 (by
      calc j₀.choose b < 2 ^ w := hcw
        _ ≤ 2 ^ (64 * w) := Nat.pow_le_pow_right (by norm_num) (by omega))
    have hL2 : limbCount (j₀.choose b * (j₀ + 1)) ≤ w + 1 := limbCount_le_of_lt (by omega) (by
      calc j₀.choose b * (j₀ + 1) < 2 ^ w * 2 ^ 20 :=
            Nat.mul_lt_mul_of_lt_of_le hcw (by
              have : j₀ + 1 ≤ 2 ^ 20 := by omega
              exact this) (by positivity)
        _ = 2 ^ (w + 20) := by rw [← Nat.pow_add]
        _ ≤ 2 ^ (64 * (w + 1)) := Nat.pow_le_pow_right (by norm_num) (by omega))
    have hL3 : limbCount (j₀.choose b % 2) = 1 := limbs_of_lt (by omega)
    have hnc := Auto.BF64.natCast.c579.costEq P (by includes) (j₀.choose b)
    rw [ite_self] at hnc
    have := cK_cost P (by includes) (j₀.choose b : K)
    have hC := size_C_le (j₀.choose b : K)
    have := mulK_cost P (by includes) (CPolynomial.C (j₀.choose b : K)).val pow.val (by omega)
      (by omega)
    have hCp : pow.val.size * (CPolynomial.C (j₀.choose b : K)).val.size ≤ pow.val.size :=
      (Nat.mul_le_mul_left _ hC).trans (by simp)
    have hCC : (CPolynomial.C (j₀.choose b : K)).val.size *
        (CPolynomial.C (j₀.choose b : K)).val.size ≤ 1 := (Nat.mul_le_mul hC hC).trans (by simp)
    have := listBeqK_cost P (by includes) M.val.toList (↑(0 : CPolynomial K) : Array K).toList
    -- the product and the remainder
    have hmul := hMB pow R (by omega)
    have hprod := cpoly_mul_size_le pow R
    have hfm : FFT.fftMulContext.mul pow R = pow * R := FFT.fftMulContext.mul_eq_mul pow R
    have hprod' := size_mul_le' pow R
    have hrem := modByMonicCachedC_cost P (by includes) hLB hLq inv R.val.size (pow * R) M hM hN58
      (by omega) hRq (by omega) (by omega) hMb (by
        rcases Nat.lt_or_ge (pow * R).val.size M.val.size with hlt | hge
        · exact Or.inl hlt
        · right
          rcases hprod' with h | h
          · omega
          · rw [h, size_zero_val] at hge; omega)
    -- the next state
    have hnext := ih (j₀ + 1)
      ((col.setIfInBounds j₀ (CPolynomial.C ((j₀.choose b : ℕ) : K) * pow),
        if (M == 0) = true then FFT.fftMulContext.mul pow R
        else modByMonicCached FFT.fftRawMulLowContext inv R.val.size (FFT.fftMulContext.mul pow R) M),
        j₀.choose b * (j₀ + 1) / (j₀ + 1 - b))
      (by omega) (by omega) (choose_succ_div hb) (by simp [hs]) (by
        have := size_modByMonicCached_le (pow * R) M hM R.val.size
        rw [← hinvdef] at this
        simp only [hfm, hM0, Bool.false_eq_true, ↓reduceIte]
        omega)
    rw [hfm, hM0]
    simp only [Bool.false_eq_true, ↓reduceIte]
    have hz : (↑(0 : CPolynomial K) : Array K).size = 0 := rfl
    have hsz : (col.setIfInBounds j₀ (CPolynomial.C (j₀.choose b : K) * pow)).size = w := by
      simp [hs]
    simp only [Array.length_toList, hz] at *
    rw [hfm, hM0] at hnext
    simp only [Bool.false_eq_true, ↓reduceIte] at hnext
    have hmono : limbCount (j₀.choose b) * limbCount (j₀ + 1) ≤ w := by
      rw [limbs_of_lt (by omega : j₀ + 1 < 2 ^ 64)]; omega
    have hmono2 : limbCount (j₀.choose b * (j₀ + 1)) * limbCount (j₀ + 1 - b) ≤ w + 1 := by
      rw [limbs_of_lt (by omega : j₀ + 1 - b < 2 ^ 64)]; omega
    have hcs : colStep N w MB LB LBq = MB + LB + LBq + 419 * N + 4 * w + 719 := rfl
    have he : (colStep N w MB LB LBq + 9) * (n + 1) =
        (colStep N w MB LB LBq + 9) * n + colStep N w MB LB LBq + 9 := by ring
    rw [he]
    cost_simp
    omega


theorem natDegree_lt_of_size_lt {R M : CPolynomial K} (h : R.val.size < M.val.size)
    (h2 : 2 ≤ M.val.size) : R.natDegree < M.natDegree := by
  unfold CPolynomial.natDegree
  generalize R.val.size = r at h ⊢
  generalize M.val.size = s at h h2 ⊢
  cases r <;> cases s <;> dsimp only <;> omega

/-- `R mod M` is `R` when `R` is shorter than the monic `M`. -/
theorem reducedR_eq (R M : CPolynomial K) (hM : M.monic = true) (h : R.val.size < M.val.size)
    (h2 : 2 ≤ M.val.size) :
    PolynomialMatrix.modByMonicWith (CPolynomial.ModContext.reversal FFT.fftRawMulLowContext) R M =
      R :=
  modByMonicWith_eq_self _ ((CPolynomial.monic_toPoly_iff M).1 hM) (natDegree_lt_of_size_lt h h2)

/-- **A relation column** (`gsRelationColumnC`): at most `colPrice N w MB LB LBq IB`. -/
theorem gsRelationColumnC_cost (hP : Includes P gsRelationColumnC.costDeps)
    {N Nb Nq MB LB LBq IB : ℕ} (hMB : MulBound P N MB) (hLB : LowBound P Nb LB)
    (hLq : LowBound P Nq LBq) (hIB : InvBound P Nq IB)
    (R M : CPolynomial K) (hM : M.monic = true) (hRM : R.val.size < M.val.size)
    (h2 : 2 ≤ M.val.size) (hN : M.val.size + R.val.size ≤ N) (hMb : M.val.size ≤ Nb + 1)
    (hRq : R.val.size ≤ Nq) (hN58 : N < 2 ^ 58) (w b : ℕ)
    (hw : w < 2 ^ 20) (hb : b ≤ w) :
    machineCost P gsRelationColumnC.costIdx [encodeValue R, encodeValue M, encodeValue w,
        encodeValue b] ≤ colPrice N w MB LB LBq IB := by
  rw [gsRelationColumnC.costEq P hP, reducedR_eq R M hM hRM h2]
  have := modByMonicWithC_first_cost P (by includes) R M hM hRM (by omega)
  have := reverseC_cost P (by includes) M.val.size (by omega) M.val
  have := hIB R.val.size (CPolynomial.Raw.reverse M.val.size M.val) hRq
  have := rangeC_cost P (by includes) (w - b) b (by omega)
  have hfold := colFoldC_cost P (by includes) hMB hLB hLq M R hM hN hMb hRq hN58 w b hw h2 _ rfl
    (w - b) b
    ((Array.replicate w 0, 1), 1) le_rfl (by omega) (Nat.choose_self b).symm (by simp)
    (by have := size_one_K; simp only []; omega)
  have hmono := Nat.mul_le_mul_right (colStep N w MB LB LBq + 9) (show w - b ≤ w by omega)
  unfold colPrice
  cost_simp
  have e : (colStep N w MB LB LBq + 9) * (w - b) = (w - b) * (colStep N w MB LB LBq + 9) := by ring
  omega

/-- **The relation matrix** (`gsRelationMatrixC`): `m` columns on monic moduli of at least `2`
coefficients, each longer than `R`, `|M_b| + |R| ≤ N`: at most `matPrice N w m MB LB LBq IB`. -/
theorem gsRelationMatrixC_cost (hP : Includes P gsRelationMatrixC.costDeps)
    {N Nb Nq MB LB LBq IB : ℕ} (hMB : MulBound P N MB) (hLB : LowBound P Nb LB)
    (hLq : LowBound P Nq LBq) (hIB : InvBound P Nq IB)
    (R : CPolynomial K) (hRq : R.val.size ≤ Nq) (moduli : Array (CPolynomial K)) (params : GuruswamiSudan.GSInterpParams)
    (hm : params.multiplicity ≤ GuruswamiSudan.interpolationWidth params)
    (hw : GuruswamiSudan.interpolationWidth params < 2 ^ 20)
    (hpar : params.messageDegree < 2 ^ 64 ∧ params.weightedDegreeBound < 2 ^ 64)
    (hmod : ∀ b < params.multiplicity, (moduli.getD b 1).monic = true ∧
      R.val.size < (moduli.getD b 1).val.size ∧ 2 ≤ (moduli.getD b 1).val.size ∧
      (moduli.getD b 1).val.size + R.val.size ≤ N ∧ (moduli.getD b 1).val.size ≤ Nb + 1)
    (hN58 : N < 2 ^ 58) :
    machineCost P gsRelationMatrixC.costIdx [encodeValue R, encodeValue moduli,
        encodeValue params] ≤
      matPrice N (GuruswamiSudan.interpolationWidth params) params.multiplicity MB LB LBq IB := by
  rw [gsRelationMatrixC.costEq P hP]
  set w := GuruswamiSudan.interpolationWidth params with hwdef
  set m := params.multiplicity with hmdef
  have := rangeLoop_cost P (by includes) m [] (by omega)
  have hl := fun b ↦ (RunsApp.of_spec (us := [encodeValue R, encodeValue moduli, encodeValue w])
    (vs := [encodeValue b]) (gsRelationMatrixC.lam0.costSpec P (by includes) R moduli w b) :
      RunsApp P (.closure gsRelationMatrixC.lam0.costIdx [encodeValue R, encodeValue moduli,
        encodeValue w]) _ _)
  have hcols := map_cost P (by includes) _ (.closure gsRelationMatrixC.lam0.costIdx
    [encodeValue R, encodeValue moduli, encodeValue w]) hl (colPrice N w MB LB LBq IB + 17)
    (List.range m) (fun b hb ↦ by
      simp only [appCost_fn, List.cons_append, List.nil_append, List.length_cons, List.length_nil]
      rw [gsRelationMatrixC.lam0.costEq P (by includes)]
      have hb' := List.mem_range.1 hb
      obtain ⟨h1, h2, h3, h4, h5⟩ := hmod b hb'
      have := gsRelationColumnC_cost P (by includes) hMB hLB hLq hIB R (moduli.getD b 1) h1 h2 h3 h4
        h5 hRq hN58 w b hw (by omega)
      omega)
  set cols := (List.map (fun b ↦ gsRelationColumnCached FFT.fftMulContext FFT.fftRawMulLowContext
    R (moduli.getD b 1) w b) (List.range m)).toArray
  have he := fun j b ↦ (RunsApp.of_spec (us := [encodeValue cols, encodeValue w])
    (vs := [encodeValue j, encodeValue b]) (gsRelationMatrixC.lam1.costSpec P (by includes) cols w
      j b) : RunsApp P (.closure gsRelationMatrixC.lam1.costIdx [encodeValue cols, encodeValue w])
        _ _)
  have hof := ofFnC_cost P (by includes) w m (by omega) (by omega) _
    (.closure gsRelationMatrixC.lam1.costIdx [encodeValue cols, encodeValue w]) he 11
    (fun j _ b _ ↦ by
      simp only [appCost_fn, List.cons_append, List.nil_append, List.length_cons, List.length_nil]
      rw [gsRelationMatrixC.lam1.costEq P (by includes)])
  simp only [List.length_range, List.length_map] at *
  have hy : GuruswamiSudan.yWeight params < 2 ^ 64 := by
    unfold GuruswamiSudan.yWeight; omega
  have hcap : GuruswamiSudan.interpolationYCap params < 2 ^ 64 := by
    unfold GuruswamiSudan.interpolationYCap; exact lt_of_le_of_lt (Nat.div_le_self _ _) hpar.2
  obtain ⟨hp1, hp2⟩ := hpar
  have hq2 := limbs_le_two (show GuruswamiSudan.interpolationYCap params + 1 < 2 ^ 128 by omega)
  unfold matPrice
  cost_simp
  have e1 : w * (m * (11 + 35) + 49) = w * (m * 46 + 49) := by ring
  have e2 : (colPrice N w MB LB LBq IB + 17 + 13) * m = m * (colPrice N w MB LB LBq IB + 30) := by ring
  omega

end

end LeanVM.Cost.Bounds.PMSolve
