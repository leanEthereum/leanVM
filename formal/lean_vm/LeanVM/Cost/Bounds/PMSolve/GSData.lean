module

public import LeanVM.Cost.Bounds.PMSolve.GSColumn
import all CompPoly.Univariate.Raw.Core
import all CompPoly.Univariate.Basic
import all CompPoly.LinearAlgebra.PolynomialMatrix.Basic
import all CompPoly.LinearAlgebra.PolynomialMatrix.Operations
import all CompPoly.Bivariate.GuruswamiSudan.Interpolation.ApproximantBasis.Basic
import all LeanVM.Protocol.Extraction.Fast.GSData

public import LeanVM.Cost.Bounds.PMLane.InterpDefs
/-!
# Bounds: the GS data, compiled

`buildGSModularDataCached fftMulContext fftRawMulLowContext R G params` (`gsDataC`): the moduli
`G, G², …, G^m` each by one product of the previous power by `G` (`gsModuliC_cost`), the relation
matrix (`gsRelationMatrixC_cost`), the shifts. **`gsDataC_cost`**: at most `dataPrice …`.
-/

namespace LeanVM.Cost.Bounds.PMSolve

open LeanVM.Cost LeanVM.Cost.Bounds LeanVM.Cost.Library LeanVM.Cost.Bounds.Decoder
open LeanVM.Cost.Extractor LeanVM.Parameters CompPoly LeanVM.Extraction.Fast
open CompPoly.PolynomialMatrix CompPoly.PolynomialMatrix.Approximant

public section

/-- A power's size: `|G^k| ≤ k·deg G + 1`. -/
theorem size_pow_le (G : CPolynomial K) (k : ℕ) : (G ^ k).val.size ≤ k * G.natDegree + 1 := by
  have h1 := LeanVM.Extraction.Fast.PMDegree.val_size_le_natDegree_add_one (G ^ k)
  have h2 : (G ^ k).natDegree ≤ k * G.natDegree := by
    rw [CPolynomial.natDegree_toPoly, CPolynomial.natDegree_toPoly G, CPolynomial.toPoly_pow]
    exact Polynomial.natDegree_pow_le
  omega

/-- The moduli's loop's states: the powers `G, …, G^(k+1)`. -/
@[expose] def powersArr (G : CPolynomial K) (k : ℕ) : Array (CPolynomial K) :=
  ((List.range (k + 1)).map fun i ↦ G ^ (i + 1)).toArray

theorem powersArr_step (G : CPolynomial K) (k : ℕ) :
    (powersArr G k).push (FFT.fftMulContext.mul ((powersArr G k).getD ((powersArr G k).size - 1) 0)
      G) = powersArr G (k + 1) := by
  have hs : (powersArr G k).size = k + 1 := by simp [powersArr]
  have hg : (powersArr G k).getD k 0 = G ^ (k + 1) := by
    rw [Array.getD_eq_getD_getElem?]
    simp [powersArr]
  rw [hs, Nat.add_sub_cancel, hg, FFT.fftMulContext.mul_eq_mul, ← pow_succ]
  simp only [powersArr, List.push_toArray]
  congr 1
  conv_rhs => rw [List.range_succ]
  rw [List.map_append]
  rfl

variable (P : MachineProgram)

/-- The moduli's loop, `n` steps from the powers up to `G^(k+1)`. -/
theorem moduliLoopC_cost (hP : Includes P gsModuliC.costDeps) {N MB : ℕ} (hMB : MulBound P N MB)
    (G : CPolynomial K) (m : ℕ) (hm : m < 2 ^ 30) (hGN : m * G.natDegree + 1 ≤ N) :
    ∀ (n k : ℕ), k + 1 + n ≤ m → ∀ l : List ℕ, l.length = n →
      machineCost P Auto.LeanVM.Cost.LoopLib.listForInId.c520.costIdx
          [.closure gsModuliC.lam0.costIdx [encodeValue G], encodeValue l,
            encodeValue (powersArr G k)] ≤ (MB + m + 33) * n + 3 := by
  have hf := fun x s ↦ (RunsApp.of_spec (us := [encodeValue G]) (vs := [encodeValue x,
    encodeValue s]) (gsModuliC.lam0.costSpec P (by includes) G x s) :
      RunsApp P (.closure gsModuliC.lam0.costIdx [encodeValue G]) _ _)
  intro n
  induction n with
  | zero =>
    intro k _ l hl
    rw [List.length_eq_zero_iff.1 hl, Auto.LeanVM.Cost.LoopLib.listForInId.c520.costEq P
      (by includes) _ _ hf]
    simp
  | succ n ih =>
    intro k hk l hl
    obtain ⟨x, l', rfl⟩ : ∃ x l', l = x :: l' := by
      cases l with
      | nil => simp at hl
      | cons x l' => exact ⟨x, l', rfl⟩
    rw [Auto.LeanVM.Cost.LoopLib.listForInId.c520.costEq_cons P (by includes) _ _ hf]
    simp only [appCost_fn, List.cons_append, List.nil_append]
    rw [gsModuliC.lam0.costEq P (by includes)]
    have hs : (powersArr G k).size = k + 1 := by simp [powersArr]
    have hlast : ((powersArr G k).getD ((powersArr G k).size - 1) 0).val.size ≤
        (k + 1) * G.natDegree + 1 := by
      rw [hs, Nat.add_sub_cancel, Array.getD_eq_getD_getElem?]
      simp only [powersArr, List.getElem?_toArray, List.getElem?_map,
        List.getElem?_range (show k < k + 1 by omega), Option.map_some, Option.getD_some]
      exact size_pow_le G (k + 1)
    have hG : G.val.size ≤ G.natDegree + 1 := by
      have := size_pow_le G 1
      simp only [pow_one, one_mul] at this
      exact this
    have hk2 := Nat.mul_le_mul_right G.natDegree (show k + 2 ≤ m by omega)
    have hk2e : (k + 2) * G.natDegree = (k + 1) * G.natDegree + G.natDegree := by ring
    have := hMB ((powersArr G k).getD ((powersArr G k).size - 1) 0) G (by omega)
    have hnext := ih (k + 1) (by omega) l' (by simpa using hl)
    rw [← powersArr_step] at hnext
    simp only [pure]
    cost_simp
    have e : (MB + m + 33) * (n + 1) = (MB + m + 33) * n + MB + m + 33 := by ring
    omega


theorem moduliForIn_size (G : CPolynomial K) (m : ℕ) (hm : m ≠ 0) :
    (forIn (m := Id) [1:m] #[G] fun _ s ↦
      have ascending := s
      have ascending := ascending.push
        (FFT.fftMulContext.mul (ascending.getD (ascending.size - 1) 0) G)
      pure (ForInStep.yield ascending)).size = m := by
  have h := CompPoly.GuruswamiSudan.ApproximantBasis.gsModuli_size FFT.fftMulContext G m
  rw [CompPoly.GuruswamiSudan.ApproximantBasis.gsModuli] at h
  simp [hm] at h
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size, Nat.add_sub_cancel,
    Nat.div_one]
  have key := List.forIn_pure_yield_eq_foldl (m := Id) (l := List.range' 1 (m - 1))
    (fun (_ : ℕ) (s : Array (CPolynomial K)) ↦
      s.push (FFT.fftMulContext.mul (s.getD (s.size - 1) 0) G)) #[G]
  exact (congrArg Array.size key).trans (by simp only [Array.getD_eq_getD_getElem?]; exact h)


/-- **The moduli** (`gsModuli`, `m ≥ 1`): `m − 1` products of a power by `G`, the array
reversed: at most `(MB + m + 33)·(m − 1) + 33·m + 54`. -/
theorem gsModuliC_cost (hP : Includes P gsModuliC.costDeps) {N MB : ℕ} (hMB : MulBound P N MB)
    (G : CPolynomial K) (m : ℕ) (hm1 : 1 ≤ m) (hm : m < 2 ^ 30)
    (hGN : m * G.natDegree + 1 ≤ N) :
    machineCost P gsModuliC.costIdx [encodeValue G, encodeValue m] ≤
      (MB + m + 33) * (m - 1) + 33 * m + 54 := by
  rw [gsModuliC.costEq P hP]
  have hm0 : (m == 0) = false := by simp; omega
  rw [hm0]
  simp only [Bool.false_eq_true, ↓reduceIte]
  rw [Auto.Std.Legacy.Range.size.c523.costEq P (by includes)]
  have hX := moduliForIn_size G m (by omega)
  have hsz : [1:m].size = m - 1 := by simp [Std.Legacy.Range.size]
  have hst : [1:m].start = 1 := rfl
  have hsp : [1:m].step = 1 := rfl
  have hsto : [1:m].stop = m := rfl
  rw [hsz, hst, hsp, hsto]
  have := rangeC_cost P (by includes) (m - 1) 1 (by omega)
  have h0 : powersArr G 0 = #[G] := by simp [powersArr]
  have hloop := moduliLoopC_cost P (by includes) hMB G m hm hGN (m - 1) 0 (by omega)
    (List.range' 1 (m - 1)) (by simp)
  rw [h0] at hloop
  have := reverseAux_cost P (by includes)
    (forIn (m := Id) [1:m] #[G] fun _ s ↦
      have ascending := s
      have ascending := ascending.push
        (FFT.fftMulContext.mul (ascending.getD (ascending.size - 1) 0) G)
      pure (ForInStep.yield ascending)).toList []
  simp only [Array.length_toList, List.length_reverse, hX] at *
  cost_simp
  omega


theorem size_of_monic {p : CPolynomial K} (hp : p.monic = true) : p.val.size = p.natDegree + 1 := by
  have h1 : p.val.size ≠ 0 := by
    intro h0
    simp [CPolynomial.monic, CPolynomial.leadingCoeff, Array.getLastD, h0] at hp
  unfold CPolynomial.natDegree
  generalize p.val.size = s at h1 ⊢
  cases s with
  | zero => omega
  | succ k => rfl

theorem monic_pow' {G : CPolynomial K} (hG : G.monic = true) (k : ℕ) : (G ^ k).monic = true := by
  rw [CPolynomial.monic_toPoly_iff, CPolynomial.toPoly_pow]
  exact ((CPolynomial.monic_toPoly_iff G).1 hG).pow k

theorem natDegree_pow' {G : CPolynomial K} (hG : G.monic = true) (k : ℕ) :
    (G ^ k).natDegree = k * G.natDegree := by
  rw [CPolynomial.natDegree_toPoly, CPolynomial.natDegree_toPoly G, CPolynomial.toPoly_pow]
  exact ((CPolynomial.monic_toPoly_iff G).1 hG).natDegree_pow k

theorem vanishingFast_monicB {F : Type*} [Field F] [BEq F] [LawfulBEq F] (xs : Array F) :
    (vanishingFast xs).monic = true :=
  (CPolynomial.monic_toPoly_iff _).2 (monic_vanishingFast xs)

theorem vanishingFast_monicK (xs : Array K) :
    @CPolynomial.monic K BF64.instZero BF64.instOne instBEqBF64 (vanishingFast xs) = true :=
  vanishingFast_monicB xs

/-- **The GS data** (`buildGSModularDataCached fftMulContext fftRawMulLowContext R G params`):
on a monic `G` of degree `n ≥ 1`, `|R| ≤ n`, `1 ≤ m ≤ w`, `(m + 1)·n + 1 ≤ N`: at most
`dataPrice N m w MB LB LBq IB`, the products within `MB` (results of at most `N`
coefficients), the back-products within `LB` (precision `m·n ≤ Nb`), the quotients and the inverses
within `LBq`, `IB` (precision `n ≤ Nq`). -/
theorem gsDataC_cost (hP : Includes P gsDataC.costDeps)
    {N Nb Nq MB LB LBq IB : ℕ} (hMB : MulBound P N MB) (hLB : LowBound P Nb LB)
    (hLq : LowBound P Nq LBq) (hIB : InvBound P Nq IB)
    (R G : CPolynomial K) (params : GuruswamiSudan.GSInterpParams) (hG : G.monic = true)
    (hn1 : 1 ≤ G.natDegree) (hR : R.val.size ≤ G.natDegree) (hm1 : 1 ≤ params.multiplicity)
    (hm : params.multiplicity ≤ GuruswamiSudan.interpolationWidth params)
    (hw : GuruswamiSudan.interpolationWidth params < 2 ^ 20)
    (hpar : params.messageDegree < 2 ^ 64 ∧ params.weightedDegreeBound < 2 ^ 64)
    (hN : (params.multiplicity + 1) * G.natDegree + 1 ≤ N) (hNb : params.multiplicity * G.natDegree ≤ Nb)
    (hNq : G.natDegree ≤ Nq) (hN58 : N < 2 ^ 58) :
    machineCost P gsDataC.costIdx [encodeValue R, encodeValue G, encodeValue params] ≤
      dataPrice N params.multiplicity (GuruswamiSudan.interpolationWidth params) MB LB LBq IB := by
  rw [gsDataC.costEq P hP]
  have hj : (params.multiplicity + 1) * G.natDegree =
      params.multiplicity * G.natDegree + G.natDegree := by ring
  have hmn : params.multiplicity * G.natDegree + 1 ≤ N := by omega
  have := gsModuliC_cost P (by includes) hMB G params.multiplicity hm1 (by omega) hmn
  have hmat := gsRelationMatrixC_cost P (by includes) hMB hLB hLq hIB R (by omega)
    (CompPoly.GuruswamiSudan.ApproximantBasis.gsModuli FFT.fftMulContext G params.multiplicity)
    params hm hw hpar (fun b hb ↦ by
      rw [CompPoly.GuruswamiSudan.ApproximantBasis.gsModuli_getD_one _ _ hb]
      have hmo := monic_pow' hG (params.multiplicity - b)
      have hs := size_of_monic hmo
      rw [natDegree_pow' hG] at hs
      have hk := Nat.mul_le_mul_right G.natDegree (show params.multiplicity - b ≤
        params.multiplicity by omega)
      have hk1 := Nat.mul_le_mul_right G.natDegree (show 1 ≤ params.multiplicity - b by omega)
      refine ⟨hmo, by omega, by omega, by omega, by omega⟩) hN58
  have := rangeLoop_cost P (by includes) (GuruswamiSudan.interpolationWidth params) [] (by omega)
  have hl := fun j ↦ (RunsApp.of_spec (us := [encodeValue params]) (vs := [encodeValue j])
    (LeanVM.Cost.Extractor.gsDataC.lam0.costSpec P (by includes)
      params j) : RunsApp P (.closure
        LeanVM.Cost.Extractor.gsDataC.lam0.costIdx
        [encodeValue params]) _ _)
  have hy : GuruswamiSudan.yWeight params < 2 ^ 64 := by
    unfold GuruswamiSudan.yWeight; omega
  have hcap : GuruswamiSudan.interpolationYCap params < 2 ^ 64 := by
    unfold GuruswamiSudan.interpolationYCap; exact lt_of_le_of_lt (Nat.div_le_self _ _) hpar.2
  have := map_cost P (by includes) _ (.closure
    LeanVM.Cost.Extractor.gsDataC.lam0.costIdx [encodeValue params])
    hl 8 (List.range (GuruswamiSudan.interpolationWidth params)) (fun j hj ↦ by
      simp only [appCost_fn, List.cons_append, List.nil_append, List.length_cons, List.length_nil]
      rw [LeanVM.Cost.Extractor.gsDataC.lam0.costEq P (by includes)]
      have := List.mem_range.1 hj
      have := limbs_le_two (show j * GuruswamiSudan.yWeight params < 2 ^ 128 by
        have := Nat.mul_le_mul (show j ≤ 2 ^ 20 by omega)
          (show GuruswamiSudan.yWeight params ≤ 2 ^ 64 by omega)
        omega)
      cost_simp
      omega)
  obtain ⟨hp1, hp2⟩ := hpar
  have hq2 := limbs_le_two (show GuruswamiSudan.interpolationYCap params + 1 < 2 ^ 128 by omega)
  simp only [List.length_range, List.length_map] at *
  unfold dataPrice
  cost_simp
  omega

end

end LeanVM.Cost.Bounds.PMSolve
