module

public import LeanVM.Cost.Bounds.PMSolve.GSData
public import LeanVM.Cost.Bounds.Decoder.Interpolate
import all CompPoly.Univariate.Raw.Core
import all CompPoly.Univariate.Basic
import all CompPoly.LinearAlgebra.PolynomialMatrix.Basic
import all CompPoly.LinearAlgebra.PolynomialMatrix.Operations
import all CompPoly.Bivariate.CoeffRows
import all CompPoly.Bivariate.GuruswamiSudan.Interpolation.Basic
import all CompPoly.Bivariate.GuruswamiSudan.Interpolation.ApproximantBasis.Basic
import all LeanVM.Protocol.Extraction.Fast.GSData

public import LeanVM.Cost.Bounds.PMLane.InterpDefs
/-!
# Bounds: the lanes' approximant-basis interpolation, compiled

`interpolateDistinctWith pmSolver points params` (`interpolatePMC`): the vanishing polynomial and
Horner's interpolant (the chain's, `vanishingC_cost`, `interpolateC_cost`), the GS data
(`gsDataC_cost`), the certified solve (`certifiedSolveC_cost`), the least row
(`leastShiftedDegreeChoiceC_cost`), the row as a bivariate polynomial and its normalization (the
chain's, `ofCoeffRowC_cost`, `normalizeLeeFastC_cost`).

**`interpolatePMC_cost`**: at most `interpPMCost p L N n m w W MB LB LBq IB`.
-/

namespace LeanVM.Cost.Bounds.PMSolve

open LeanVM.Cost LeanVM.Cost.Bounds LeanVM.Cost.Library LeanVM.Cost.Bounds.Decoder
open LeanVM.Cost.Extractor LeanVM.Parameters CompPoly LeanVM.Extraction.Fast
open CompPoly.PolynomialMatrix CompPoly.PolynomialMatrix.Approximant
open LeanVM.Cost.Bounds.PMBasis

public section

/-- The best choice's invariant: a degree at most `B`. -/
@[expose] def ChoiceInv (B : ℕ) (best : Option (RowChoice K)) : Prop :=
  ∀ c, best = some c → c.degree ≤ B ∧ c.index < 2 ^ 62

theorem choiceInv_step {B : ℕ} {M : PolynomialMatrix K} {shift : Array ℕ}
    {best : Option (RowChoice K)} {i : ℕ} (hbest : ChoiceInv B best)
    (hdeg : ∀ d, rowShiftedDegree? (M.getD i #[]) shift = some d → d ≤ B) (hi : i < 2 ^ 62) :
    ChoiceInv B (M.leastShiftedDegreeRowStep? shift best i) := by
  intro c hc
  simp only [leastShiftedDegreeRowStep?] at hc
  rcases hd : rowShiftedDegree? (M.getD i #[]) shift with _ | d
  · rw [hd] at hc
    exact hbest c hc
  · rw [hd] at hc
    have := hdeg d hd
    cases best with
    | none =>
      simp only [Option.some.injEq] at hc
      subst hc
      exact ⟨this, hi⟩
    | some cur =>
      simp only at hc
      split at hc
      · simp only [Option.some.injEq] at hc
        subst hc
        exact ⟨this, hi⟩
      · exact hbest c hc

variable (P : MachineProgram)

/-- **The least row** (`leastShiftedDegreeChoice?`): on `r` rows of at most `C` entries of at most
`D` coefficients, shifts at most `S`: at most `(84·C + 98)·r + 20`. -/
theorem leastShiftedDegreeChoiceC_cost (hP : Includes P leastShiftedDegreeChoiceC.costDeps)
    {C D S : ℕ} (hC : C < 2 ^ 62) (hDS : D + S < 2 ^ 62) (M : PolynomialMatrix K)
    (hr : M.size < 2 ^ 62) (hrows : ∀ row ∈ M.toList, RowWithin C D row) (shift : Array ℕ)
    (hS : ∀ j, shift.getD j 0 ≤ S) :
    machineCost P leastShiftedDegreeChoiceC.costIdx [encodeValue M, encodeValue shift] ≤
      (84 * C + 98) * M.size + 20 := by
  rw [leastShiftedDegreeChoiceC.costEq P hP]
  have hrw : ∀ i, RowWithin C D (M.getD i #[]) := by
    intro i
    rw [Array.getD_eq_getD_getElem?]
    cases h : M[i]? with
    | none => exact ⟨by simp, by simp⟩
    | some row => exact hrows row (Array.mem_toList_iff.2 (Array.mem_of_getElem? h))
  have := rangeLoop_cost P (by includes) M.size [] (by omega)
  have hf := listFoldl_le P (by includes) _
    (.closure leastShiftedDegreeChoiceC.lam0.costIdx [encodeValue M, encodeValue shift])
    (fun best i ↦ RunsApp.of_spec (us := [encodeValue M, encodeValue shift])
      (vs := [encodeValue best, encodeValue i])
      (leastShiftedDegreeChoiceC.lam0.costSpec P (by includes) M shift best i))
    (84 * C + 72) (ChoiceInv (D + S)) (List.range M.size) none (fun c hc ↦ by cases hc)
    (fun best hbest i hi ↦ by
      rw [List.mem_range] at hi
      have hdeg : ∀ d, rowShiftedDegree? (M.getD i #[]) shift = some d → d ≤ D + S :=
        fun d hd ↦ rowShiftedDegree?_le (hrw i) hS hd
      refine ⟨choiceInv_step hbest hdeg (by omega), ?_⟩
      · simp only [appCost_fn, List.cons_append, List.nil_append, List.length_cons, List.length_nil]
        rw [leastShiftedDegreeChoiceC.lam0.costEq P (by includes),
          Auto.CompPoly.PolynomialMatrix.leastShiftedDegreeRowStep?.c584.costEq P (by includes)]
        have := rowShiftedDegree_cost P (by includes) hC (by omega) (M.getD i #[]) (hrw i) shift hS
        generalize M.getD i #[] = row at this hdeg ⊢
        generalize hd : rowShiftedDegree? row shift = o
        cases o with
        | none => dsimp only; omega
        | some d =>
          have := hdeg d hd
          cases best with
          | none => dsimp only; omega
          | some cur =>
            have := hbest cur rfl
            dsimp only
            rw [Auto.CompPoly.PolynomialMatrix.betterRowChoice.c585.costEq P (by includes)]
            cost_simp
            split_ifs <;> omega)
  simp only [List.length_range] at hf
  have e : (84 * C + 98) * M.size = (84 * C + 72 + 11) * M.size + 15 * M.size := by ring
  omega


/-! ## The GS data's sizes -/

/-- **The GS data's equation**: `w` relation rows of width `m`, `m` monic moduli `G^(m−b)` of at
most `m·n + 1` coefficients, each entry shorter than its column's modulus. -/
theorem gsEquation_sizes (R G : CPolynomial K) (params : GuruswamiSudan.GSInterpParams)
    (hG : G.monic = true) (hn1 : 1 ≤ G.natDegree)
    (hw : GuruswamiSudan.interpolationWidth params < 2 ^ 29) (hm : params.multiplicity < 2 ^ 29)
    (hQ : params.multiplicity * G.natDegree + 1 < 2 ^ 60) :
    let eq := GuruswamiSudan.ApproximantBasis.modularEquation
      (buildGSModularDataCached pmSolver.mulContext FFT.fftRawMulLowContext R G params)
    LiftSizes eq (GuruswamiSudan.interpolationWidth params) params.multiplicity
      (params.multiplicity * G.natDegree + 1) ∧
      MatrixWidth eq.matrix = params.multiplicity := by
  intro eq
  have heq : eq = GuruswamiSudan.ApproximantBasis.modularEquation
      (GuruswamiSudan.ApproximantBasis.buildGSModularDataWithRG FFT.fftMulContext FFT.fftModContext
        R G params) := by
    show GuruswamiSudan.ApproximantBasis.modularEquation (buildGSModularDataCached
      FFT.fftMulContext FFT.fftRawMulLowContext R G params) = _
    rw [buildGSModularDataCached_eq _ _ FFT.fftModContext]
  rw [heq]
  have hGm : G.toPoly.Monic := (CPolynomial.monic_toPoly_iff G).1 hG
  refine ⟨⟨GuruswamiSudan.ApproximantBasis.gsRelationMatrixWithModuli_size _ _ _ _ _,
    GuruswamiSudan.ApproximantBasis.gsModuli_size _ _ _, hw, hm, hQ, fun j hj ↦ ?_,
    fun i hi j hj ↦ ?_⟩,
    GuruswamiSudan.ApproximantBasis.gsRelationMatrixWithModuli_matrixWidth _ _ _ _ _⟩
  · change ((GuruswamiSudan.ApproximantBasis.gsModuli FFT.fftMulContext G
        params.multiplicity).getD j 0).monic = true ∧
      ((GuruswamiSudan.ApproximantBasis.gsModuli FFT.fftMulContext G
        params.multiplicity).getD j 0).val.size ≤ params.multiplicity * G.natDegree + 1
    rw [GuruswamiSudan.ApproximantBasis.gsModuli_getD _ _ hj]
    have hmo := monic_pow' hG (params.multiplicity - j)
    have hs := size_of_monic hmo
    rw [natDegree_pow' hG] at hs
    have := Nat.mul_le_mul_right G.natDegree (show params.multiplicity - j ≤ params.multiplicity
      by omega)
    exact ⟨hmo, by omega⟩
  · have h := natDegree_gsRelationMatrix_entry_lt FFT.fftMulContext FFT.fftModContext R G params
      hGm hn1 hi hj
    have h1 := LeanVM.Extraction.Fast.PMDegree.val_size_le_natDegree_add_one
      (rowGet ((GuruswamiSudan.ApproximantBasis.gsRelationMatrixWithModuli FFT.fftMulContext
        FFT.fftModContext R (GuruswamiSudan.ApproximantBasis.gsModuli FFT.fftMulContext G
          params.multiplicity) params).getD i #[]) j)
    have hmo : ((GuruswamiSudan.ApproximantBasis.gsModuli FFT.fftMulContext G
        params.multiplicity).getD j 0).monic = true := by
      rw [GuruswamiSudan.ApproximantBasis.gsModuli_getD _ _ hj]
      exact monic_pow' hG _
    have h2 := size_of_monic hmo
    show (rowGet ((GuruswamiSudan.ApproximantBasis.gsRelationMatrixWithModuli FFT.fftMulContext
        FFT.fftModContext R (GuruswamiSudan.ApproximantBasis.gsModuli FFT.fftMulContext G
          params.multiplicity) params).getD i #[]) j).val.size <
      ((GuruswamiSudan.ApproximantBasis.gsModuli FFT.fftMulContext G
        params.multiplicity).getD j 0).val.size
    omega

/-- The GS shift `j·(k − 1)`, `j < w`: at most `W`. -/
theorem interpolationShifts_le (params : GuruswamiSudan.GSInterpParams) (j : ℕ) :
    (GuruswamiSudan.interpolationShifts params).getD j 0 ≤ params.weightedDegreeBound := by
  unfold GuruswamiSudan.interpolationShifts CBivariate.weightedDegreeShift
  rw [Array.getD_eq_getD_getElem?]
  by_cases hj : j < GuruswamiSudan.interpolationWidth params
  · simp only [List.getElem?_toArray, List.getElem?_map, List.getElem?_range hj, Option.map_some,
      Option.getD_some]
    have h1 : j ≤ GuruswamiSudan.interpolationYCap params := by
      unfold GuruswamiSudan.interpolationWidth at hj; omega
    have h2 : GuruswamiSudan.interpolationYCap params * GuruswamiSudan.yWeight params ≤
        params.weightedDegreeBound := by
      unfold GuruswamiSudan.interpolationYCap; exact Nat.div_mul_le_self _ _
    exact (Nat.mul_le_mul_right _ h1).trans h2
  · rw [List.getElem?_toArray, List.getElem?_map, List.getElem?_eq_none (by simpa using hj)]
    simp

theorem interpolationShifts_size (params : GuruswamiSudan.GSInterpParams) :
    (GuruswamiSudan.interpolationShifts params).size = GuruswamiSudan.interpolationWidth params := by
  simp [GuruswamiSudan.interpolationShifts, CBivariate.weightedDegreeShift]


/-- **The certified solve's rows**: at most `w + m` rows of `w` entries of at most `o + 2`
coefficients, `o` the certified problem's maximal order. -/
theorem certifiedRows_sizes (equation : ModularEquation K) (shift : Array ℕ) (bound : ℕ)
    {w m Q : ℕ} (hs : LiftSizes equation w m Q) :
    let M := certifiedSolutionBasis FFT.fftModContext (popovEvalPMBasisContext FFT.novelTransform
      FFT.fftMulContext FFT.fftMulLowContext 1) equation shift bound
    let o := maxOrder (fullWindowExactNullspaceProblem FFT.fftModContext equation bound)
    M.size ≤ w + m ∧ ∀ row ∈ M.toList, RowWithin w (o + 2) row := by
  intro M o
  obtain ⟨hw, hm, -, -, -, hmod, -⟩ := hs
  have hmonic : ∀ j < equation.moduli.size, (equation.moduli.getD j 0).monic = true :=
    fun j hj ↦ (hmod j (by omega)).1
  obtain ⟨-, -, -, hpsize⟩ := liftProblem_sizes equation bound hmonic
  have hsW : equation.solutionWidth = w := hw
  obtain ⟨hBsize, hBrows⟩ := certBasis_spec (fullWindowExactNullspaceProblem FFT.fftModContext
    equation bound) (certShift equation shift bound)
  refine ⟨?_, fun row hrow ↦ ?_⟩
  · show (certifiedSolutionBasis _ _ equation shift bound).size ≤ w + m
    unfold certifiedSolutionBasis
    split
    · simp only [principalSolutionRows, Array.size_map]
      exact Array.size_filter_le.trans (by rw [hBsize, hpsize]; omega)
    · simp
  · obtain ⟨-, bRow, hbMem, -, rfl⟩ := mem_certifiedSolutionBasis.1 hrow
    obtain ⟨-, hd⟩ := hBrows bRow hbMem
    refine ⟨by simp [hsW], fun e he ↦ ?_⟩
    simp only [List.mem_toArray, List.mem_map, List.mem_range] at he
    obtain ⟨j, -, rfl⟩ := he
    have := LeanVM.Extraction.Fast.PMDegree.val_size_le_natDegree_add_one (rowGet bRow j)
    have := hd j
    omega

/-- The certified problem's maximal order on the GS data: `m·n + bound + 2`. -/
theorem gsEquation_maxOrder (R G : CPolynomial K) (params : GuruswamiSudan.GSInterpParams)
    (hG : G.monic = true) (hm : 0 < params.multiplicity) (bound : ℕ) :
    maxOrder (fullWindowExactNullspaceProblem FFT.fftModContext
      (GuruswamiSudan.ApproximantBasis.modularEquation
        (buildGSModularDataCached pmSolver.mulContext FFT.fftRawMulLowContext R G params)) bound) =
      params.multiplicity * G.natDegree + bound + 2 := by
  have h : buildGSModularDataCached pmSolver.mulContext FFT.fftRawMulLowContext R G params =
      GuruswamiSudan.ApproximantBasis.buildGSModularDataWithRG FFT.fftMulContext FFT.fftModContext
        R G params := buildGSModularDataCached_eq _ _ _ _ _ _
  rw [h]
  exact gsProblem_maxOrder _ _ R G params ((CPolynomial.monic_toPoly_iff G).1 hG) bound hm

/-- **The lanes' interpolation, compiled** (`interpolatePMC`, `interpolateDistinctWith pmSolver`):
on `n` points, `k > 1`, at most `interpPMCost p L N n m w W MB LB LBq IB`, `N = (m + 1)·n + 1`,
given the products' prices (the products of at most `N` coefficients within `MB`, the truncated
products at precision `m·n` within `LB`, at precision `n` within `LBq`, Newton's inverse at
precision `n` within `IB`) and the PM-basis core's price at the leaf price `L`
(`PMCoreCostAt`). -/
theorem interpolatePMC_cost (hP : Includes P interpolatePMC.costDeps) (p : PMPrices)
    {MB LB LBq IB : ℕ} (points : Array (K × K)) (params : GuruswamiSudan.GSInterpParams)
    (hMB : MulBound P ((params.multiplicity + 1) * points.size + 1) MB)
    (hLB : LowBound P (params.multiplicity * points.size) LB)
    (hLq : LowBound P points.size LBq) (hIB : InvBound P points.size IB)
    {L SB : ℕ}
    (hcore : PMCoreCostAt P p L (GuruswamiSudan.interpolationWidth params + params.multiplicity)
      params.multiplicity SB)
    (hSB : params.weightedDegreeBound + params.weightedDegreeBound + 1 +
      2 * (params.multiplicity * points.size + 1 + params.weightedDegreeBound + 2) ≤ SB)
    (h37 : 3 * (params.multiplicity * points.size + 1 + params.weightedDegreeBound + 2) ≤ 2 ^ 37)
    (hsz : InterpSizes points.size params)
    (hpm : PMInterpSizes points.size params) (hk : 1 < params.messageDegree) :
    machineCost P interpolatePMC.costIdx [encodeValue points, encodeValue params] ≤
      interpPMCost p L ((params.multiplicity + 1) * points.size + 1) points.size
        params.multiplicity (GuruswamiSudan.interpolationWidth params)
        params.weightedDegreeBound MB LB LBq IB := by
  obtain ⟨hn55, hW60, hk64, hyW, hcap, hm55, -⟩ := hsz
  obtain ⟨hn1, hm1, hmw, hw20, hN45, hW40⟩ := hpm
  rw [interpolatePMC.costEq P hP]
  simp only [show ¬params.messageDegree ≤ 1 by omega, ↓reduceIte]
  -- G and R
  have hxs : (points.map fun point ↦ point.1).size = points.size := Array.size_map ..
  have hGm0 := vanishingFast_monicK (points.map fun point ↦ point.1)
  have hGm : (vanishingFast (points.map fun point ↦ point.1)).monic = true := hGm0
  have hGn := natDegree_vanishingFast (points.map fun point ↦ point.1)
  rw [hxs] at hGn
  have hGs := vanishingFast_size_le (points.map fun point ↦ point.1)
  rw [hxs] at hGs
  have hRs := interpolate_size_le (CPolynomial.BatchEvalContext.horner K) points
  have := vanishingC_cost P (by includes) (points.map fun point ↦ point.1) (by omega)
  rw [hxs] at this
  have := interpolateC_cost P (by includes) (vanishingFast (points.map fun point ↦ point.1)) points
    (by omega) (by omega)
  have hl := fun pt ↦ RunsApp.of_spec (us := []) (vs := [encodeValue pt])
    (LeanVM.Cost.Extractor.interpolatePMC.lam0.costSpec P (by includes) pt)
  have := map_cost P (by includes) _
    (.closure LeanVM.Cost.Extractor.interpolatePMC.lam0.costIdx []) hl 2
    points.toList (fun pt _ ↦ by
      simp only [appCost_fn, List.nil_append, List.length_nil]
      rw [LeanVM.Cost.Extractor.interpolatePMC.lam0.costEq P (by includes)])
  -- the GS data
  have hInc : Includes P gsDataC.costDeps := by includes
  have a1 : 1 ≤ (vanishingFast (points.map fun point ↦ point.1)).natDegree := by omega
  have a2 : (CPolynomial.interpolateCoefficientFormWithVanishing (CPolynomial.BatchEvalContext.horner K)
      (vanishingFast (points.map fun point ↦ point.1)) points).val.size ≤
      (vanishingFast (points.map fun point ↦ point.1)).natDegree := by omega
  have a3 : params.weightedDegreeBound < 2 ^ 64 := by omega
  have a4 : (params.multiplicity + 1) * (vanishingFast (points.map fun point ↦ point.1)).natDegree + 1 ≤
      (params.multiplicity + 1) * points.size + 1 := by rw [hGn]
  have a5 : params.multiplicity * (vanishingFast (points.map fun point ↦ point.1)).natDegree ≤
      params.multiplicity * points.size := by rw [hGn]
  have a6 : (vanishingFast (points.map fun point ↦ point.1)).natDegree ≤ points.size := by rw [hGn]
  have a7 : (params.multiplicity + 1) * points.size + 1 < 2 ^ 58 := by omega
  have hdata := gsDataC_cost P hInc hMB hLB hLq hIB
    (CPolynomial.interpolateCoefficientFormWithVanishing (CPolynomial.BatchEvalContext.horner K)
      (vanishingFast (points.map fun point ↦ point.1)) points)
    (vanishingFast (points.map fun point ↦ point.1)) params
  replace hdata := hdata hGm a1 a2 hm1 hmw hw20 ⟨hk64, a3⟩ a4 a5 a6 a7
  -- the equation, the certified solve
  have hmn : params.multiplicity * points.size + 1 < 2 ^ 45 := by
    have : (params.multiplicity + 1) * points.size = params.multiplicity * points.size +
      points.size := by ring
    omega
  have a8 : params.multiplicity * (vanishingFast (points.map fun point ↦ point.1)).natDegree + 1 <
      2 ^ 60 := by rw [hGn]; omega
  have a9 : GuruswamiSudan.interpolationWidth params < 2 ^ 29 := by omega
  have a10 : params.multiplicity < 2 ^ 29 := by omega
  have hEq := gsEquation_sizes
    (CPolynomial.interpolateCoefficientFormWithVanishing (CPolynomial.BatchEvalContext.horner K)
      (vanishingFast (points.map fun point ↦ point.1)) points)
    (vanishingFast (points.map fun point ↦ point.1)) params
  replace hEq := hEq hGm a1 a9 a10 a8
  obtain ⟨hL, hMW⟩ := hEq
  rw [hGn] at hL
  have ho := gsEquation_maxOrder
    (CPolynomial.interpolateCoefficientFormWithVanishing (CPolynomial.BatchEvalContext.horner K)
      (vanishingFast (points.map fun point ↦ point.1)) points)
    (vanishingFast (points.map fun point ↦ point.1)) params
  replace ho := ho hGm (Nat.lt_of_lt_of_le Nat.zero_lt_one hm1) params.weightedDegreeBound
  rw [hGn] at ho
  have hshift : (buildGSModularDataCached pmSolver.mulContext FFT.fftRawMulLowContext
      (CPolynomial.interpolateCoefficientFormWithVanishing (CPolynomial.BatchEvalContext.horner K)
        (vanishingFast (points.map fun point ↦ point.1)) points)
      (vanishingFast (points.map fun point ↦ point.1)) params).shift =
      GuruswamiSudan.interpolationShifts params := rfl
  rw [hshift, solveWindow_some]
  have hsolve := certifiedSolveC_cost P (by includes) p hcore _ (GuruswamiSudan.interpolationShifts
    params) params.weightedDegreeBound hL (by rw [hMW]; omega) (interpolationShifts_size params)
    (interpolationShifts_le params) (by omega) (by omega) (by omega) hSB h37
  rw [ho] at hsolve
  -- the least row
  set eqn := GuruswamiSudan.ApproximantBasis.modularEquation (buildGSModularDataCached
    pmSolver.mulContext FFT.fftRawMulLowContext
    (CPolynomial.interpolateCoefficientFormWithVanishing (CPolynomial.BatchEvalContext.horner K)
      (vanishingFast (points.map fun point ↦ point.1)) points)
    (vanishingFast (points.map fun point ↦ point.1)) params) with heqn
  have hMeq : pmSolver.solutionBasis eqn (GuruswamiSudan.interpolationShifts params)
      (some params.weightedDegreeBound) = certifiedSolutionBasis FFT.fftModContext
      (popovEvalPMBasisContext FFT.novelTransform FFT.fftMulContext FFT.fftMulLowContext 1) eqn
      (GuruswamiSudan.interpolationShifts params) params.weightedDegreeBound := rfl
  rw [hMeq]
  obtain ⟨hMs, hMrows⟩ := certifiedRows_sizes eqn (GuruswamiSudan.interpolationShifts params)
    params.weightedDegreeBound hL
  rw [ho] at hMrows
  set M := certifiedSolutionBasis FFT.fftModContext
      (popovEvalPMBasisContext FFT.novelTransform FFT.fftMulContext FFT.fftMulLowContext 1) eqn
      (GuruswamiSudan.interpolationShifts params) params.weightedDegreeBound with hMdef
  have hlc := leastShiftedDegreeChoiceC_cost P (by includes) (C := GuruswamiSudan.interpolationWidth
    params) (D := params.multiplicity * points.size + params.weightedDegreeBound + 2 + 2)
    (S := params.weightedDegreeBound) (by omega) (by omega) M (by omega) hMrows
    (GuruswamiSudan.interpolationShifts params) (interpolationShifts_le params)
  -- the row, normalized
  have hNS : NormSizes params (params.multiplicity * points.size + params.weightedDegreeBound + 2 + 2) :=
    ⟨hW60, hk64, hyW, by omega⟩
  have hcase : ∀ c, M.leastShiftedDegreeChoice? (GuruswamiSudan.interpolationShifts params) = some c →
      max (limbCount c.degree) (limbCount params.weightedDegreeBound) +
        (if c.degree ≤ params.weightedDegreeBound then
          machineCost P ofCoeffRowC.costIdx [encodeValue c.row] +
            machineCost P Auto.LeanVM.Extraction.Fast.normalizeLeeFast.c629.costIdx
              [encodeValue params, encodeValue (CBivariate.ofCoeffRow c.row)] + 5
        else 1) + 8 ≤
      (3 * (params.multiplicity * points.size + params.weightedDegreeBound + 2 + 2) + 32) *
        GuruswamiSudan.interpolationWidth params + normBound params.weightedDegreeBound
          (GuruswamiSudan.interpolationWidth params) + 30 := by
    intro c hc
    obtain ⟨hidx, hrow, hdeg⟩ := leastShiftedDegreeChoice?_some_valid hc
    have hrw : RowWithin (GuruswamiSudan.interpolationWidth params)
        (params.multiplicity * points.size + params.weightedDegreeBound + 2 + 2) c.row := by
      rw [hrow, Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hidx, Option.getD_some]
      exact hMrows _ (Array.getElem_mem_toList hidx)
    have hd := rowShiftedDegree?_le hrw (interpolationShifts_le params) hdeg
    have := ofCoeffRowC_cost P (by includes) c.row hrw (by omega)
    obtain ⟨hQs, hQi⟩ := ofCoeffRow_sizes hrw
    have := normalizeLeeFastC_cost P (by includes) params (CBivariate.ofCoeffRow c.row) hNS hQi
      hQs (by omega)
    cost_simp
    split <;> omega
  -- the assembly
  rw [Auto.CompPoly.GuruswamiSudan.ApproximantBasis.modularEquation.c622.costEq P (by includes),
    Auto.LeanVM.Extraction.Fast.solveWindow.c623.costEq P (by includes)]
  have hGn' := Nat.mul_le_mul_right points.size hGs
  have hMs' := Nat.mul_le_mul_left (84 * GuruswamiSudan.interpolationWidth params + 98) hMs
  have hopt : Option.casesOn (motive := fun _ ↦ ℕ)
      (M.leastShiftedDegreeChoice? (GuruswamiSudan.interpolationShifts params)) 1
      (fun val ↦ max (limbCount val.degree) (limbCount params.weightedDegreeBound) +
        (if val.degree ≤ params.weightedDegreeBound then
          machineCost P ofCoeffRowC.costIdx [encodeValue val.row] +
            machineCost P Auto.LeanVM.Extraction.Fast.normalizeLeeFast.c629.costIdx
              [encodeValue params, encodeValue (CBivariate.ofCoeffRow val.row)] + 5
        else 1) + 8) ≤
      (3 * (params.multiplicity * points.size + params.weightedDegreeBound + 2 + 2) + 32) *
        GuruswamiSudan.interpolationWidth params + normBound params.weightedDegreeBound
          (GuruswamiSudan.interpolationWidth params) + 30 := by
    cases hch : M.leastShiftedDegreeChoice? (GuruswamiSudan.interpolationShifts params) with
    | none => dsimp only; omega
    | some c => exact hcase c hch
  simp only [Array.length_toList, List.length_map] at *
  unfold interpPMCost
  cost_simp at hopt ⊢
  omega

end

end LeanVM.Cost.Bounds.PMSolve
