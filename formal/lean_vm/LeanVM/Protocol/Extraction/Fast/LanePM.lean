module

public import LeanVM.Protocol.Extraction.Fast.CertifiedSolve
public import LeanVM.Protocol.Extraction.Fast.DecodeAdmissible
public import LeanVM.Protocol.Extraction.Fast.FFT.Additive
public import LeanVM.Protocol.Extraction.Fast.GSData

/-!
# The lanes by the approximant-basis interpolation

The proof side's reference decoder (`decodeStacksDistinct`, `Fast/DecodeAdmissible.lean`)
interpolates each lane by Lee–O'Sullivan's basis reduced by Mulders–Storjohann
(`interpolateDistinct`). Here the
lanes interpolate by CompPoly's approximant-basis interpolation (Chowdhury, Jeannerod, Neiger,
Schost, Villard) on a modular-equation solver `S` (`interpolateDistinctWith`), and the chain up to
the decoded stacks is copied with it (`gsRunDistinctWith`, …, `decodeStacksDistinctWith`).

Another interpolation may return another polynomial `Q`, so Roth–Ruckenstein another list, in
another order; but what the run lists does not depend on the interpolation (`mem_gsRunNoCheck`:
the polynomials of degree `< k` within the radius, when an interpolation polynomial exists), and
each lane's list is deduplicated and sorted (`mergeSort_dedup_eq`), so the lanes' lists are
equal (`laneListWith_eq`) and so the decoded stacks: **`decodeStacksDistinctWith_eq`**, at every
admissible shape, for every solver.

`decodeStacksDistinctPM` is the chain on the non-adaptive solver (`pmSolver`:
`certifiedModularSolutionBasisContext` on the additive-FFT products, the ordered-weak-Popov PM-basis
at leaf cutoff `1` with evaluation-domain matrix products), proved
equal to `decodeStacksDistinct` (**`decodeStacksDistinctPM_eq`**) and to `decodeStacksFast`
(`decodeStacksDistinctPM_eq_fast`, the rewrite `extractorTop_eq_full` uses): the compiled
extractor's list decoder (`decOf`, `Fast/Compiled.lean`).
-/

namespace LeanVM.Extraction.Fast

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Parameters.Whir LeanVM.Extraction
open CompPoly CompPoly.GuruswamiSudan CompPoly.PolynomialMatrix CompPoly.PolynomialMatrix.Approximant

public section

/-! ## The interpolation -/

/-- The approximant-basis interpolation on the solver `S`, with the fast vanishing polynomial and
Horner's evaluations. -/
@[expose] def approxInterpContextWith (S : ModularSolutionBasisContext K) : GSInterpContext K :=
  ApproximantBasis.approximantBasisInterpContext vanishingContextFast
    (CPolynomial.BatchEvalContext.horner K) S

/-- **The approximant-basis interpolation of distinct points**: `approxInterpContextWith S`'s,
without the distinctness check, with the fast normalization (`normalizeLeeFast`), the modular
data with each modulus's inverse computed once (`buildGSModularDataCached`, on the additive-FFT
low products). -/
@[expose] def interpolateDistinctWith (S : ModularSolutionBasisContext K)
    (points : Array (K × K)) (params : GSInterpParams) : Option (CBivariate K) :=
  if params.messageDegree ≤ 1 then
    some (lowMessageDegreeInterpolation points params.multiplicity)
  else
    let G := vanishingFast (points.map fun point ↦ point.1)
    let R := CPolynomial.interpolateCoefficientFormWithVanishing
      (CPolynomial.BatchEvalContext.horner K) G points
    let data := buildGSModularDataCached S.mulContext FFT.fftRawMulLowContext R G params
    let basis := S.solutionBasis (ApproximantBasis.modularEquation data) data.shift
      (some params.weightedDegreeBound)
    match leastShiftedDegreeChoice? basis data.shift with
    | none => none
    | some choice =>
        if choice.degree ≤ params.weightedDegreeBound then
          normalizeLeeFast params (CBivariate.ofCoeffRow choice.row)
        else
          none

theorem interpolateDistinctWith_eq (S : ModularSolutionBasisContext K) {points : Array (K × K)}
    (h : DistinctXCoordinates points) (params : GSInterpParams) :
    interpolateDistinctWith S points params = (approxInterpContextWith S).interpolate points params := by
  show _ = ApproximantBasis.approximantBasisInterpolate _ _ _ points params
  rw [interpolateDistinctWith, ApproximantBasis.approximantBasisInterpolate,
    ApproximantBasis.approximantBasisPositiveInterpolate,
    LeeOSullivan.distinctXCoordinatesBool_iff.2 h, normalizeLeeFast_eq_fun]
  by_cases hk : params.messageDegree ≤ 1
  · rw [ite_eq_left hk, ite_eq_left hk]
  · rw [ite_eq_right hk, ite_eq_right hk, ite_eq_left rfl]
    simp only [vanishingContextFast, ApproximantBasis.normalizeApproximantCandidate?,
      LeeOSullivan.normalizeLeeCandidate?, buildGSModularDataCached_eq _ _ S.modContext]
    split
    all_goals (rename_i heq; rw [heq])

/-! ## The run -/

/-- `gsRunNF` (Roth–Ruckenstein at precision `W + 1`, no fallback) is `gsRunNoCheck`, for every
interpolation. -/
theorem gsRunNF_eq_gsRunNoCheck (I : GSInterpContext K) (points : Array (K × K))
    (params : GSInterpParams) (radius : ℕ) :
    gsRunNF I points params radius = gsRunNoCheck I points params radius := by
  rw [gsRunNF, gsRunNoCheck]
  cases hQ : I.interpolate points params with
  | none => rfl
  | some Q =>
    dsimp only
    rw [prefixesNF_eq_truncD (I.sound points params Q hQ)]

/-- **The lane runner on the solver `S`**: `gsRunDistinctNF` with `interpolateDistinctWith S`. -/
@[expose] def gsRunDistinctWith (S : ModularSolutionBasisContext K) (points : Array (K × K))
    (params : GSInterpParams) (radius : ℕ) : Array (CPolynomial K) :=
  match interpolateDistinctWith S points params with
  | none => #[]
  | some Q =>
    (prefixesNF fieldRootCtxFast params.messageDegree
        (CBivariate.truncateX Q (params.weightedDegreeBound + 1)) (params.weightedDegreeBound + 1)
        0 default).filter fun p ↦
      degreeLtBool p params.messageDegree && passesDistanceFast points radius p

theorem gsRunDistinctWith_eq (S : ModularSolutionBasisContext K) {points : Array (K × K)}
    (h : DistinctXCoordinates points) (params : GSInterpParams) (radius : ℕ) :
    gsRunDistinctWith S points params radius =
      gsRunNoCheck (approxInterpContextWith S) points params radius := by
  rw [← gsRunNF_eq_gsRunNoCheck, gsRunDistinctWith, gsRunNF, interpolateDistinctWith_eq S h,
    passesDistanceFast_eq]
  rfl

/-- **The runner on `S` lists what the runner lists**, on distinct points where the final root
check is redundant. -/
theorem mem_gsRunDistinctWith (S : ModularSolutionBasisContext K) {points : Array (K × K)}
    (hd : DistinctXCoordinates points) {params : GSInterpParams} {radius : ℕ}
    (hW : params.weightedDegreeBound < params.multiplicity * (points.size - radius))
    (p : CPolynomial K) :
    p ∈ (gsRunDistinctWith S points params radius).toList ↔
      p ∈ (gsRunDistinctNF points params radius).toList := by
  rw [gsRunDistinctWith_eq S hd, mem_gsRunNoCheck _ _ _ _ hd hW, gsRunDistinctNF_eq hd,
    gsRunDistinct_eq hd, mem_gsRunNoCheck _ _ _ _ hd hW]

/-! ## The lane chain -/

/-- `gsLaneDistinct` on the solver `S`. -/
@[expose] def gsLaneWith (S : ModularSolutionBasisContext K) (κ R A : ℕ) (Sym : ℕ → ℕ → K)
    (u : ℕ) : Array (CPolynomial K) :=
  let params := gsParamsFor (2 ^ κ) (2 ^ (κ + R)) A
  gsRunDistinctWith S (lanePointsS (2 ^ (κ + R)) Sym u) params.interp params.radius

/-- `laneListDistinct` on the solver `S`. -/
@[expose] def laneListWith (S : ModularSolutionBasisContext K) (κ R A : ℕ) (Sym : ℕ → ℕ → K)
    (u : ℕ) : List (Array K) :=
  (((gsLaneWith S κ R A Sym u).toList.map (toNovelFast κ)).dedup).mergeSort coeffsLE

/-- `laneEncodedDistinct` on the solver `S`. -/
@[expose] def laneEncodedWith (S : ModularSolutionBasisContext K) (κ R A : ℕ) (Sym : ℕ → ℕ → K)
    (u : ℕ) : List (Array K × Array K) :=
  (laneListWith S κ R A Sym u).map fun c ↦ (c, novelFwd κ R c)

/-- `pruneUpToDistinct` on the solver `S`. -/
@[expose] def pruneUpToWith (S : ModularSolutionBasisContext K) (κ R A : ℕ) (W : ℕ → List K)
    (U : ℕ) : List (List (Array K) × List ℕ) :=
  let T := laneTable (2 ^ (κ + R)) W
  (List.range U).foldl
    (fun st u ↦
      if st.isEmpty then []
      else pruneStep A (tableSymbol T u) (laneEncodedWith S κ R A (tableSymbol T) u) st)
    [([], List.range (2 ^ (κ + R)))]

/-- **The decoded stacks, the lanes interpolated on the solver `S`.** -/
@[expose] def decodeStacksDistinctWith (S : ModularSolutionBasisContext K) (μ R : ℕ)
    (W : ℕ → List K) : List (Vector K (2 ^ μ)) :=
  (pruneUpToWith S (μ - initialFold) R (johnsonThreshold μ R) W (2 ^ initialFold)).map
    fun s ↦ stackOf μ s.1

theorem mem_gsLaneWith (S : ModularSolutionBasisContext K) {κ R A : ℕ}
    (h : checkRedundant κ R (gsParamsFor (2 ^ κ) (2 ^ (κ + R)) A)) (Sym : ℕ → ℕ → K) (u : ℕ)
    (p : CPolynomial K) :
    p ∈ (gsLaneWith S κ R A Sym u).toList ↔ p ∈ (gsLaneDistinct κ R A Sym u).toList := by
  simp only [checkRedundant, Bool.and_eq_true, decide_eq_true_eq] at h
  have hd := distinct_lanePointsS _ (Nat.pow_le_pow_right (by norm_num) h.1) Sym u
  have hW : (gsParamsFor (2 ^ κ) (2 ^ (κ + R)) A).interp.weightedDegreeBound <
      (gsParamsFor (2 ^ κ) (2 ^ (κ + R)) A).interp.multiplicity *
        ((lanePointsS (2 ^ (κ + R)) Sym u).size - (gsParamsFor (2 ^ κ) (2 ^ (κ + R)) A).radius) := by
    simpa [lanePointsS] using h.2
  exact mem_gsRunDistinctWith S hd hW p

/-- **A lane's list does not depend on the solver**, where the final root check is redundant. -/
theorem laneListWith_eq (S : ModularSolutionBasisContext K) {κ R A : ℕ}
    (h : checkRedundant κ R (gsParamsFor (2 ^ κ) (2 ^ (κ + R)) A)) (Sym : ℕ → ℕ → K) (u : ℕ) :
    laneListWith S κ R A Sym u = laneListDistinct κ R A Sym u := by
  rw [laneListWith, laneListDistinct]
  refine mergeSort_dedup_eq fun x ↦ ?_
  simp only [List.mem_map, mem_gsLaneWith S h]

theorem pruneUpToWith_eq (S : ModularSolutionBasisContext K) {κ R A : ℕ}
    (h : checkRedundant κ R (gsParamsFor (2 ^ κ) (2 ^ (κ + R)) A)) (W : ℕ → List K) (U : ℕ) :
    pruneUpToWith S κ R A W U = pruneUpToDistinct κ R A W U := by
  simp only [pruneUpToWith, pruneUpToDistinct, laneEncodedWith, laneEncodedDistinct,
    laneListWith_eq S h]

/-- **At admissible shapes, the decoded stacks do not depend on the solver.** -/
theorem decodeStacksDistinctWith_eq (S : ModularSolutionBasisContext K) {μ R : ℕ}
    (h : Whir.Admissible μ R) (W : ℕ → List K) :
    decodeStacksDistinctWith S μ R W = decodeStacksDistinct μ R W := by
  rw [decodeStacksDistinctWith, decodeStacksDistinct,
    pruneUpToWith_eq S (checkRedundant_johnson h)]

/-! ## On the non-adaptive solver -/

/-- **The lanes' solver**: the non-adaptive certified solve, its rows selected by degree
(`certifiedModularSolutionBasisContext`: no modular filter, `CertifiedSolve.lean`), on the
additive-FFT products and remainders (`FFT.fftMulContext`, `FFT.fftModContext`), the
ordered-weak-Popov PM-basis at leaf cutoff `1` with its matrix products on the additive-FFT
evaluation domain, each product's plan built once (`popovEvalPMBasisContext FFT.novelTransform`). -/
@[expose] def pmSolver : ModularSolutionBasisContext K :=
  certifiedModularSolutionBasisContext FFT.fftMulContext FFT.fftModContext
    (popovEvalPMBasisContext FFT.novelTransform FFT.fftMulContext FFT.fftMulLowContext 1)

/-- **The decoded stacks, the lanes by the approximant-basis interpolation on `pmSolver`.** -/
@[expose] def decodeStacksDistinctPM (μ R : ℕ) (W : ℕ → List K) : List (Vector K (2 ^ μ)) :=
  decodeStacksDistinctWith pmSolver μ R W

/-- **`decodeStacksDistinctPM` is `decodeStacksDistinct`** at admissible shapes. -/
theorem decodeStacksDistinctPM_eq {μ R : ℕ} (h : Whir.Admissible μ R) (W : ℕ → List K) :
    decodeStacksDistinctPM μ R W = decodeStacksDistinct μ R W :=
  decodeStacksDistinctWith_eq pmSolver h W

/-- `decodeStacksDistinctPM` is `decodeStacksFast` at admissible shapes (the rewrite
`extractorTop_eq_full` makes with `decodeStacksDistinct_eq`). -/
theorem decodeStacksDistinctPM_eq_fast {μ R : ℕ} (h : Whir.Admissible μ R) (W : ℕ → List K) :
    decodeStacksDistinctPM μ R W = decodeStacksFast μ R W := by
  rw [decodeStacksDistinctPM_eq h, decodeStacksDistinct_eq h]

/-- `decodeStacksDistinctPM` is the statement's `decodeStacks` at admissible shapes. -/
theorem decodeStacksDistinctPM_eq_decodeStacks {μ R : ℕ} (h : Whir.Admissible μ R)
    (W : ℕ → List K) : decodeStacksDistinctPM μ R W = decodeStacks μ R W := by
  rw [decodeStacksDistinctPM_eq_fast h, decodeStacksFast_eq]

end

end LeanVM.Extraction.Fast
