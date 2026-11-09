module

public import LeanVM.Cost.Bounds.Decoder.Prefixes
public import LeanVM.Cost.Bounds.PMBasis.LaneDefs
public import LeanVM.Cost.Extractor.PMLane
public import LeanVM.Cost.Bounds.CostConst
import all CompPoly.Univariate.Raw.Core
import all CompPoly.Univariate.Basic

/-!
# Bound: one lane's run on `pmSolver`, compiled

`gsRunPMC` (`gsRunDistinctWith pmSolver`, `Cost/Extractor/PMLane.lean`) is the extractor's
lane run `gsRunDistinctNF` with the interpolation `interpolateDistinctWith pmSolver`
(`interpolatePMC`): the interpolation, the truncation, Roth–Ruckenstein's search
(`prefixesNFC_cost`), the candidates filtered. **`gsRunPMC_cost`**: at most `gsRunBoundPM p`,
given the interpolation within the model's price `interpPMPrice p` on its input (`hi`:
`interpolatePMC_cost_price`, applied per lane in `Bounds/PMLane/Decode.lean`).

The sizes the run needs of the interpolated polynomial (`ℓ + 1` rows of at most `W + 1`
coefficients, at most `max 1 ℓ` prefixes) follow, as for the extractor's interpolation, from its
being an interpolation witness (`interpolatePM_valid`: the approximant-basis interpolation's
soundness, `approxInterpContextWith`).
-/

namespace LeanVM.Cost.Bounds.PMLane

open LeanVM.Cost LeanVM.Cost.Bounds LeanVM.Cost.Library LeanVM.Cost.Bounds.Decoder
open LeanVM.Cost.Extractor LeanVM.Parameters CompPoly LeanVM.Extraction LeanVM.Extraction.Fast
open CompPoly.GuruswamiSudan

public section

/-! ## The interpolated polynomial -/

/-- The approximant-basis interpolation's polynomial is an interpolation witness (on distinct
points). -/
theorem interpolatePM_valid {points : Array (K × K)} (h : DistinctXCoordinates points)
    {params : GSInterpParams} {Q : CBivariate K}
    (hQ : interpolateDistinctWith pmSolver points params = some Q) :
    ValidInterpolationWitness points params Q :=
  (approxInterpContextWith pmSolver).sound points params Q
    (by rw [← interpolateDistinctWith_eq pmSolver h]; exact hQ)

/-- Its sizes: at most `ℓ + 1` rows, row `y` of at most `W + 1 − (k − 1)·y` coefficients. -/
theorem interpolatePM_sizes {points : Array (K × K)} (h : DistinctXCoordinates points)
    {params : GSInterpParams} {Q : CBivariate K}
    (hQ : interpolateDistinctWith pmSolver points params = some Q)
    (hk : 1 < params.messageDegree) :
    Q.val.size ≤ interpolationYCap params + 1 ∧
      ∀ y, (Q.val.coeff y).val.size ≤ params.weightedDegreeBound + 1 - yWeight params * y := by
  have hv := interpolatePM_valid h hQ
  refine ⟨(lenLe_of_validInterpolation hv hk).1.val_size_le, fun y ↦ ?_⟩
  have hw := (CBivariate.natWeightedDegree_le_iff_coeff Q 1 (yWeight params) _).1 hv.2.1
  refine cpoly_val_size_le_of_coeff _ _ fun i hi ↦ ?_
  by_contra hne
  have := hw i y hne
  omega

/-- Roth–Ruckenstein's search on it returns at most `max 1 ℓ` prefixes. -/
theorem prefixesNF_size_le_PM {points : Array (K × K)} (h : DistinctXCoordinates points)
    {params : GSInterpParams} {Q : CBivariate K}
    (hQ : interpolateDistinctWith pmSolver points params = some Q)
    (hk : 1 < params.messageDegree) :
    (prefixesNF fieldRootCtxFast params.messageDegree
      (CBivariate.truncateX Q (params.weightedDegreeBound + 1)) (params.weightedDegreeBound + 1) 0
      default).size ≤ max 1 (interpolationYCap params) := by
  have hv := interpolatePM_valid h hQ
  rw [prefixesNF_eq_truncD hv, prefixesTruncD_eq,
    prefixesTrunc_eq fieldRootCtxFast _ Q _ (fun _ ↦ replayPath Q []) 0 default rfl]
  refine (prefixesWithFuelFast_size_le fieldRootCtxFast_nodup _ _ _ _).trans ?_
  have hd := rrDeg_le (lenLe_of_validInterpolation hv hk).1
  simp only [replayPath, List.foldl_nil, Nat.add_sub_cancel] at hd ⊢
  omega

/-- **The lane returns at most `max 1 ℓ` polynomials** on `pmSolver`. -/
theorem gsRunDistinctWith_size_le {points : Array (K × K)} (h : DistinctXCoordinates points)
    (params : GSInterpParams) (radius : ℕ) (hk : 1 < params.messageDegree) :
    (gsRunDistinctWith pmSolver points params radius).size ≤ max 1 (interpolationYCap params) := by
  rw [gsRunDistinctWith]
  split
  · simp
  · rename_i Q hQ
    exact Array.size_filter_le.trans (prefixesNF_size_le_PM h hQ hk)

/-- Each polynomial the lane returns on `pmSolver` has at most `k` coefficients. -/
theorem gsRunDistinctWith_mem_size_le {points : Array (K × K)} {params : GSInterpParams}
    {radius : ℕ} {p : CPolynomial K} (hp : p ∈ gsRunDistinctWith pmSolver points params radius) :
    p.val.size ≤ params.messageDegree := by
  rw [gsRunDistinctWith] at hp
  split at hp
  · simp at hp
  · rw [Array.mem_filter] at hp
    have := hp.2
    simp only [Bool.and_eq_true, degreeLtBool, decide_eq_true_eq] at this
    exact this.1

/-! ## The run -/

variable (P : MachineProgram)

/-- **One lane's run on `pmSolver`** (`gsRunDistinctWith pmSolver`: the interpolation,
Roth–Ruckenstein's search, the candidates filtered): at most `gsRunBoundPM p`, the interpolation
within `interpPMPrice p`. -/
theorem gsRunPMC_cost (hP : Includes P gsRunPMC.costDeps) {p : PMBasis.PMPrices}
    (points : Array (K × K)) (params : GSInterpParams) (radius : ℕ)
    (hi : machineCost P interpolatePMC.costIdx [encodeValue points, encodeValue params] ≤
      PMBasis.interpPMPrice p points.size params)
    (hs : InterpSizes points.size params) (hk1 : 1 < params.messageDegree)
    (hd : DistinctXCoordinates points) (hr : radius < 2 ^ 64)
    (hX : params.weightedDegreeBound + 1 < 2 ^ 56) (hY : interpolationYCap params + 2 < 2 ^ 28)
    (hk56 : params.messageDegree < 2 ^ 56) :
    machineCost P gsRunPMC.costIdx [encodeValue points, encodeValue params, encodeValue radius] ≤
      PMBasis.gsRunBoundPM p points.size params := by
  have ⟨hn, hW, hk, hyW, hw, _⟩ := hs
  rw [gsRunPMC.costEq P hP]
  generalize hQ : interpolateDistinctWith pmSolver points params = oQ at hi
  cases oQ with
  | none => dsimp only; unfold PMBasis.gsRunBoundPM; omega
  | some Q =>
    dsimp only
    have hsz := interpolatePM_sizes hd hQ hk1
    have hrr := prefixesNFC_cost P (by includes) (interpolatePM_valid hd hQ) hk1 hX hY hk56
    have hQi : InnerLe Q.val (params.weightedDegreeBound + 1) := fun c hc ↦ by
      obtain ⟨y, hy, rfl⟩ := Array.getElem_of_mem hc
      have := hsz.2 y
      have hc' : Q.val.coeff y = Q.val[y] := by
        rw [CPolynomial.Raw.coeff, Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hy]
        rfl
      rw [hc'] at this
      exact this.trans (Nat.sub_le _ _)
    have := truncateXC_cost P (by includes) Q (params.weightedDegreeBound + 1) (by omega) hQi
      (by omega)
    have h1 : (25 * (params.weightedDegreeBound + 1) + 72) * Q.val.size ≤
        (25 * (params.weightedDegreeBound + 1) + 72) * (interpolationYCap params + 1) :=
      Nat.mul_le_mul_left _ hsz.1
    have hres := prefixesNF_size_le_PM hd hQ hk1
    have hmem : ∀ p ∈ prefixesNF fieldRootCtxFast params.messageDegree
        (CBivariate.truncateX Q (params.weightedDegreeBound + 1)) (params.weightedDegreeBound + 1) 0
        default, p.val.size ≤ params.messageDegree := by
      have hv := interpolatePM_valid hd hQ
      rw [prefixesNF_eq_truncD hv, prefixesTruncD_eq,
        prefixesTrunc_eq fieldRootCtxFast _ Q _ (fun _ ↦ replayPath Q []) 0 default rfl]
      intro p hp
      have := prefixesWithFuelFast_mem_size_le fieldRootCtxFast _ _ 0 default
        (by show (default : CPolynomial K).val.size ≤ 0; rfl) p hp
      omega
    have hfv := fun p ↦ RunsApp.of_spec (us := [encodeValue points, encodeValue params, encodeValue radius]) (vs := [encodeValue p])
      (gsRunPMC.lam0.costSpec P (by includes) points params radius p)
    generalize hR : prefixesNF fieldRootCtxFast params.messageDegree
      (CBivariate.truncateX Q (params.weightedDegreeBound + 1)) (params.weightedDegreeBound + 1) 0
      default = res at hres hmem
    have hfil := filter_cost P (by includes) _
      (.closure gsRunPMC.lam0.costIdx [encodeValue points, encodeValue params, encodeValue radius]) hfv
      ((46 * params.messageDegree + 36) * points.size + 35) res.toList (fun p hp ↦ by
        have hps := hmem p (by simpa using hp)
        simp only [appCost_fn, List.cons_append, List.nil_append, List.length_cons, List.length_nil]
        rw [gsRunPMC.lam0.costEq P (by includes),
          (cost_const% (degreeLtBool (F := K)) costEq) P (by includes)]
        cost_simp
        split_ifs with hdeg
        · simp only [degreeLtBool, decide_eq_true_eq] at hdeg
          rw [(cost_const% (passesDistanceFast (F := K)) costEq) P (by includes)]
          have := mismatchCountC_cost P (by includes) points p (by omega)
          have := mismatchCountFast_le points p
          have := Nat.mul_le_mul_right points.size (show 46 * p.val.size + 36 ≤
            46 * params.messageDegree + 36 by omega)
          cost_simp
          omega
        · omega)
    have hfl := List.length_filter_le (fun p ↦ degreeLtBool p params.messageDegree &&
      passesDistanceFast points radius p) res.toList
    simp only [Array.length_toList] at hfil hfl
    have h2 : ((46 * params.messageDegree + 36) * points.size + 54) * res.size ≤
        ((46 * params.messageDegree + 36) * points.size + 54) * max 1 (interpolationYCap params) :=
      Nat.mul_le_mul_left _ hres
    have e2 : ((46 * params.messageDegree + 36) * points.size + 54) * res.size =
        ((46 * params.messageDegree + 36) * points.size + 35 + 15) * res.size + 4 * res.size := by
      ring
    unfold PMBasis.gsRunBoundPM
    cost_simp
    omega

end

end LeanVM.Cost.Bounds.PMLane
