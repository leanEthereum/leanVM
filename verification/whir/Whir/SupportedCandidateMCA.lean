import Whir.SupportedCandidateFolding
import Whir.ProductionTransitions

/-! Raw same-set MCA exclusions required for SAME-target lifting. These are
stronger than the existing all-candidates-lost restoration event and are charged
explicitly; no accepted-prover availability premise is hidden in their bound. -/
namespace Whir.SupportedCandidateExtraction
open Concrete Protocol CandidateFolding MutualAgreement ParameterBounds

open Classical in
noncomputable def mcaSeeds (profile : Profile) (level : Fin (config profile).folds.size)
    {lanes : Nat} (oracle : Fin (lanes * 2) → Fin (length (config profile) level) → E) : Finset E :=
  Finset.univ.filter (RowBad foldGenerator
    (LinearMap.range (concreteEncoder (CausalGame.remaining (config profile) level)
      (config profile).rates[level.val]!)) (threshold (config profile) level)
    ![fun lane => oracle (evenLane lane), fun lane => oracle (oddLane lane)])

/-- Per actual fresh fold scalar, for ANY fixed prefix row oracle and ANY lane
count, the separately charged SAME-target MCA event costs at most 2^-84. -/
theorem mcaSeeds_probability (profile : Profile) (level : Fin (config profile).folds.size)
    {lanes : Nat} (oracle : Fin (lanes * 2) → Fin (length (config profile) level) → E) :
    Soundness.uniformProb (mcaSeeds profile level oracle) ≤ (2 ^ 108 : ℚ) / 2 ^ 192 := by
  classical
  obtain ⟨depth, degreePositive, degreeBound⟩ := ProductionTransitions.production_fold_facts profile level
  let n := CausalGame.remaining (config profile) level
  let rate := (config profile).rates[level.val]!
  let domain := AdditiveCode.concreteDomain (n + rate) depth
  have rangeEq : LinearMap.range (concreteEncoder n rate) = rsCode domain (2 ^ n) := by
    unfold concreteEncoder
    exact novelEncoder_range _ _ (AdditiveCode.concrete_bitBasis_independent n (by omega)) _
  have johnson := (production_radius profile level).2
  simp only [rho_cast, dimension, length, Nat.cast_pow, Nat.cast_ofNat] at johnson
  change 1 ≤ 2 ^ n - 1 at degreePositive
  change 2 ^ n - 1 ≤ 2 ^ (n + rate) - 2 at degreeBound
  have estimate := johnson_row_bad_probability domain degreePositive degreeBound
    (radius (config profile) level) (production_radius profile level).1.le
    (by simpa only [n, rate, Nat.cast_pow, Nat.cast_ofNat] using johnson)
    ![fun lane => oracle (evenLane lane), fun lane => oracle (oddLane lane)]
  have degree : 2 ^ n - 1 + 1 = 2 ^ n := by
    have positive : 0 < 2 ^ n := by positivity
    omega
  rw [degree] at estimate
  have eventEq : mcaSeeds profile level oracle = Finset.univ.filter
      (RowBad foldGenerator (rsCode domain (2 ^ n))
        ⌈(length (config profile) level : ℝ) * (1 - radius (config profile) level)⌉₊
        ![fun lane => oracle (evenLane lane), fun lane => oracle (oddLane lane)]) := by
    dsimp only [n, rate] at rangeEq ⊢
    simp only [mcaSeeds, rangeEq, ProductionTransitions.threshold_real]
  simp only [length, n, rate] at eventEq
  erw [← eventEq] at estimate
  have bounded := estimate.trans (div_le_div_of_nonneg_right
    (production_johnsonNumerator profile level) (by positivity))
  simp only [FieldModel.card_E, Nat.cast_pow, Nat.cast_ofNat] at bounded
  exact (Rat.cast_le (K := ℝ)).mp (by simpa only [Rat.cast_div, Rat.cast_pow, Rat.cast_ofNat] using bounded)

#print axioms mcaSeeds_probability
end Whir.SupportedCandidateExtraction
