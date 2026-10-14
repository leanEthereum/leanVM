import Whir.FoldSoundness
import Whir.InitialSoundness
import Whir.ConcreteCandidates

/-! Production numerical envelopes are applied to actual transition events,
not used as hypotheses standing in for the MCA or candidate-list theorem. -/
namespace Whir.ProductionTransitions
open Concrete Protocol CausalGame CandidateFolding VerifierInvariant
open ParameterBounds GroupedChallenges

/-- The rational threshold in the candidate list is exactly the real threshold
in the checked MCA provider. -/
theorem threshold_real (c : Config) (i : Nat) :
    threshold c i = ⌈(length c i : ℝ) * (1 - radius c i)⌉₊ := by
  apply eq_of_forall_ge_iff
  intro bound
  simp only [threshold, Nat.ceil_le, radius, sub_sub_cancel]
  constructor <;> intro h <;> exact_mod_cast h

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- These are the actual dimensions required by the MCA theorem, evaluated from
the production constructor, not an independently copied parameter table. -/
theorem production_fold_facts : ∀ p : Profile, ∀ i : Fin (config p).folds.size,
    remaining (config p) i + (config p).rates[i.val]! ≤ 64 ∧
    1 ≤ dimension (config p) i - 1 ∧
    dimension (config p) i - 1 ≤ length (config p) i - 2 := by
  decide +kernel

open Classical in
/-- A fresh fold challenge loses the actual candidate invariant with at most the
production ledger's fold error. Every list/MCA/field prerequisite is discharged. -/
theorem production_fold_escape (top : Bool) (p : Profile) (i : Fin (config p).folds.size)
    {lanes : Nat} (oracle : Fin (lanes * 2) →
      Fin (2 ^ (remaining (config p) i + (config p).rates[i.val]!)) → E)
    (state : VerifierState E) (next : E → Message E)
    (weightSize : state.weight.size = (lanes * 2) * dimension (config p) i)
    (lost : Lost (arrayCandidates top
      (concreteEncoder (remaining (config p) i) (config p).rates[i.val]!) oracle
      (threshold (config p) i)) state) :
    Soundness.uniformProb (Finset.univ.filter fun r : E =>
      ¬ Lost (arrayCandidates top
        (concreteEncoder (remaining (config p) i) (config p).rates[i.val]!)
        (foldOracle oracle r) (threshold (config p) i))
        (state.fold (CandidateFolding.foldBlock top (dimension (config p) i)) r (next r))) ≤
      foldError (config p) (estimates (config p)) i := by
  classical
  obtain ⟨depth, degree_pos, degree_bound⟩ := production_fold_facts p i
  have johnson := (production_radius p i).2
  simp only [rho_cast, dimension, length, Nat.cast_pow, Nat.cast_ofNat] at johnson
  have incoming : Lost (arrayCandidates top
      (concreteEncoder (remaining (config p) i) (config p).rates[i.val]!) oracle
      ⌈((length (config p) i : Nat) : ℝ) * (1 - radius (config p) i)⌉₊) state := by
    rw [← threshold_real]
    exact lost
  have result := FoldSoundness.concrete_fold_escape top (remaining (config p) i)
    (config p).rates[i.val]! depth degree_pos degree_bound (radius (config p) i)
    (production_radius p i).1.le johnson oracle state next weightSize incoming
  dsimp only at result
  have hthreshold := threshold_real (config p) i
  dsimp only [length] at hthreshold
  rw [← hthreshold] at result
  have card : ((arrayCandidates top
      (concreteEncoder (remaining (config p) i) (config p).rates[i.val]!) oracle
      (threshold (config p) i)).card : ℝ) ≤ 2 ^ 32 := by
    exact_mod_cast ConcreteCandidates.production_arrayCandidates_card top p i oracle
  have numerator := production_johnsonNumerator p i
  have relaxed := result.trans (add_le_add
    (mul_le_mul_of_nonneg_right card (by positivity))
    (div_le_div_of_nonneg_right numerator (by positivity)))
  simp only [FieldModel.card_E, Nat.cast_pow, Nat.cast_ofNat] at relaxed
  have rhs : (2 ^ 32 : ℝ) * (2 / 2 ^ 192) + 2 ^ 108 / 2 ^ 192 =
      (2 * 2 ^ 32 + 2 ^ 108) / 2 ^ 192 := by ring
  rw [rhs] at relaxed
  change _ ≤ (2 * (2 ^ 32 : ℚ) + 2 ^ 108) / 2 ^ 192
  apply (Rat.cast_le (K := ℝ)).mp
  simp only [Rat.cast_div, Rat.cast_add, Rat.cast_mul, Rat.cast_pow, Rat.cast_ofNat, dimension]
  convert relaxed using 1
  congr 2

end Whir.ProductionTransitions
