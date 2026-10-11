import Whir.RingMapBatching
import Whir.FieldEquivalence

/-!
# Gamma and ring-map soundness for the actual three-word extension field

All field laws, cardinality, and 64-conjugate distinctness are proved for the
executable representation. The sent slices and candidate list are fixed before
the independent gamma and six map challenges; no numerical security-level claim
beyond the explicit rational error bounds is made.
-/
namespace Whir.RingMapBatchingConcrete

open scoped BigOperators Classical
open Concrete

/-- Gamma batching alone, for actual extension elements. -/
theorem batch_zero_probability {m : ℕ} (δ : Fin m → Fin 64 → E) (hne : δ ≠ 0) :
    Soundness.uniformProb (Finset.univ.filter fun γ : E =>
      RingMapBatching.batchErrors γ δ = 0) ≤ ((m - 1 : ℕ) : ℚ) / (2 : ℚ)^192 := by
  have h := RingMapBatching.batch_zero_probability δ hne
  norm_num only [FieldModel.card_E, Nat.cast_pow, Nat.cast_ofNat] at h ⊢
  exact h

/-- Actual unequal slice families have gamma loss plus the `2^-160` map loss. -/
theorem family_error_probability {m : ℕ} (sent honest : Fin m → Fin 64 → E)
    (hne : sent ≠ honest) :
    Soundness.uniformProb (Finset.univ.filter fun r : E × (Fin 6 → E) =>
      RingSwitch.familyTarget (RingSwitch.composedMap r.2)
        (fun i : Fin 64 => (E.ofK 2) ^ i.val) (fun j : Fin m => r.1 ^ j.val) sent =
      RingSwitch.familyTarget (RingSwitch.composedMap r.2)
        (fun i : Fin 64 => (E.ofK 2) ^ i.val) (fun j : Fin m => r.1 ^ j.val) honest) ≤
      ((m - 1 : ℕ) : ℚ) / (2 : ℚ)^192 + 1 / (2 : ℚ)^160 := by
  have h := RingMapBatching.family_error_probability (E.ofK 2)
    FieldModel.actual_conjugates_injective sent honest hne
  norm_num only [FieldModel.card_E, Nat.cast_pow, Nat.cast_ofNat] at h ⊢
  exact h

/-- The comparison target is the actual honest packed-family opening expression,
with each gamma scale inside the map, for arbitrary honest bit slices and weights. -/
theorem honest_family_error_probability {m : ℕ} {U : Type*} [Fintype U]
    (bits : Fin m → Fin 64 → U → Bool) (weights : Fin m → U → E)
    (sent : Fin m → Fin 64 → E)
    (hne : sent ≠ fun j => RingSwitch.slice (weights j) (bits j)) :
    Soundness.uniformProb (Finset.univ.filter fun r : E × (Fin 6 → E) =>
      RingSwitch.familyTarget (RingSwitch.composedMap r.2)
        (fun i : Fin 64 => (E.ofK 2) ^ i.val) (fun j : Fin m => r.1 ^ j.val) sent =
      ∑ j : Fin m, ∑ u : U, RingSwitch.composedMap r.2 (r.1 ^ j.val * weights j u) *
        RingSwitch.packed (fun i : Fin 64 => (E.ofK 2) ^ i.val) (bits j) u) ≤
      ((m - 1 : ℕ) : ℚ) / (2 : ℚ)^192 + 1 / (2 : ℚ)^160 := by
  have h := RingMapBatching.honest_family_error_probability (E.ofK 2)
    FieldModel.actual_conjugates_injective bits weights sent hne
  norm_num only [FieldModel.card_E, Nat.cast_pow, Nat.cast_ofNat] at h ⊢
  exact h

/-- The candidate list is an input independent of both challenge draws. -/
theorem family_fixed_list {m : ℕ} (sent : Fin m → Fin 64 → E)
    (candidates : Finset (Fin m → Fin 64 → E)) :
    Soundness.uniformProb (Finset.univ.filter fun r : E × (Fin 6 → E) =>
      ∃ honest ∈ candidates, sent ≠ honest ∧
        RingSwitch.familyTarget (RingSwitch.composedMap r.2)
          (fun i : Fin 64 => (E.ofK 2) ^ i.val) (fun j : Fin m => r.1 ^ j.val) sent =
        RingSwitch.familyTarget (RingSwitch.composedMap r.2)
          (fun i : Fin 64 => (E.ofK 2) ^ i.val) (fun j : Fin m => r.1 ^ j.val) honest) ≤
      (candidates.card : ℚ) *
        (((m - 1 : ℕ) : ℚ) / (2 : ℚ)^192 + 1 / (2 : ℚ)^160) := by
  have h := RingMapBatching.family_fixed_list (E.ofK 2)
    FieldModel.actual_conjugates_injective sent candidates
  norm_num only [FieldModel.card_E, Nat.cast_pow, Nat.cast_ofNat] at h ⊢
  exact h

end Whir.RingMapBatchingConcrete
