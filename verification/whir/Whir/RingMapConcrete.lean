import Whir.RingMapSoundness
import Whir.FieldEquivalence

/-! Assumption-free field/basis instantiation of the six-stage map bound for the
actual three-word extension representation. Errors remain fixed before sampling. -/
namespace Whir.RingMapConcrete
open scoped BigOperators Classical
open Concrete

/-- Nonzero actual 64-slice errors produce a nonzero challenge polynomial. -/
theorem discrepancy_ne_zero (errors : Fin 64 → E) (hne : errors ≠ 0) :
    RingMapSoundness.discrepancyPolynomial (fun i => (E.ofK 2) ^ i.val) errors ≠ 0 :=
  RingMapSoundness.discrepancy_ne_zero (E.ofK 2)
    FieldModel.actual_conjugates_injective errors hne

/-- The actual extension has `2^192` elements; six independent uniform
challenges therefore lose at most `2^-160` against a fixed false slice table. -/
theorem map_error_probability (errors : Fin 64 → E) (hne : errors ≠ 0) :
    Soundness.uniformProb (Finset.univ.filter fun f : Fin 6 → E =>
      (∑ i : Fin 64, (E.ofK 2) ^ i.val * RingSwitch.composedMap f (errors i)) = 0) ≤
        1 / (2:ℚ)^160 := by
  have h := RingMapSoundness.map_error_probability (E.ofK 2)
    FieldModel.actual_conjugates_injective errors hne
  norm_num only [FieldModel.card_E, Nat.cast_pow, Nat.cast_ofNat] at h ⊢
  exact h

/-- The concrete fixed-list bound has no field-law or conjugacy hypotheses. -/
theorem map_error_fixed_list (errors : Finset (Fin 64 → E))
    (nonzero : ∀ e ∈ errors, e ≠ 0) :
    Soundness.uniformProb (Finset.univ.filter fun f : Fin 6 → E =>
      ∃ e ∈ errors, (∑ i : Fin 64, (E.ofK 2) ^ i.val * RingSwitch.composedMap f (e i)) = 0) ≤
        (errors.card : ℚ) * (1 / (2:ℚ)^160) := by
  have h := RingMapSoundness.map_error_fixed_list (E.ofK 2)
    FieldModel.actual_conjugates_injective errors nonzero
  norm_num only [FieldModel.card_E, Nat.cast_pow, Nat.cast_ofNat] at h ⊢
  exact h

end Whir.RingMapConcrete
