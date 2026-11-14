/-
  LeanVM.Guest.B1.Place.OsFinal

  `open_stacked` is complete placed at every stack log and rate.
-/

module

public import LeanVM.Guest.B1.Place.ArmFinal
public import LeanVM.Guest.B1.Place.LrBound
public import LeanVM.Guest.B1.Place.LqExact
public import LeanVM.Guest.B1.Whir.CHonest

/-!
# `open_stacked`, placed

**`open_stacked_completeAtD`**, **`open_stacked_completeAtB`**: OsSpec's statements, from the
placed lift (`Arm.open_stacked_completeAtD_of`, `Arm.open_stacked_completeAtB_of`), the body's honest
data (`Whir.os_honest_proved`), `level_residual`'s placed statement (`level_residual_completeAt`)
and, frames below `2^32`, the helpers within the words bounds of their trees (`helperBounds`).
-/

namespace LeanVM.Guest.B1

open LeanVM.Guest.Core

@[expose] public section

/-- **`open_stacked` is complete placed at every stack log and rate.** -/
theorem open_stacked_completeAtD : open_stacked_completeAtD_Spec :=
  Arm.open_stacked_completeAtD_of Whir.os_honest_proved level_residual_completeAt

/-- **The helpers within the words bounds of their trees**, frames below `2^32`. -/
theorem helperBounds (fs : String → ℕ) (cert : String → V → ℕ) (κ : ℕ) (hrf : Lift.RunsFit fs cert)
    (hcons : RunsConsec cert) (hκ : 11 ≤ κ) (hfs : ∀ f, fs f < 2 ^ 32) : Arm.HelperBounds fs cert κ :=
  ⟨level_positions_completeAtB fs cert κ hrf hcons (by omega) hfs,
    level_queries_completeAtB fs cert κ hfs, level_residual_completeAtB fs cert κ hfs⟩

/-- **`open_stacked` is complete placed at every stack log and rate, within `osBosAt` words**,
every frame below `2^32`. -/
theorem open_stacked_completeAtB : open_stacked_completeAtB_Spec :=
  Arm.open_stacked_completeAtB_of Whir.os_honest_proved level_residual_completeAt helperBounds

end
end LeanVM.Guest.B1
