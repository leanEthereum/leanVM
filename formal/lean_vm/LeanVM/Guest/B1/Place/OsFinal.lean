/-
  LeanVM.Guest.B1.Place.OsFinal

  `open_stacked` is complete placed at every stack log and rate.
-/

module

public import LeanVM.Guest.B1.Place.ArmFinal
public import LeanVM.Guest.B1.Place.LrProof
public import LeanVM.Guest.B1.Whir.CHonest

/-!
# `open_stacked`, placed

**`open_stacked_completeAtD`**: OsSpec's statement, from the placed lift
(`Arm.open_stacked_completeAtD_of`), the body's honest data (`Whir.os_honest_proved`) and
`level_residual`'s placed statement (`level_residual_completeAt`).
-/

namespace LeanVM.Guest.B1

@[expose] public section

/-- **`open_stacked` is complete placed at every stack log and rate.** -/
theorem open_stacked_completeAtD : open_stacked_completeAtD_Spec :=
  Arm.open_stacked_completeAtD_of Whir.os_honest_proved level_residual_completeAt

end
end LeanVM.Guest.B1
