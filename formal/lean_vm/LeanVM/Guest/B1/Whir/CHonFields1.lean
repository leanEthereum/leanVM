/-
  LeanVM.Guest.B1.Whir.CHonFields1

  The 28 candidates' `FieldStatic`, by kernel evaluation.
-/

module

public import LeanVM.Guest.B1.Whir.CHonFields0

namespace LeanVM.Guest.B1.Whir

@[expose] public section

theorem fieldStatic_all (m : ℕ) (h : m < 28) : FieldStatic (osCfg m) := by
  interval_cases m
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel

end
end LeanVM.Guest.B1.Whir
