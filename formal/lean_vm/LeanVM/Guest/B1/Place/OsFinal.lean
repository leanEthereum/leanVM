/-
  LeanVM.Guest.B1.Place.OsFinal

  `open_stacked`'s helpers within the words bounds of their trees.
-/

module

public import LeanVM.Guest.B1.Place.ArmFinal
public import LeanVM.Guest.B1.Place.LrBound
public import LeanVM.Guest.B1.Place.LsProof
public import LeanVM.Guest.B1.Place.LqProofP
public import LeanVM.Guest.B1.Whir.CHonest

/-!
# `open_stacked`'s helpers, bounded

`helperBounds`: frames below `2^32`, the helpers within the words bounds of their trees (`Arm.HelperBounds`).
-/

namespace LeanVM.Guest.B1

open LeanVM.Guest.Core

@[expose] public section

/-- **The helpers within the words bounds of their trees**, frames below `2^32`. -/
theorem helperBounds (fs : String → ℕ) (cert : String → V → ℕ) (κ : ℕ) (hrf : Lift.RunsFit fs cert)
    (hcons : RunsConsec cert) (hκ : 11 ≤ κ) (hfs : ∀ f, fs f < 2 ^ 32) : Arm.HelperBounds fs cert κ :=
  ⟨level_positions_completeAtBE fs cert κ hrf hcons (by omega) hfs,
    level_queries_completeAtBP fs cert κ hfs, level_residual_completeAtB fs cert κ hfs⟩

end
end LeanVM.Guest.B1
