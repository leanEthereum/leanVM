/-
  LeanVM.Guest.CoreMode.Fam.ResExp

  A constant's power of `g`, sound.
-/

module

public import LeanVM.Guest.CoreMode.Fam.ResF
public import LeanVM.Guest.CoreMode.Fam.FamDefs

/-!
# A constant's power of `g`

`powOf1_sound`: `powOf1 c = some z` makes `c = g^z`.
-/

namespace LeanVM.Guest.EndExec

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Mode LeanVM.Guest.Core LeanVM.Guest.Memory
open LeanVM.Guest.Res (powOf powOf1)

public section

theorem powOf1_sound {c : E} {z : ℕ} (h : powOf1 c = some z) : c = ofK (Parameters.g ^ z) := by
  unfold powOf1 at h
  split_ifs at h with h1
  · obtain rfl := (Option.some.inj h).symm
    rw [eq_ofK_limb h1.1, h1.2, pow_zero]
  · exact powOf_sound h

end

end LeanVM.Guest.EndExec
