module

public import LeanVM.Guest.Fast.GLanes
public import LeanVM.Guest.Word

/-!
# `gLanes`, checked

`gLanes_eq`: `gLanes[k]` is the lane of `g^k` (`gpowK`, square-and-multiply), by kernel
evaluation. This module imports the table and `Guest/Word.lean` alone (`Fast/Firewall.lean`).
-/

namespace LeanVM.Guest.Fast

open LeanVM.Parameters

@[expose] public section

theorem gLanes_eq : gLanes = (List.range 256).map fun k ↦ (gpowK k).lane.toNat := by
  decide +kernel

end
end LeanVM.Guest.Fast
