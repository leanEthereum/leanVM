/-
  LeanVM.Guest.B1.VsC.VsHonDone

  `VsHonPartsEx alW` and `verify_sub`'s windows at `alW`, every part discharged.
-/

module

public import LeanVM.Guest.B1.VsC.VsHonFin
public import LeanVM.Guest.B1.VsC.VsHonD3L

/-!
# `VsHonPartsEx alW`, proved

**`vsHonPartsEx_alW`**: `VsHonPartsIn`'s one field is `VsCtx.honCtx_d3Left`. **`vsWindows_alW`**: `verify_sub`'s
windows from its callees at `alW`, `k = 17`.
-/

namespace LeanVM.Guest.B1.VsC

open LeanVM.Guest.Memory (alW)

@[expose] public section

/-- **`VsHonPartsEx alW`.** -/
theorem vsHonPartsEx_alW : VsHonPartsEx alW :=
  vsHonPartsEx_of_in ⟨fun _ _ _ _ _ hal hok hN hE => VsCtx.honCtx_d3Left hal hok hN hE⟩

/-- **`verify_sub`'s windows at `alW`.** -/
theorem vsWindows_alW : VsWindowsFromCallees alW 17 :=
  vsWindows_alW_of_in ⟨fun _ _ _ _ _ hal hok hN hE => VsCtx.honCtx_d3Left hal hok hN hE⟩

end
end LeanVM.Guest.B1.VsC
