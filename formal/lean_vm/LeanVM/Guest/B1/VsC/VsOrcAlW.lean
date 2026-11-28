/-
  LeanVM.Guest.B1.VsC.VsOrcAlW

  `verify_sub`'s windows at the deployed alignment `alW`, from the honest contexts.
-/

module

public import LeanVM.Guest.B1.VsC.VsOrcPin
public import LeanVM.Guest.Memory.GuestWordsA

/-!
# `verify_sub`'s windows at `alW`

`vsOrcW_of_honexA` and `vsWindows_of_honexA` at the deployed alignment `alW` (`Complete/Left.lean`'s choice):
**`vsOrcW_of_honex`**, **`vsWindows_of_honex`**.
-/

namespace LeanVM.Guest.B1.VsC

open LeanVM.Guest.Memory (alW)

@[expose] public section

/-- **`verify_sub`'s honest oracle statement at `alW`**, from the honest contexts. -/
theorem vsOrcW_of_honex (hH : VsHonEx alW) : VsOrcWFromCallees alW 17 := vsOrcW_of_honexA hH

/-- **`verify_sub`'s windows at `alW`**, from the honest contexts. -/
theorem vsWindows_of_honex (hH : VsHonEx alW) : VsWindowsFromCallees alW 17 := vsWindows_of_honexA hH

end
end LeanVM.Guest.B1.VsC
