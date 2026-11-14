/-
  LeanVM.Guest.Exact.InverseCheck

  The `inverse` hints of the functions that have them are each followed, in its block, by
  `assertNe` on its two values, by the kernel, one function at a time.
-/

module

public import LeanVM.Guest.Exact.Defs
public import LeanVM.Guest.CoreRef
public import LeanVM.Guest.CoreNames

/-!
# The `inverse` hints are pinned

`verify_tables`, `verify_bus_gkr` and `da_row_shape` hold the guest's eight `inverse` hints. In each,
every `inverse` hint is immediately followed by `assertNe` on its value and its word
(`pinsInverse`), which makes it exact on every valuation holding the path (`inverse_exact`).
-/

namespace LeanVM.Guest.Core

@[expose] public section

theorem vt_inversePinned : Stmt.blockNextOk isInverse pinsInverse (fn% «verify_tables»).body = true := by
  decide +kernel

theorem vbg_inversePinned :
    Stmt.blockNextOk isInverse pinsInverse (fn% «verify_bus_gkr»).body = true := by
  decide +kernel

theorem drs_inversePinned :
    Stmt.blockNextOk isInverse pinsInverse (fn% «da_row_shape»).body = true := by
  decide +kernel

end
end LeanVM.Guest.Core
