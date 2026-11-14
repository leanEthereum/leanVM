/-
  LeanVM.Guest.Exact.FreeCheck

  The functions whose own computed hints are `inverse` hints pinned by `assertNe`, and nothing computed below them,
  are exact for free: `da_row_shape` and `verify_bus_gkr`, by the kernel.
-/

module

public import LeanVM.Guest.Exact.Free
public import LeanVM.Guest.CoreRef
public import LeanVM.Guest.CoreNames

/-!
# Locally pinned, exact for free

`da_row_shape` and `verify_bus_gkr` each hold an `inverse` hint pinned by the `assertNe` after it, and no other
computed hint is in their subtrees (`exactFree`), so every valid tree of either is exact on every reader
(`every_exact_of_free`).
-/

namespace LeanVM.Guest.Memory

@[expose] public section

theorem da_row_shape_exactFree : ExactFreeG (name% «da_row_shape») :=
  exactFreeG_of (j := idx% «da_row_shape») (by decide +kernel)

theorem verify_bus_gkr_exactFree : ExactFreeG (name% «verify_bus_gkr») :=
  exactFreeG_of (j := idx% «verify_bus_gkr») (by decide +kernel)

end
end LeanVM.Guest.Memory
