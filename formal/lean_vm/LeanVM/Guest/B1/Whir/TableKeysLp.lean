/-
  LeanVM.Guest.B1.Whir.TableKeysLp

  Every entry of `lpTable` is named by its numbers, by the kernel.
-/

module

public import LeanVM.Guest.B1.Whir.NameNums
public import LeanVM.Guest.B1.Whir.HelperTables
public import LeanVM.Guest.B1.Whir.HelperT

namespace LeanVM.Guest.B1.Whir

@[expose] public section

/-- An `lpTable` entry's numbers: squeezes, depth, cap depth. -/
def lpKey (x : ℕ × String × ℕ × ℕ) : List ℕ := [x.1, x.2.2.1, x.2.2.2]

set_option maxRecDepth 100000 in
theorem lp_names : ∀ e ∈ lpTable, e.1 = keyStr "level_positions__L" (lpKey e.2) := by
  decide +kernel

end
end LeanVM.Guest.B1.Whir
