/-
  LeanVM.Guest.B1.Whir.TableKeysLr

  Every entry of `lrTable` is named by its numbers, by the kernel.
-/

module

public import LeanVM.Guest.B1.Whir.NameNums
public import LeanVM.Guest.B1.Whir.HelperAll

namespace LeanVM.Guest.B1.Whir

@[expose] public section

/-- An `lrTable` entry's numbers: queries, columns, high part's length and bits. -/
def lrKey (x : ℕ × ℕ × ℕ × ℕ × String × String) : List ℕ := [x.1, x.2.1, x.2.2.1, x.2.2.2.1]

set_option maxRecDepth 100000 in
theorem lr_names : ∀ e ∈ lrTable, e.1 = keyStr "level_residual__L" (lrKey e.2) := by
  decide +kernel

end
end LeanVM.Guest.B1.Whir
