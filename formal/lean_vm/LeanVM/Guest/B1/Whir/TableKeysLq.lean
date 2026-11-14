/-
  LeanVM.Guest.B1.Whir.TableKeysLq

  Every entry of `lqTable` is named by its numbers, by the kernel.
-/

module

public import LeanVM.Guest.B1.Whir.NameNums
public import LeanVM.Guest.B1.Whir.HelperTables
public import LeanVM.Guest.B1.Whir.HelperT

namespace LeanVM.Guest.B1.Whir

@[expose] public section

/-- An `lqTable` entry's numbers. -/
def lqKey (x : ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ) : List ℕ :=
  [x.1, x.2.1, x.2.2.1, x.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.1, x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1,
    x.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2]

set_option maxRecDepth 100000 in
theorem lq_names_take : ∀ e ∈ lqTable.take 96, e.1 = keyStr "level_queries__L" (lqKey e.2) := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem lq_names_drop : ∀ e ∈ lqTable.drop 96, e.1 = keyStr "level_queries__L" (lqKey e.2) := by
  decide +kernel

/-- Every entry of `lqTable` is named by its numbers, in two kernel checks to bound the memory. -/
theorem lq_names : ∀ e ∈ lqTable, e.1 = keyStr "level_queries__L" (lqKey e.2) := by
  intro e he
  rw [← List.take_append_drop 96 lqTable, List.mem_append] at he
  exact he.elim (lq_names_take e) (lq_names_drop e)

end
end LeanVM.Guest.B1.Whir
