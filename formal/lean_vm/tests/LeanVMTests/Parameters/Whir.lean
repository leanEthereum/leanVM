import LeanVM.Parameters.Whir

/-!
# WHIR parameter tests

The ladder against the second verifier's table (`python-verifier/verifier.py:912-937` at leanVM
`127510d14c98ade4e8a97646c44fa7f1ff5e752d`): the smallest stack at rate 1/2, the largest at rate
1/16, and one three-level case, each with its residual; the window's four edges rejected; the
table's shape; the block lengths of the first ladder; and a nearby false statement, the rate
exponent of level 1 under a wrong domain reduction.
-/

namespace LeanVMTests.Parameters.Whir

open LeanVM.Parameters.Whir

/-- `(222, 55)` at `μ = 15`, rate 1/2: level 0 folds six variables at rate exponent 1, level 1
four at exponent `1 + 6 - 3 = 4`, and five remain. -/
example : ladder 15 1 = some [⟨6, 1, 222⟩, ⟨4, 4, 55⟩] := by decide

example : residualLog 15 1 = 5 := by decide

/-- `(56, 32, 23, 18, 15, 12)` at `μ = 28`, rate 1/16: six levels, the exponent rising by three
once and then by one per level, and two variables remain. -/
example : ladder 28 4 =
    some [⟨6, 4, 56⟩, ⟨4, 7, 32⟩, ⟨4, 10, 23⟩, ⟨4, 13, 18⟩, ⟨4, 16, 15⟩, ⟨4, 19, 12⟩] := by
  decide

example : residualLog 28 4 = 2 := by decide

/-- `(223, 56, 30)` at `μ = 16`, rate 1/2: ten variables after level 0 is more than five, so a
third level folds the last four, and two remain. -/
example : ladder 16 1 = some [⟨6, 1, 223⟩, ⟨4, 4, 56⟩, ⟨4, 7, 30⟩] := by decide

example : residualLog 16 1 = 2 := by decide

/-! ## Outside the window -/

example : ladder 14 1 = none := by decide
example : ladder 29 1 = none := by decide
example : ladder 15 0 = none := by decide
example : ladder 15 5 = none := by decide

/-! ## The table and the constants -/

/-- Four rates, fourteen stack sizes. -/
example : queryTable.length = 4 ∧ ∀ row ∈ queryTable, row.length = 14 := by decide

/-- Level 0 of the first ladder is a code of length `2^10` (nine message variables at exponent
1), level 1 of length `2^9` (five at exponent 4). -/
example : ∀ levels, ladder 15 1 = some levels → blockLogs 15 levels = [10, 9] := by decide

example : oodSamples 0 = 0 ∧ oodSamples 1 = 1 ∧ oodSamples 5 = 1 := by decide

/-! ## A nearby false statement -/

/-- With the initial domain reduction applied as the subsequent one (one bit), level 1 would sit
at exponent `1 + 6 - 1 = 6`; with no reduction at all, at `7`. The pinned ladder has `4`. -/
example : ladder 15 1 ≠ some [⟨6, 1, 222⟩, ⟨4, 6, 55⟩] ∧
    ladder 15 1 ≠ some [⟨6, 1, 222⟩, ⟨4, 7, 55⟩] := by decide

end LeanVMTests.Parameters.Whir
