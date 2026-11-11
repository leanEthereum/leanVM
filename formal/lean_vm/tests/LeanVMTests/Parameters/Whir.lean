import LeanVM.Parameters.Whir

/-!
# WHIR parameter tests

The ladder against the deployed verifier's (`WHIR_QUERIES` and `derive_config`,
`crates/verifier/src/whir.rs:26-72` at leanVM's `f128`, `71205cca4`): the smallest stack at rate 1/2, the
largest at rate 1/16, and one three-level case, each with its residual; the window's four edges
rejected; the table's shape; the block lengths of the first ladder; and a nearby false statement,
the rate exponent of level 1 under a wrong domain reduction.
-/

namespace LeanVMTests.Parameters.Whir

open LeanVM.Parameters.Whir

/-- `(238, 63)` at `μ = 15`, rate 1/2: level 0 folds six variables at rate exponent 1, level 1
four at exponent `1 + 6 - 3 = 4`, and five remain. -/
example : ladder 15 1 = some [⟨6, 1, 238⟩, ⟨4, 4, 63⟩] := by decide

example : residualLog 15 1 = 5 := by decide

/-- `(55, 32, 22, 18, 15, 13)` at `μ = 28`, rate 1/16: six levels, the exponent rising by three
once and then by one per level, and two variables remain. -/
example : ladder 28 4 =
    some [⟨6, 4, 55⟩, ⟨4, 7, 32⟩, ⟨4, 10, 22⟩, ⟨4, 13, 18⟩, ⟨4, 16, 15⟩, ⟨4, 19, 13⟩] := by
  decide

example : residualLog 28 4 = 2 := by decide

/-- `(230, 60, 42)` at `μ = 16`, rate 1/2: ten variables after level 0 is more than five, so a
third level folds the last four, and two remain. -/
example : ladder 16 1 = some [⟨6, 1, 230⟩, ⟨4, 4, 60⟩, ⟨4, 7, 42⟩] := by decide

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

example : oodSamplesAt 0 = 0 ∧ oodSamplesAt 1 = 1 ∧ oodSamplesAt 5 = 1 := by decide

/-! ## A nearby false statement -/

/-- With the initial domain reduction applied as the subsequent one (one bit), level 1 would sit
at exponent `1 + 6 - 1 = 6`; with no reduction at all, at `7`. The pinned ladder has `4`. -/
example : ladder 15 1 ≠ some [⟨6, 1, 238⟩, ⟨4, 6, 63⟩] ∧
    ladder 15 1 ≠ some [⟨6, 1, 238⟩, ⟨4, 7, 63⟩] := by decide

end LeanVMTests.Parameters.Whir
