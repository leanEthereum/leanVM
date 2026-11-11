import LeanVM.Parameters.Whir

/-!
# WHIR parameter tests

The ladder against the deployed verifier's (`WHIR_QUERIES` and `derive_config`,
`crates/verifier/src/whir.rs`): the smallest stack at rate 1/2, a three-level case, the largest at
rate 1/16, and `(28, 4)`, each with its residual; the window's four edges rejected; the table's
shape; the block lengths of the first ladder; and a nearby false statement, the rate exponent of
level 1 under a wrong domain reduction.
-/

namespace LeanVMTests.Parameters.Whir

open LeanVM.Parameters.Whir

/-- `(56, 32, 23, 18, 15, 12)` at `μ = 28`, rate 1/16: six levels, the exponent rising by three
once and then by one per level, and two variables remain. -/
example : ladder 28 4 =
    some [⟨6, 4, 56⟩, ⟨4, 7, 32⟩, ⟨4, 10, 23⟩, ⟨4, 13, 18⟩, ⟨4, 16, 15⟩, ⟨4, 19, 12⟩] := by
  decide

example : residualLog 28 4 = 2 := by decide

/-- `(223, 56, 30)` at `μ = 16`, the smallest stack, rate 1/2: level 0 folds six variables at rate
exponent 1, level 1 four at exponent `1 + 6 - 3 = 4`; six variables after level 1 are more than
five, so a third level folds four more, and two remain. -/
example : ladder 16 1 = some [⟨6, 1, 223⟩, ⟨4, 4, 56⟩, ⟨4, 7, 30⟩] := by decide

example : residualLog 16 1 = 2 := by decide

/-- `(57, 33, 23, 18, 15, 12)` at `μ = 30`, the largest stack, rate 1/16: six levels, and four
variables remain. -/
example : ladder 30 4 =
    some [⟨6, 4, 57⟩, ⟨4, 7, 33⟩, ⟨4, 10, 23⟩, ⟨4, 13, 18⟩, ⟨4, 16, 15⟩, ⟨4, 19, 12⟩] := by
  decide

example : residualLog 30 4 = 4 := by decide

/-! ## Outside the window -/

example : ladder 15 1 = none := by decide
example : ladder 31 1 = none := by decide
example : ladder 16 0 = none := by decide
example : ladder 16 5 = none := by decide

/-! ## The table and the constants -/

/-- Four rates, fifteen stack sizes. -/
example : queryTable.length = 4 ∧ ∀ row ∈ queryTable, row.length = 15 := by decide

/-- Level 0 of the smallest ladder is a code of length `2^11` (ten message variables at exponent
1), level 1 of length `2^10` (six at exponent 4), level 2 of length `2^9` (two at exponent 7). -/
example : ∀ levels, ladder 16 1 = some levels → blockLogs 16 levels = [11, 10, 9] := by decide

example : oodSamples 0 = 0 ∧ oodSamples 1 = 1 ∧ oodSamples 5 = 1 := by decide

/-! ## A nearby false statement -/

/-- With the initial domain reduction applied as the subsequent one (one bit), level 1 would sit
at exponent `1 + 6 - 1 = 6`; with no reduction at all, at `7`. The pinned ladder has `4`. -/
example : ladder 16 1 ≠ some [⟨6, 1, 223⟩, ⟨4, 6, 56⟩, ⟨4, 9, 30⟩] ∧
    ladder 16 1 ≠ some [⟨6, 1, 223⟩, ⟨4, 7, 56⟩, ⟨4, 11, 30⟩] := by decide

end LeanVMTests.Parameters.Whir
