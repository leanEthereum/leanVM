/-
  LeanVM.Guest.B1.Bits.GrindData

  `grind_check`'s expansion as a template over its grind's bits, checked against every deployed
  specialization by kernel evaluation.
-/

module

public import LeanVM.Guest.B1.Bits.Meaning
public import LeanVM.Guest.B1.Common.Find

/-!
# `grind_check`'s body (TRIAGE #21)

`grind_check(word, tabs, nbits)` (`crates/rec_aggregation/guests/lean_ethereum.py`, G below)
hints the lane `word`'s low limb from bit `nbits` on as `n_win` windows in the exponent, `W = n_win
- 1` of `WIN_TAB_BITS = 11` bits and a top one of `gcTop b` bits, range checks each
(`assert_window`, a range check against `g^(2^w - 1)`, `wBound w`), reads each window's pattern
from the table (`tabs[w]`), joins them by Horner's rule in `x^11` from the top window, shifts the
result by `x^nbits` and asserts it, and the word less it over `y`, in `K`. With the window
variables `.n 2 .. .n (W + 1)` (window `j` at `.n (2 + j)`) and the top window `.n (W + 2)`:

* `gcHead b`: the two hints, the top window's range check and read (`acc` at `W + 8`);
* `gcIterAt W i`, `1 ≤ i ≤ W`, from `c = W + 9 i`: window `W - i`'s range check and read, the
  running value times `x^11` plus it (`acc` at `c + 8`);
* `gcTail b`: the shift by `x^b`, the split's two `K` checks, the return.

`grind_check_found`: every deployed `grind_check__L{b}` is `gcBodyT b`, with parameters `[.n 0,
.n 1]`. Kept apart from the proof (`Bits/Grind.lean`) so that the kernel's comparison runs once.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.Verifier

@[expose] public section

/-- The full windows below the top one, `n_win - 1`. -/
def gcW (b : ℕ) : ℕ := (64 - b + 10) / 11 - 1

/-- The top window's width. -/
def gcTop (b : ℕ) : ℕ := 64 - b - 11 * gcW b

/-- `assert log(w) < 2^width`'s bound, `g^(2^width - 1)` (`assert_window`). -/
def wBound (width : ℕ) : E := E.ofLimbs (gpowK (2 ^ width - 1)) 0

/-- The top window's hints, range check and read: the running value at `W + 8`. -/
def gcHead (b : ℕ) : List Stmt :=
  [.atom (.hint (.windowsExp (.n 0) b 11 (gcW b)
      (.stack ((List.range (gcW b)).map fun j => .n (2 + j))))),
    .atom (.hint (.windowsExp (.n 0) (b + 11 * gcW b) (gcTop b) 1 (.stack [.n (gcW b + 2)]))),
    .atom (.const (.n (gcW b + 3)) (wBound (gcTop b))),
    .atom (.rangeCheck (.n (gcW b + 2)) (.n (gcW b + 4)) (.n (gcW b + 5)) (.n (gcW b + 6))
      (.n (gcW b + 3))),
    .atom (.mul (.n (gcW b + 7)) (.n 1) (.n (gcW b + 2))),
    .atom (.load (.n (gcW b + 8)) (.n (gcW b + 7)) 0)]

/-- Horner step `i` (`1 ≤ i ≤ W`) from `c = W + 9 i`: window `W - i` (`.n (W + 2 - i)`) range
checked and read, the running value `c - 1` times `x^11` plus it, at `c + 8`. -/
def gcIterAt (W i : ℕ) : List Stmt :=
  [.atom (.const (.n (W + 9 * i)) (wBound 11)),
    .atom (.rangeCheck (.n (W + 2 - i)) (.n (W + 9 * i + 1)) (.n (W + 9 * i + 2))
      (.n (W + 9 * i + 3)) (.n (W + 9 * i))),
    .atom (.const (.n (W + 9 * i + 4)) (word 2048 0)),
    .atom (.mul (.n (W + 9 * i + 5)) (.n (W + 9 * i - 1)) (.n (W + 9 * i + 4))),
    .atom (.mul (.n (W + 9 * i + 6)) (.n 1) (.n (W + 2 - i))),
    .atom (.load (.n (W + 9 * i + 7)) (.n (W + 9 * i + 6)) 0),
    .atom (.add (.n (W + 9 * i + 8)) (.n (W + 9 * i + 5)) (.n (W + 9 * i + 7)))]

/-- The shift by `x^b`, the split, the return, from `e = 10 W + 9` (the running value at
`e - 1`). -/
def gcTail (b : ℕ) : List Stmt :=
  [.atom (.const (.n (10 * gcW b + 9)) (word (2 ^ b) 0)),
    .atom (.mul (.n (10 * gcW b + 10)) (.n (10 * gcW b + 8)) (.n (10 * gcW b + 9))),
    .atom (.add (.n (10 * gcW b + 11)) (.n 0) (.n (10 * gcW b + 10))),
    .atom (.const (.n (10 * gcW b + 12)) (word 2 1)),
    .atom (.mul (.n (10 * gcW b + 13)) (.n (10 * gcW b + 11)) (.n (10 * gcW b + 12))),
    .atom (.const (.n (10 * gcW b + 14)) (word (2 ^ b) 0)),
    .atom (.mul (.n (10 * gcW b + 15)) (.n (10 * gcW b + 8)) (.n (10 * gcW b + 14))),
    .atom (.assertInK (.n (10 * gcW b + 13)) (.n (10 * gcW b + 15))),
    .ret []]

/-- **`grind_check__L{b}`'s expansion.** -/
def gcBodyT (b : ℕ) : List Stmt :=
  gcHead b ++ ((List.range (gcW b)).map fun i => gcIterAt (gcW b) (i + 1)).flatten ++ gcTail b

/-- The windows tile the lane above `b`: the top window is `1 ..= 11` bits and ends at bit `63`. -/
theorem gc_shape : ∀ b ∈ grindBitsDeployed,
    1 ≤ gcTop b ∧ gcTop b ≤ 11 ∧ b + 11 * gcW b + gcTop b = 64 := by
  decide

set_option maxRecDepth 100000 in
theorem grind_check_found_2 : coreProgram.find? (grindCheckName 2) = some Data.core431 ∧
    Data.core431.params = [.n 0, .n 1] ∧ Data.core431.body = gcBodyT 2 :=
  ⟨coreProgram_find?_at (j := 431) rfl, rfl,
    stmtsEqb_sound (by decide +kernel)⟩

set_option maxRecDepth 100000 in
theorem grind_check_found_3 : coreProgram.find? (grindCheckName 3) = some Data.core442 ∧
    Data.core442.params = [.n 0, .n 1] ∧ Data.core442.body = gcBodyT 3 :=
  ⟨coreProgram_find?_at (j := 442) rfl, rfl,
    stmtsEqb_sound (by decide +kernel)⟩

set_option maxRecDepth 100000 in
theorem grind_check_found_7 : coreProgram.find? (grindCheckName 7) = some Data.core89 ∧
    Data.core89.params = [.n 0, .n 1] ∧ Data.core89.body = gcBodyT 7 :=
  ⟨coreProgram_find?_at (j := 89) rfl, rfl,
    stmtsEqb_sound (by decide +kernel)⟩

set_option maxRecDepth 100000 in
theorem grind_check_found_13 : coreProgram.find? (grindCheckName 13) = some Data.core334 ∧
    Data.core334.params = [.n 0, .n 1] ∧ Data.core334.body = gcBodyT 13 :=
  ⟨coreProgram_find?_at (j := 334) rfl, rfl,
    stmtsEqb_sound (by decide +kernel)⟩

set_option maxRecDepth 100000 in
theorem grind_check_found_15 : coreProgram.find? (grindCheckName 15) = some Data.core307 ∧
    Data.core307.params = [.n 0, .n 1] ∧ Data.core307.body = gcBodyT 15 :=
  ⟨coreProgram_find?_at (j := 307) rfl, rfl,
    stmtsEqb_sound (by decide +kernel)⟩

set_option maxRecDepth 100000 in
theorem grind_check_found_17 : coreProgram.find? (grindCheckName 17) = some Data.core447 ∧
    Data.core447.params = [.n 0, .n 1] ∧ Data.core447.body = gcBodyT 17 :=
  ⟨coreProgram_find?_at (j := 447) rfl, rfl,
    stmtsEqb_sound (by decide +kernel)⟩

set_option maxRecDepth 100000 in
theorem grind_check_found_18 : coreProgram.find? (grindCheckName 18) = some Data.core448 ∧
    Data.core448.params = [.n 0, .n 1] ∧ Data.core448.body = gcBodyT 18 :=
  ⟨coreProgram_find?_at (j := 448) rfl, rfl,
    stmtsEqb_sound (by decide +kernel)⟩

set_option maxRecDepth 100000 in
theorem grind_check_found_19 : coreProgram.find? (grindCheckName 19) = some Data.core449 ∧
    Data.core449.params = [.n 0, .n 1] ∧ Data.core449.body = gcBodyT 19 :=
  ⟨coreProgram_find?_at (j := 449) rfl, rfl,
    stmtsEqb_sound (by decide +kernel)⟩

set_option maxRecDepth 100000 in
theorem grind_check_found_20 : coreProgram.find? (grindCheckName 20) = some Data.core450 ∧
    Data.core450.params = [.n 0, .n 1] ∧ Data.core450.body = gcBodyT 20 :=
  ⟨coreProgram_find?_at (j := 450) rfl, rfl,
    stmtsEqb_sound (by decide +kernel)⟩

set_option maxRecDepth 100000 in
theorem grind_check_found_21 : coreProgram.find? (grindCheckName 21) = some Data.core451 ∧
    Data.core451.params = [.n 0, .n 1] ∧ Data.core451.body = gcBodyT 21 :=
  ⟨coreProgram_find?_at (j := 451) rfl, rfl,
    stmtsEqb_sound (by decide +kernel)⟩

set_option maxRecDepth 100000 in
theorem grind_check_found_22 : coreProgram.find? (grindCheckName 22) = some Data.core452 ∧
    Data.core452.params = [.n 0, .n 1] ∧ Data.core452.body = gcBodyT 22 :=
  ⟨coreProgram_find?_at (j := 452) rfl, rfl,
    stmtsEqb_sound (by decide +kernel)⟩

set_option maxRecDepth 100000 in
theorem grind_check_found_23 : coreProgram.find? (grindCheckName 23) = some Data.core453 ∧
    Data.core453.params = [.n 0, .n 1] ∧ Data.core453.body = gcBodyT 23 :=
  ⟨coreProgram_find?_at (j := 453) rfl, rfl,
    stmtsEqb_sound (by decide +kernel)⟩

set_option maxRecDepth 100000 in
theorem grind_check_found_24 : coreProgram.find? (grindCheckName 24) = some Data.core454 ∧
    Data.core454.params = [.n 0, .n 1] ∧ Data.core454.body = gcBodyT 24 :=
  ⟨coreProgram_find?_at (j := 454) rfl, rfl,
    stmtsEqb_sound (by decide +kernel)⟩

set_option maxRecDepth 100000 in
theorem grind_check_found_25 : coreProgram.find? (grindCheckName 25) = some Data.core455 ∧
    Data.core455.params = [.n 0, .n 1] ∧ Data.core455.body = gcBodyT 25 :=
  ⟨coreProgram_find?_at (j := 455) rfl, rfl,
    stmtsEqb_sound (by decide +kernel)⟩

set_option maxRecDepth 100000 in
theorem grind_check_found_26 : coreProgram.find? (grindCheckName 26) = some Data.core456 ∧
    Data.core456.params = [.n 0, .n 1] ∧ Data.core456.body = gcBodyT 26 :=
  ⟨coreProgram_find?_at (j := 456) rfl, rfl,
    stmtsEqb_sound (by decide +kernel)⟩

set_option maxRecDepth 100000 in
theorem grind_check_found_27 : coreProgram.find? (grindCheckName 27) = some Data.core457 ∧
    Data.core457.params = [.n 0, .n 1] ∧ Data.core457.body = gcBodyT 27 :=
  ⟨coreProgram_find?_at (j := 457) rfl, rfl,
    stmtsEqb_sound (by decide +kernel)⟩

set_option maxRecDepth 100000 in
theorem grind_check_found_28 : coreProgram.find? (grindCheckName 28) = some Data.core458 ∧
    Data.core458.params = [.n 0, .n 1] ∧ Data.core458.body = gcBodyT 28 :=
  ⟨coreProgram_find?_at (j := 458) rfl, rfl,
    stmtsEqb_sound (by decide +kernel)⟩

set_option maxRecDepth 100000 in
theorem grind_check_found_29 : coreProgram.find? (grindCheckName 29) = some Data.core459 ∧
    Data.core459.params = [.n 0, .n 1] ∧ Data.core459.body = gcBodyT 29 :=
  ⟨coreProgram_find?_at (j := 459) rfl, rfl,
    stmtsEqb_sound (by decide +kernel)⟩

set_option maxRecDepth 100000 in
theorem grind_check_found_30 : coreProgram.find? (grindCheckName 30) = some Data.core460 ∧
    Data.core460.params = [.n 0, .n 1] ∧ Data.core460.body = gcBodyT 30 :=
  ⟨coreProgram_find?_at (j := 460) rfl, rfl,
    stmtsEqb_sound (by decide +kernel)⟩

/-- **Every deployed `grind_check` is the template.** -/
theorem grind_check_found : ∀ b ∈ grindBitsDeployed, ∃ fn : Fn,
    coreProgram.find? (grindCheckName b) = some fn ∧ fn.params = [.n 0, .n 1] ∧
      fn.body = gcBodyT b := by
  intro b hb
  simp only [grindBitsDeployed, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨_, grind_check_found_2⟩
  · exact ⟨_, grind_check_found_3⟩
  · exact ⟨_, grind_check_found_7⟩
  · exact ⟨_, grind_check_found_13⟩
  · exact ⟨_, grind_check_found_15⟩
  · exact ⟨_, grind_check_found_17⟩
  · exact ⟨_, grind_check_found_18⟩
  · exact ⟨_, grind_check_found_19⟩
  · exact ⟨_, grind_check_found_20⟩
  · exact ⟨_, grind_check_found_21⟩
  · exact ⟨_, grind_check_found_22⟩
  · exact ⟨_, grind_check_found_23⟩
  · exact ⟨_, grind_check_found_24⟩
  · exact ⟨_, grind_check_found_25⟩
  · exact ⟨_, grind_check_found_26⟩
  · exact ⟨_, grind_check_found_27⟩
  · exact ⟨_, grind_check_found_28⟩
  · exact ⟨_, grind_check_found_29⟩
  · exact ⟨_, grind_check_found_30⟩

end
end LeanVM.Guest.B1
