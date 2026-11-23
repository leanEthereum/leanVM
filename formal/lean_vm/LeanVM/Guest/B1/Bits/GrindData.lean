/-
  LeanVM.Guest.B1.Bits.GrindData

  `grind_check`'s expansion as a template over its grind's bits, and its inlining into a caller.
-/

module

public import LeanVM.Guest.B1.Bits.Meaning
public import LeanVM.Guest.B1.Common.Find
public import LeanVM.Guest.Renumber

/-!
# `grind_check`'s body (TRIAGE #21)

`grind_check(word, tabs, nbits)` (`guests/lean_ethereum.py`, G below), `@inline`,
hints the lane `word`'s low limb from bit `nbits` on as `n_win` windows in the exponent, `W = n_win
- 1` of `WIN_TAB_BITS = 11` bits and a top one of `gcTop b` bits, range checks each
(`assert_window`, a range check against `g^(2^w - 1)`, `wBound w`), reads each window's pattern
from the table (`tabs[w]`), joins them by Horner's rule in `x^11` from the top window, shifts the
result by `x^nbits` and asserts it, and the word less it over `y`, in `K`. With the window
variables `.n 2 .. .n (W + 1)` (window `j` at `.n (2 + j)`) and the top window `.n (W + 2)`, the
word at `.n 0` and the tables at `.n 1`:

* `gcHead b`: the two hints, the top window's range check and read (`acc` at `W + 8`);
* `gcIterAt W i`, `1 ≤ i ≤ W`, from `c = W + 9 i`: window `W - i`'s range check and read, the
  running value times `x^11` plus it (`acc` at `c + 8`);
* `gcTailPre b`: the shift by `x^b`, the split's two `K` checks.

`gcPre b` is the whole expansion, values `.n 0 ..< .n (gcLen b)`. A caller inlining it renames
them (`gcRen o w tabs`): the word to its operand `w`, the tables to `tabs`, value `.n k`, `k ≥ 2`,
to `.n (o + k - 2)`, its own values from `o` on (`gcInlineT b o w tabs`).
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

/-- The shift by `x^b` and the split, from `e = 10 W + 9` (the running value at `e - 1`). -/
def gcTailPre (b : ℕ) : List Stmt :=
  [.atom (.const (.n (10 * gcW b + 9)) (word (2 ^ b) 0)),
    .atom (.mul (.n (10 * gcW b + 10)) (.n (10 * gcW b + 8)) (.n (10 * gcW b + 9))),
    .atom (.add (.n (10 * gcW b + 11)) (.n 0) (.n (10 * gcW b + 10))),
    .atom (.const (.n (10 * gcW b + 12)) (word 2 1)),
    .atom (.mul (.n (10 * gcW b + 13)) (.n (10 * gcW b + 11)) (.n (10 * gcW b + 12))),
    .atom (.const (.n (10 * gcW b + 14)) (word (2 ^ b) 0)),
    .atom (.mul (.n (10 * gcW b + 15)) (.n (10 * gcW b + 8)) (.n (10 * gcW b + 14))),
    .atom (.assertInK (.n (10 * gcW b + 13)) (.n (10 * gcW b + 15)))]

/-- **`grind_check`'s expansion**, from its word `.n 0` and its tables `.n 1`. -/
def gcPre (b : ℕ) : List Stmt :=
  gcHead b ++ ((List.range (gcW b)).map fun i => gcIterAt (gcW b) (i + 1)).flatten ++ gcTailPre b

/-- Its values: the word, the tables and its own, `.n 0 ..< .n (gcLen b)`. -/
def gcLen (b : ℕ) : ℕ := 10 * gcW b + 16

/-- **Inlined into a caller**: the word to `w`, the tables to `tabs`, its own value `.n k` to
`.n (o + k - 2)`. -/
def gcRen (o : ℕ) (w tabs : V) (v : V) : V :=
  if v.idx = 0 then w else if v.idx = 1 then tabs else .n (o + v.idx - 2)

/-- **`grind_check(w, tabs, b)` inlined**, its own values from `.n o`. -/
def gcInlineT (b o : ℕ) (w tabs : V) : List Stmt := Stmt.renameList (gcRen o w tabs) (gcPre b)

/-- The windows tile the lane above `b`: the top window is `1 ..= 11` bits and ends at bit `63`. -/
theorem gc_shape : ∀ b ∈ grindBitsDeployed,
    1 ≤ gcTop b ∧ gcTop b ≤ 11 ∧ b + 11 * gcW b + gcTop b = 64 := by
  decide

theorem gcW_pos : ∀ b ∈ grindBitsDeployed, 1 ≤ gcW b := by decide

/-- Every value of the expansion is one of its `gcLen b`. -/
theorem gcPre_vals : ∀ b ∈ grindBitsDeployed,
    (Stmt.valsList (gcPre b)).all (fun v => decide (v = .n v.idx ∧ v.idx < gcLen b)) = true := by
  decide

end
end LeanVM.Guest.B1
