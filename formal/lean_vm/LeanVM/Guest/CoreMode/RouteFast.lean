/-
  LeanVM.Guest.CoreMode.RouteFast

  The route's pointer check with each value's cell looked up in a trie of the certificate's cells,
  equal to the check as stated (`ptrCellB_eq`), for the kernel.
-/

module

public import LeanVM.Guest.CoreMode.Route
public import LeanVM.Guest.Bridge.JumpCellsPack

/-!
# Cells by trie

`B2C.cellJ j v` reads entry `v.idx` of the flattened list of function `j`'s cells. The kernel walks
that list cons by cons at every read and keeps each step, so a long body's pointer check
(`ptrCellB`, a read for each `DEREF`) costs the product of its pointers and its cells, in time and
memory. `cellT` reads the same entry from the cells as a trie built once by halves
(`Bridge.buildT`), a read the depth of the trie; `cellT_eq` and `ptrCellB_eq` say it is the same
number and the same check, so a certificate rewrites with them before the kernel decides it.
-/

namespace LeanVM.Guest.CoreMode

open LeanVM.Guest LeanVM.Guest.Core

@[expose] public section

/-- Function `j`'s cells as a trie, value `k`'s at key `k`. -/
noncomputable def locsT (j : ℕ) : Exec.Trie ℕ := Bridge.buildT 32 (certOf j).locs

/-- `B2C.cellJ`, read from `locsT`. -/
noncomputable def cellT (j : ℕ) (v : V) : ℕ :=
  bif Nat.blt (v.idx + 1) (2 ^ 32) then (Check.getF (locsT j) v.idx).getD 0 else B2C.cellJ j v

theorem cellT_eq (j : ℕ) (v : V) : cellT j v = B2C.cellJ j v := by
  unfold cellT
  cases h : Nat.blt (v.idx + 1) (2 ^ 32)
  · rfl
  · rw [Bool.cond_true, locsT, Bridge.getF_buildT 32 _ _ (Nat.blt_eq.mp h), B2C.cellJ,
      List.getD_eq_getElem?_getD]

/-- `ptrCellB`, its cells read by `cellT`. -/
noncomputable def ptrCellT (j : ℕ) : Stmt → Bool
  | .atom a => match ptrOf a with
    | some p => ((Bridge.extraOf j).lookup p.idx).isNone && decide (p.idx < 2 ^ 30) &&
      decide (2 ≤ cellT j p) && decide (cellT j p < B2C.fsN j)
    | none => true
  | _ => true

theorem ptrCellB_eq (j : ℕ) : ptrCellB j = ptrCellT j := by
  funext s
  cases s with
  | atom a => cases h : ptrOf a <;> simp only [ptrCellB, ptrCellT, h, cellT_eq]
  | _ => rfl

end

end LeanVM.Guest.CoreMode
