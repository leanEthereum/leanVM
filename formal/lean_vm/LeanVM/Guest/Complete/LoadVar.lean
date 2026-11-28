/-
  LeanVM.Guest.Complete.LoadVar

  An atom placing nothing, writing no heap word, and loading only through named values: the check
  a large body passes chunk by chunk.
-/

module

public import LeanVM.Guest.Exact.Atoms
public import LeanVM.Guest.Memory.Placed
public import LeanVM.Guest.Memory.HintsCheck
public import LeanVM.Guest.Renumber

/-!
# Loads through named values

`loadVarB ps a`: `a` places nothing (`atomUnplaced`), a hint writes no heap word, and a load reads
through one of the values `.n v` of `ps` (value, cells) at an offset below its cells. A body
checked by `Stmt.atomsAll` distributes over `++` (`Stmt.atomsAll_append`), and so does
`Stmt.pureList` (`pureList_append`), so a large body is checked by chunks.

`quietB a`: `a` places nothing and a hint writes no heap word, loads unrestricted.

`l2Loads`: `main_loop2`'s, its coverage cell (`.n 62`) and its claim's four cells (`.n 65`).
-/

namespace LeanVM.Guest.Complete

open LeanVM.Guest.Core LeanVM.Guest.Memory

@[expose] public section

/-- **An atom placing nothing, hinting no heap word, loading through `ps`** (value, cells). -/
def loadVarB (ps : List (ℕ × ℕ)) (a : Atom) : Bool :=
  atomUnplaced a && match a with
    | .hint h => ((hintDest? h).bind destHeap?).isNone
    | .load _ p off => ps.any fun q => p == .n q.1 && decide (off < q.2)
    | _ => true

/-- **An atom placing nothing and hinting no heap word.** -/
def quietB (a : Atom) : Bool :=
  atomUnplaced a && match a with
    | .hint h => ((hintDest? h).bind destHeap?).isNone
    | _ => true

/-- `main_loop2`'s loads: the coverage cell, the claim's four cells. -/
abbrev l2Loads : List (ℕ × ℕ) := [(62, 1), (65, 4)]

theorem pureList_append (S : List String) : ∀ (l l' : List Stmt),
    Stmt.pureList S (l ++ l') = (Stmt.pureList S l && Stmt.pureList S l')
  | [], _ => by simp [Stmt.pureList]
  | s :: l, l' => by
      simp only [List.cons_append, Stmt.pureList, pureList_append S l l', Bool.and_assoc]

end
end LeanVM.Guest.Complete
