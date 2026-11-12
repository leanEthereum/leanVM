/-
  LeanVM.Guest.Memory.GuestMainFree

  No function of the guest calls `main` (`coreProgram_callsIn_noMain`), from its memory check
  (`memAll`).
-/

module

public import LeanVM.Guest.Memory.GuestMem
public import LeanVM.Guest.Memory.SizeTransfer

/-!
# No function of the guest calls `main`

No callee of any function is `main` (`mainFree_all`), so the paths of every function call only
functions other than `main` (`coreProgram_callsIn_noMain`), and bounds transfer between frame
sizes agreeing but at `main`.
-/

namespace LeanVM.Guest

open Core Memory

@[expose] public section

/-- No callee of function `j` is `main`. -/
noncomputable def mainFreeJ (j : ℕ) : Bool :=
  match coreProgram[j]? with
  | none => true
  | some fn => (Stmt.blockCallees fn.body).all fun g => decide (g ≠ "main")

/-- **No function calls `main`**, function by function. -/
theorem mainFree_all : ∀ j < coreProgram.length, mainFreeJ j = true := by
  intro j hj
  unfold mainFreeJ
  rw [List.getElem?_eq_getElem hj, List.all_eq_true]
  exact fun g hg => decide_eq_true (memAll_callees memAll hj g hg)

/-- **No path of the guest calls `main`.** -/
theorem coreProgram_callsIn_noMain : CallsIn coreProgram (· ≠ "main") := by
  refine callsIn_of_callees fun f _ fn hfn g hg => ?_
  obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp (List.mem_of_find?_eq_some hfn)
  exact memAll_callees memAll hj g hg

end
end LeanVM.Guest
