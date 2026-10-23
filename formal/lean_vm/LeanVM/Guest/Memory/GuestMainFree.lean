/-
  LeanVM.Guest.Memory.GuestMainFree

  No function of the guest calls `main`, so the paths of every other function call only functions
  other than `main` (`coreProgram_callsIn_noMain`), and bounds transfer between frame sizes agreeing
  but at `main`.
-/

module

public import LeanVM.Guest.Memory.GuestMainFree.All
public import LeanVM.Guest.Memory.SizeTransfer

namespace LeanVM.Guest

open Core Memory

@[expose] public section

/-- **No path of the guest calls `main`.** -/
theorem coreProgram_callsIn_noMain : CallsIn coreProgram (· ≠ "main") := by
  refine callsIn_of_callees fun f _ fn hfn g hg => ?_
  obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp (List.mem_of_find?_eq_some hfn)
  have hc := mainFree_all j (by rw [coreProgram_length] at hj; exact hj)
  unfold mainFreeJ at hc
  rw [List.getElem?_eq_getElem hj] at hc
  simpa using List.all_eq_true.mp hc g hg

end
end LeanVM.Guest
