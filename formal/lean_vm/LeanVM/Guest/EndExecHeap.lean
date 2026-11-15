/-
  LeanVM.Guest.EndExecHeap

  `HeapPops` from the reference tree popping the honest advised sizes under `Memory.heapSlots`.
-/

module

public import LeanVM.Guest.EndExecRef
public import LeanVM.Guest.EndExecHSlots

/-!
# The advised sizes of the reference run

`heapPops_of`: if every reference tree pops the honest `heap_sizes` entries under `heapSlots`, it does
under `advSlots` (`HeapPops`): the tree re-chooses the temporaries of a valid one (`heapPops_retemp`),
on which the two agree (`heapPops_advSlots`).
-/

namespace LeanVM.Guest.EndExec

open LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Memory

@[expose] public section

/-- **`HeapPops` from the reference trees' advised sizes under `heapSlots`.** -/
theorem heapPops_of (h : ∀ r : Ref, r.Ok → r.T.heapPops heapSlots = heapStream r) : HeapPops := by
  intro r hr
  obtain ⟨t, ν, hv, -, -, -, -, -, hT⟩ := hr.tree
  rw [← h r hr, hT, heapPops_retemp, heapPops_retemp, heapPops_advSlots hv]

end

end LeanVM.Guest.EndExec
