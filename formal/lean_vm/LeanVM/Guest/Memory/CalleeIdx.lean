/-
  LeanVM.Guest.Memory.CalleeIdx

  A callee's index (`calleeIdx`) names it (`calleeIdx_spec`).
-/

module

public import LeanVM.Guest.Memory.GuestCalleesOk
public import LeanVM.Guest.Memory.GuestIdx

namespace LeanVM.Guest.Memory

open LeanVM.Guest.Core LeanVM.Guest

@[expose] public section

/-- **A callee's index names it.** -/
theorem calleeIdx_spec {j k : ℕ} {g : String} (h : calleeIdx j g = some k) :
    (coreProgram[k]?).map Fn.name = some g := by
  unfold calleeIdx at h
  have hm := List.mem_of_find?_eq_some h
  have hn := List.find?_some h
  simp only [decide_eq_true_eq] at hn
  have hk : k < coreProgram.length := by
    unfold Data.calleesJ at hm
    rcases hf : Data.calleeT.find j with _ | l
    · rw [hf] at hm; simp at hm
    · rw [hf] at hm
      have := NTree.find_all Data.calleeT_lt hf
      have := List.all_eq_true.mp this k hm
      simpa [coreProgram_length] using this
  exact Data.nameT_spec hk hn

end
end LeanVM.Guest.Memory
