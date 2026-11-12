/-
  LeanVM.Guest.Memory.GuestWf

  The guest's core IR is well formed (`Program.Wf`), from its memory check (`memAll`).
-/

module

public import LeanVM.Guest.Memory.GuestMem

/-!
# The guest is well formed

Every `callIf` of the guest names a loop helper taking its arguments, and every `match` and fused
dispatch has at most `2^64 - 1` arms; so every derivation of the guest's `Program.Rel` is an honest
evaluation (`Program.Rel.tree`).
-/

namespace LeanVM.Guest

open Core Memory

@[expose] public section

/-- **The guest's core IR is well formed.** -/
theorem coreProgram_wf : coreProgram.Wf := memAll_wf memAll

end
end LeanVM.Guest
