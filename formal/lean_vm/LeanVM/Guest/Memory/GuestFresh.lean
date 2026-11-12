/-
  LeanVM.Guest.Memory.GuestFresh

  The guest's core IR has fresh range-check temporaries (`Program.Fresh`), from its memory check
  (`memAll`).
-/

module

public import LeanVM.Guest.Memory.GuestMem

namespace LeanVM.Guest

open Core Memory

@[expose] public section

/-- **The guest's range-check temporaries are fresh.** -/
theorem coreProgram_fresh : coreProgram.Fresh := memAll_fresh memAll

end
end LeanVM.Guest
