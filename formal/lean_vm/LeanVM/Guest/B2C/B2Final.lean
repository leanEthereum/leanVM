/-
  LeanVM.Guest.B2C.B2Final

  B2's completeness at the deployed instance: every compiled function runs by the kernel's
  completeness checks, so the honest memory runs to the end within the counts.
-/

module

public import LeanVM.Guest.B2C.B2
public import LeanVM.Guest.B2C.Cplw
public import LeanVM.Guest.B2C.FrameAll
public import LeanVM.Guest.EndCompleteFinal

namespace LeanVM.Guest.B2C

@[expose] public section

/-- **Every compiled function runs** (`B2Hyps.run`), from the kernel's completeness checks. -/
theorem cplRun_all : ∀ j, 1 ≤ j → j < nFns → CplRun j := cplRun_of_ok Cplw.cplOk_all

/-- **B2's hypotheses**: every function runs, and every running instance's frame holds what the
check reads (the call sites of a path apart, by the completeness checks). -/
theorem b2Hyps : B2Hyps := ⟨cplRun_all, frameHolds_all (sitesApart_all_of Cplw.cplOk_all)⟩

/-- **Checker K's `b2`**: the honest memory runs from `main`'s entry to the end. -/
theorem b2cB2 : B2cB2 := b2_complete b2Hyps

/-- **Checker K's `count`**: a run of the honest memory to the end is within the counts. -/
theorem b2cCount : B2cCount := b2_count b2Hyps

end
end LeanVM.Guest.B2C
