/-
  LeanVM.Guest.B1.VsC.Mono

  `CallCompletes` under a stronger precondition.
-/

module

public import LeanVM.Guest.Complete.CallComplete

namespace LeanVM.Guest.Complete

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory

@[expose] public section

/-- `CallCompletes` under a stronger precondition (`Complete/Straight.lean`'s `CallCompletes.mono` also weakens the post). -/
theorem CallCompletes.mono' {k : ℕ} {f : String} {args rets : List E} {P P' : Reader → Prop}
    {Q : Reader → Tree → Prop} (h : CallCompletes k f args rets P Q) (hP : ∀ rd, P' rd → P rd) :
    CallCompletes k f args rets P' Q := fun b => by
  obtain ⟨n, W, hW, h⟩ := h b
  exact ⟨n, W, hW, fun rd hl hw hp => h rd hl hw (hP rd hp)⟩

end
end LeanVM.Guest.Complete
