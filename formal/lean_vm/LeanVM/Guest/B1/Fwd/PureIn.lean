/-
  LeanVM.Guest.B1.Fwd.PureIn

  `Program.PureIn` as a kernel check: a set of functions placing nothing.
-/

module

public import LeanVM.Guest.Memory.Uniform

namespace LeanVM.Guest.B1.Tables

open LeanVM.Guest.Core LeanVM.Guest.Memory

@[expose] public section

/-- `Program.PureIn`, as a check. -/
def pureInB (P : Core.Program) (S : List String) : Bool :=
  S.all fun g ↦ match P.find? g with
    | some fn => Stmt.pureList S fn.body
    | none => true

theorem pureIn_of_pureInB {P : Core.Program} {S : List String} (h : pureInB P S = true) :
    P.PureIn S := by
  intro g hg fn hf
  have := List.all_eq_true.mp h g hg
  simpa [hf] using this

end
end LeanVM.Guest.B1.Tables
