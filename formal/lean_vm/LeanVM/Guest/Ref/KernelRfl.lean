/-
  LeanVM.Guest.Ref.KernelRfl

  `kernel_rfl`: an `↔` closed by `Iff.rfl`, its two sides' definitional equality left to the
  kernel.
-/

module

public meta import Lean.Elab.Tactic.Basic

/-!
# `kernel_rfl`

A condition `vc` computes for a long body is a deep term: comparing it with a recursive definition
of it by `exact Iff.rfl` exceeds the elaborator's recursion depth (`maxRecDepth`), though both
unfold to one term. `kernel_rfl` closes a goal `a ↔ b` by `Iff.refl a` without the elaborator's
check; the kernel checks `a` and `b` definitionally equal when the declaration is added, and a
failure fails the declaration. As for `vc`, `lake-build.py --dev` keeps the kernel on in a module
that uses it (`vc` there too).
-/

public meta section

namespace LeanVM.Guest.Ref

open Lean Elab Tactic Meta

/-- `kernel_rfl`: close `a ↔ b` by `Iff.rfl`, `a` and `b`'s definitional equality checked by the
kernel only. -/
elab "kernel_rfl" : tactic => do
  let g ← getMainGoal
  let some (a, _) := (← instantiateMVars (← g.getType)).iff? | throwError "kernel_rfl: not an `↔`"
  g.assign (mkApp (mkConst ``Iff.refl) a)
  replaceMainGoal []

end LeanVM.Guest.Ref
