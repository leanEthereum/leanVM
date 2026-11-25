/-
  LeanVM.Guest.Ref.KernelIff

  `kernel_iff`: an `↔` whose two sides the kernel finds definitionally equal, checked at the tactic.
-/

module

public meta import Lean.Elab.Tactic.Basic

/-!
# `kernel_iff`

A condition `vc` computes for a long body is a deep term: comparing it with a recursive definition
of it by `exact Iff.rfl` exceeds the elaborator's recursion depth (`maxRecDepth`), though both
unfold to one term. `kernel_iff` closes `a ↔ b` by `Iff.refl a` once the kernel has found `a` and
`b` definitionally equal in the goal's local context. The check runs at the tactic whatever
`debug.skipKernelTC` says, and a failure fails the tactic.

PolyFun's `kernel_rfl` (`PolyFun.Logic.KernelRfl`) checks an equation by the kernel too, after
closing it over the local context as an auxiliary lemma. On such a condition the kernel's check of
the closed lemma is far slower than the check in context, so this tactic keeps the context.
-/

public meta section

namespace LeanVM.Guest.Ref

open Lean Elab Tactic Meta

/-- `kernel_iff`: close `a ↔ b` by `Iff.rfl`, after the kernel finds `a` and `b` definitionally
equal in the goal's local context. -/
elab "kernel_iff" : tactic => liftMetaFinishingTactic fun g => g.withContext do
  let t ← instantiateMVars (← g.getType)
  let some (a, b) := t.iff? | throwError "kernel_iff: the goal is not an `↔`{indentExpr t}"
  if t.hasMVar then throwError "kernel_iff: the goal contains metavariables{indentExpr t}"
  unless ← ofExceptKernelException (Kernel.isDefEq (← getEnv) (← getLCtx) a b) do
    throwError "kernel_iff: the kernel finds the two sides not definitionally equal{indentExpr t}"
  g.assign (mkApp (mkConst ``Iff.refl) a)

end LeanVM.Guest.Ref
