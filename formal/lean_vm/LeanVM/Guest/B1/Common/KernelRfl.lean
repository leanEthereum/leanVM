/-
  LeanVM.Guest.B1.Common.KernelRfl

  `kernel_rfl` as a tactic: an equation closed by `rfl` that only the kernel checks.
-/

module

public meta import Lean.Elab.Tactic.ElabTerm
public meta import Lean.Meta.Tactic.AuxLemma

/-!
# `kernel_rfl`, the tactic

The command `kernel_rfl x : a = b` (`Guest/KernelLit.lean`) needs the equation as a statement of
its own. The tactic closes an equation where a term needs one, such as the body equation passed
to a lemma: it adds the auxiliary theorem `a = b` by `rfl` and lets the kernel alone check it, as
`decide +kernel` does for a decision. The kernel compares the two sides structurally and unfolds
each only as far as the comparison needs, where `stmtsEqb_sound (by decide +kernel)` evaluates a
Boolean comparator on both sides in full.
-/

public meta section

namespace LeanVM.Guest.B1

open Lean Elab Tactic Meta

/-- `kernel_rfl` closes a goal `a = b`, with neither metavariables nor local hypotheses in it, by
`rfl` checked by the kernel alone, as an auxiliary theorem. -/
syntax (name := kernelRflTac) "kernel_rfl" : tactic

@[tactic kernelRflTac] def evalKernelRfl : Tactic := fun _ =>
  closeMainGoalUsing `kernel_rfl fun ty _ => do
    let ty ← instantiateMVars ty
    if ty.hasMVar || ty.hasFVar then
      throwError "kernel_rfl: the goal has metavariables or local hypotheses{indentExpr ty}"
    let some (α, a, _) := ty.eq? | throwError "kernel_rfl: not an equality{indentExpr ty}"
    let lvls := (← Term.getLevelNames).reverse.filter (collectLevelParams {} ty).params.contains
    let n ← withOptions (Elab.async.set · false) <|
      mkAuxLemma lvls ty (mkApp2 (mkConst ``Eq.refl [← getLevel α]) α a)
    return mkConst n (lvls.map .param)

end LeanVM.Guest.B1
