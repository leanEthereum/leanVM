/-
  LeanVM.Guest.KernelRfl

  `kernel_rfl`, the tactic: an `↔` closed by `Iff.rfl`, or a closed `=` by `rfl`, the two sides'
  definitional equality checked by the kernel only.
-/

module

public meta import Lean.Elab.Tactic.Basic
public meta import Lean.Meta.Tactic.AuxLemma

/-!
# `kernel_rfl`, the tactic

A condition `vc` computes for a long body is a deep term: comparing it with a recursive definition
of it by `exact Iff.rfl` exceeds the elaborator's recursion depth (`maxRecDepth`), though both
unfold to one term. The tactic `kernel_rfl` closes `a ↔ b` by `Iff.refl a` without the elaborator's
check: the kernel checks `a` and `b` definitionally equal when the declaration is added, and a
failure fails the declaration.

It closes `a = b`, with neither metavariables nor local hypotheses, by an auxiliary theorem
`Eq.refl a` that only the kernel checks, as `decide +kernel` adds its proof: a body equation passed
to a lemma, where `stmtsEqb_sound (by decide +kernel)` would evaluate a Boolean comparator on both
sides in full while the kernel compares the two terms structurally and unfolds each only as far as
the comparison needs. `KernelLit`'s command `kernel_rfl` is the same check for a stated equation.
-/

public meta section

namespace LeanVM.Guest

open Lean Elab Tactic Meta

/-- `kernel_rfl`: close `a ↔ b` by `Iff.rfl`, or a closed `a = b` by `rfl` as an auxiliary theorem,
`a` and `b`'s definitional equality checked by the kernel only. -/
elab "kernel_rfl" : tactic => do
  let g ← getMainGoal
  let ty ← instantiateMVars (← g.getType)
  if let some (a, _) := ty.iff? then
    g.assign (mkApp (mkConst ``Iff.refl) a)
    replaceMainGoal []
  else
    let some (α, a, _) := ty.eq? | throwError "kernel_rfl: neither an `↔` nor an `=`{indentExpr ty}"
    if ty.hasMVar || ty.hasFVar then
      throwError "kernel_rfl: the goal has metavariables or local hypotheses{indentExpr ty}"
    let lvls := (← Term.getLevelNames).reverse.filter (collectLevelParams {} ty).params.contains
    let n ← withOptions (Elab.async.set · false) <|
      mkAuxLemma lvls ty (mkApp2 (mkConst ``Eq.refl [← getLevel α]) α a)
    closeMainGoal `kernel_rfl (mkConst n (lvls.map .param))

end LeanVM.Guest
