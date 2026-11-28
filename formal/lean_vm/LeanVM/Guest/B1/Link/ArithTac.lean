/-
  LeanVM.Guest.B1.Link.ArithTac

  `kernel_eq`, the tactic: an equation closed by `Eq.refl`, its sides' definitional equality
  checked by the kernel only.
-/

module

public meta import Lean.Elab.Tactic.Basic

/-!
# `kernel_eq`, the tactic

`LeanVM.Guest.KernelRfl`'s `kernel_rfl` for an equation: `kernel_eq` closes `a = b` by
`Eq.refl a` without the elaborator's check, the kernel checking `a` and `b` definitionally equal
when the declaration is added (a failure fails the declaration). The link's arithmetic
(`LeanVM.Guest.B1.Link.Arith`) uses it where a generic definition, evaluated at the field and at
an expression evaluated at the field, unfolds over the concrete tables to one term.
-/

public meta section

namespace LeanVM.Guest

open Lean Elab Tactic Meta

/-- `kernel_eq`: close `a = b` by `Eq.refl a`, `a` and `b`'s definitional equality checked by the
kernel only. -/
elab "kernel_eq" : tactic => do
  let g ← getMainGoal
  let some (ty, a, _) := (← instantiateMVars (← g.getType)).eq? | throwError "kernel_eq: not an `=`"
  let u ← getLevel ty
  g.assign (mkApp2 (mkConst ``Eq.refl [u]) ty a)
  replaceMainGoal []

end LeanVM.Guest
