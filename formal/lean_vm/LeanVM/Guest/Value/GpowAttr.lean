/-
  LeanVM.Guest.Value.GpowAttr

  The simp set of pointer arithmetic in powers of `g`.
-/

module

public import Lean.Meta.Tactic.Simp.RegisterCommand

/-!
# `gpow_simps`

Declared apart from its lemmas (`LeanVM.Guest.Value.Gpow`) because a simp attribute takes effect
only in the modules that import its declaration.
-/

@[expose] public section

/-- Normalize pointer arithmetic to one power of `g` per pointer (`LeanVM.Guest.Value.Gpow`). -/
register_simp_attr gpow_simps
