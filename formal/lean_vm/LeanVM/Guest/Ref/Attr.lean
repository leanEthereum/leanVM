/-
  LeanVM.Guest.Ref.Attr

  The simp set that unfolds a reference function's relation into its commands' meanings.
-/

module

public import Lean.Meta.Tactic.Simp.RegisterCommand
public meta import Lean.Meta.Tactic.Simp.Attr

/-!
# `ref_norm`

`simp only [ref_norm, …]` unfolds `Cmd.SatList` of a reference function's body (`LeanVM.Guest.Ref.Lang`)
block by block, `unroll` included, into the meanings of its commands, the terms evaluated. The set is
filled in `LeanVM.Guest.Ref.Lang`; it is declared here because a simp attribute takes effect only in
the modules that import its declaration.
-/

@[expose] public section

/-- Unfold a reference function's commands into their meanings (`LeanVM.Guest.Ref.Lang`). -/
register_simp_attr ref_norm
