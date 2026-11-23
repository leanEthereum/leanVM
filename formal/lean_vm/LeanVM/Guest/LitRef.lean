/-
  LeanVM.Guest.LitRef

  `lit% c`: the value of the definition `c`, a numeral expression, as one literal.
-/

module

public meta import Lean.Elab.Term

/-!
# A definition's literal

A size one function's proofs own and another's restate (`B1.expTabWords`, `exponent_tables`' table)
is defined once, and the restating sites write `lit% c`: it elaborates to the literal the definition
evaluates to, so a proof reads exactly as with a hand copy, and a change to the definition reaches
every site by itself.
-/

public meta section

namespace LeanVM.Guest.LitRef

open Lean Elab Term Meta

/-- `lit% c`: the natural number the definition `c` evaluates to, as a literal. -/
elab:max "lit% " c:ident : term => do
  let n ← realizeGlobalConstNoOverloadWithInfo c
  let some (.defnInfo d) := ((← getEnv).setExporting false).find? n
    | throwErrorAt c "lit%: {n} is not a definition"
  let some v ← (evalNat d.value).run
    | throwErrorAt c "lit%: {n} is not a numeral expression"
  return mkNatLit v

end LeanVM.Guest.LitRef
