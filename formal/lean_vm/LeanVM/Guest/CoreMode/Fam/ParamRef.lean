/-
  LeanVM.Guest.CoreMode.Fam.ParamRef

  `param% f p`: the position of guest function `f`'s parameter named `p`, as a literal.
-/

module

public meta import Lean.Elab.Term

/-!
# Parameters by name

`guest-export` writes each guest function `f` to `Data/Source.lean` as `Data.fn_f`, its parameters
named. `param% f "p"` elaborates to the position of the parameter named `p`, every parameter up to it
a runtime scalar, so the position is that of `p`'s value among the core function's parameters
(`V.param`). A table keyed by parameter position reads by name, and a parameter added before `p`
reaches it by the export alone.
-/

public meta section

namespace LeanVM.Guest.CoreMode.Fam.ParamRef

open Lean Elab Term

/-- The elements of a list literal. -/
partial def listElems (e : Expr) : List Expr :=
  match e.getAppFnArgs with
  | (``List.cons, #[_, h, t]) => h :: listElems t
  | _ => []

/-- A string literal's value. -/
def strOf (e : Expr) : Option String :=
  match e with
  | .lit (.strVal s) => some s
  | _ => none

/-- A parameter literal's name, when it is a runtime scalar. -/
def scalarName (e : Expr) : Option String :=
  match e.getAppFnArgs with
  | (`LeanVM.Guest.Source.Param.mk, #[n, k]) =>
    match k.getAppFnArgs with
    | (`LeanVM.Guest.Source.ParamKind.runtime, #[s]) =>
      if s.isConstOf `LeanVM.Guest.Source.Shape.scalar then strOf n else none
    | _ => none
  | _ => none

/-- `param% f "p"`: the position of function `f`'s parameter `p`, every one up to it a runtime scalar. -/
elab:max "param% " f:ident p:str : term => do
  let n := `LeanVM.Guest.Data ++ Name.mkSimple ("fn_" ++ f.getId.toString)
  -- The source is imported privately: look it up outside the exported view, and insert only a literal.
  let some (.defnInfo d) := ((← getEnv).setExporting false).find? n
    | throwErrorAt f "no guest function {f.getId} ({n})"
  let some ps := d.value.getAppArgs[1]? | throwErrorAt f "{n} is not a function literal"
  let names := (listElems ps).map scalarName
  let rec go : List (Option String) → Nat → TermElabM Expr
    | [], _ => throwErrorAt p "{f.getId} has no runtime scalar parameter {p.getString} up front"
    | none :: _, _ => throwErrorAt p "{f.getId}'s parameters before {p.getString} are not all runtime scalars"
    | some s :: rest, i => if s = p.getString then return mkNatLit i else go rest (i + 1)
  go names 0

end LeanVM.Guest.CoreMode.Fam.ParamRef
