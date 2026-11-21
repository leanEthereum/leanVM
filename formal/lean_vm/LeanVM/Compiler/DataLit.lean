/-
  LeanVM.Compiler.DataLit

  `data_lit`: a generated data definition, elaborated without info trees and not compiled.
-/

module

public meta import Lean.Elab.Command
public meta import Lean.Compiler.NoncomputableAttr

/-!
# Generated data

`data_lit x : T := e` adds `def x : T := e`, the value `e` as `def` elaborates it and the same
reducibility hints, through `addDecl`: the kernel checks it as it checks a `def`. Two things a
`def` does are skipped, both outside the kernel's check:

* the info trees of `e`'s elaboration (one node per subterm): they feed the editor and the module's
  reference index (`.ilean`), whose construction grows faster than the term on a long literal, and no
  tool reads the index of a generated data module;
* code generation: `x` is marked `noncomputable`, so a computable definition that reads it fails to
  compile instead of running it. The generated data is read by the kernel only (`decide +kernel`,
  `kernel_rfl`, the `state_lit` meta code).

Nothing here is trusted: `x` is only a definition, its value the elaborated `e`.
-/

public meta section

namespace LeanVM.Compiler.DataLit

open Lean Elab Command

/-- `data_lit x : T := e` adds `def x : T := e`, elaborated without info trees and not compiled
(`noncomputable`). -/
syntax (name := dataLit) (docComment)? "data_lit " ident " : " term " := " term : command

@[command_elab dataLit] def elabDataLit : CommandElab := fun stx => do
  let name := (← getCurrNamespace) ++ stx[2].getId
  let (ty, e) ← liftTermElabM <| withEnableInfoTree false do
    let ty ← Term.elabType stx[4]
    let e ← Term.elabTermEnsuringType stx[6] ty
    Term.synthesizeSyntheticMVarsNoPostponing
    let ty ← instantiateMVars ty
    let e ← instantiateMVars e
    if ty.hasMVar || e.hasMVar then throwError "data_lit: the term or its type is not known"
    pure (ty, e)
  let hints := ReducibilityHints.regular (getMaxHeight (← getEnv) e + 1)
  liftCoreM <| addDecl (forceExpose := true) (.defnDecl (mkDefinitionValEx name [] ty e hints .safe []))
  modifyEnv (addNoncomputable · name)
  if let some doc := stx[0].getOptional? then
    liftTermElabM <| addDocString name (mkNullNode #[]) ⟨doc⟩

end LeanVM.Compiler.DataLit
