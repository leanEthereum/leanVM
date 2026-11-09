/-
  LeanVM.Guest.KernelLit

  `kernel_lit`: a value the kernel computes once, written into a definition, and the kernel's
  check that it is the value of the term it was computed from.
-/

module

public meta import Lean.Elab.Command
public meta import Lean.Meta.Basic

/-!
# Values computed once by the kernel

The kernel shares no evaluation between declarations: two `decide +kernel` checks that start from
the same costly term evaluate it twice. `kernel_lit x : T := e` evaluates `e` once and adds

* `def x : T := v`, `v` the kernel's normal form of `e`: constructors and literals only;
* `theorem x_eq : e = x`, by `rfl`,

and the kernel checks both, the theorem by evaluating `e` and comparing it with `v`. A check that
starts from `x` (rewritten by `x_eq`) reads `v` instead of evaluating `e`.

The normal form is found here, outside the kernel's checks, by the kernel's weak head normal form
(`Kernel.whnf`) on the fields of each constructor in turn, each subterm once. Nothing here is
trusted: a wrong `v` fails the kernel's check of `x_eq`.
-/

public meta section

namespace LeanVM.Guest.KernelLit

open Lean Elab Command

/-- Which fields of constructor `c` hold data, to be normalized: not proofs, not types. -/
def dataFields (c : ConstructorVal) : MetaM (Array Bool) :=
  Meta.forallTelescopeReducing c.type fun xs _ ↦ do
    let mut m := #[]
    for h : k in [c.numParams:xs.size] do
      m := m.push (!(← Meta.isProp (← Meta.inferType xs[k])) && !(← Meta.isType xs[k]))
    return m

/-- The state of `nf`: the normal forms found, and each constructor's data fields. -/
structure NfState where
  done : Std.HashMap Expr Expr := {}
  ctors : Std.HashMap Name (Array Bool) := {}

/-- The data fields of constructor `c`. -/
def fieldsOf (ci : ConstructorVal) : StateT NfState MetaM (Array Bool) := do
  match (← get).ctors.get? ci.name with
  | some m => return m
  | none =>
    let m ← dataFields ci
    modify fun s ↦ { s with ctors := s.ctors.insert ci.name m }
    return m

/-- The kernel's normal form of `e`: a literal, or a constructor applied to its parameters and
fields, its data fields in normal form. A constructor application is kept and its fields
normalized; anything else is first put in weak head normal form by the kernel. -/
partial def nf (e : Expr) : StateT NfState MetaM Expr := do
  if let some r := (← get).done.get? e then return r
  let env ← getEnv
  let ctorOf (w : Expr) : Option ConstructorVal := match w.getAppFn with
    | .const c _ => match env.find? c with
      | some (.ctorInfo ci) => if w.getAppNumArgs == ci.numParams + ci.numFields then some ci else none
      | _ => none
    | _ => none
  -- the subterms already normalized are replaced by their normal forms first, so that a term
  -- naming another (`index segs`, `segs` normalized) reads its normal form, not evaluating it again
  let w ← if e.isLit || (ctorOf e).isSome then pure e
    else
      let done := (← get).done
      match Kernel.whnf env {} (e.replace fun x ↦ done.get? x) with
      | .ok w => pure w
      | .error _ => throwError "kernel_lit: the kernel's weak head normal form failed"
  let r ← if w.isLit then pure w
    else match ctorOf w with
      | some ci =>
        let mask ← fieldsOf ci
        let args := w.getAppArgs
        let mut out := #[]
        for h : k in [0:args.size] do
          out := out.push (← if k < ci.numParams || !(mask[k - ci.numParams]?.getD false) then
            pure args[k] else nf args[k])
        pure (mkAppN w.getAppFn out)
      | none => throwError "kernel_lit: no constructor at the head of a weak head normal form"
  modify fun s ↦ { s with done := s.done.insert e r }
  return r

/-- `kernel_lit x : T := e` adds `def x : T := v`, `v` the kernel's normal form of `e` (constructors
and literals), and `theorem x_eq : e = x`, by `rfl`; the kernel checks both. -/
syntax (name := kernelLit) (docComment)? "kernel_lit " ident " : " term " := " term : command

@[command_elab kernelLit] def elabKernelLit : CommandElab := fun stx => do
  let name := (← getCurrNamespace) ++ stx[2].getId
  let (ty, e, u, v) ← liftTermElabM do
    let ty ← Term.elabType stx[4]
    let e ← Term.elabTermEnsuringType stx[6] ty
    Term.synthesizeSyntheticMVarsNoPostponing
    let ty ← instantiateMVars ty
    let e ← instantiateMVars e
    if ty.hasMVar || e.hasMVar then throwError "kernel_lit: the term or its type is not known"
    let u ← Meta.getLevel ty
    let v ← (nf e).run' {}
    pure (ty, e, u, v)
  -- the value is exported: checks in other modules read it
  liftCoreM <| addDecl (forceExpose := true)
    (.defnDecl (mkDefinitionValEx name [] ty v .abbrev .safe []))
  if let some doc := stx[0].getOptional? then
    liftTermElabM <| addDocString name (mkNullNode #[]) ⟨doc⟩
  let c := mkConst name
  liftCoreM <| addDecl
    (.thmDecl (mkTheoremValEx (name.appendAfter "_eq") [] (mkApp3 (mkConst ``Eq [u]) ty e c)
      (mkApp2 (mkConst ``Eq.refl [u]) ty c) []))

end LeanVM.Guest.KernelLit
