/-
  LeanVM.Guest.DataLit

  `data% t`: a data literal built as a term without elaborating each of its nodes.
-/

module

public meta import Lean.Elab.SyntheticMVars

/-!
# Data literals as terms

The generated data of the guest's certificates (a pack's copy of a function's code,
`Pack/*/Bundle.lean`; its core IR, `Pack/*/Core*.lean`) is hundreds of thousands of constructor
applications of numerals, strings and lists. The elaborator elaborates every application, numeral
and list against its expected type, synthesizes each numeral's instance and unifies the results.
`data% t` reads the same text and builds the term directly from the expected type: an application
`.c a₁ … aₙ` (or `c a₁ … aₙ`, `⟨a₁, …, aₙ⟩`) of a constant whose binders after the type's
parameters are the `n` explicit arguments, each built at its binder's type; a numeral at `ℕ` as the
elaborator writes it (`OfNat.ofNat ℕ n (instOfNatNat n)`); a string; a list `[a, …]` or `a :: l`; a
tuple `(a, b, …)`.
Anything else is elaborated as usual. Nothing here is trusted: the kernel checks the definition's
value against its type, and the certificates check the values against the statement's data
(`Checked/Link*`).
-/

namespace LeanVM.Guest.DataLit

open Lean Elab Term Meta

public meta section

/-- `data% t`: the data literal `t`, built at the expected type. -/
syntax (name := dataLit) "data% " term : term

/-- `t` elaborated as usual at type `ty`. -/
def elabUsual (stx : Syntax) (ty : Expr) : TermElabM Expr := do
  let e ← elabTermEnsuringType stx ty
  synthesizeSyntheticMVarsNoPostponing
  instantiateMVars e

/-- The elements of a chain `a :: b :: … :: l`, and its last term `l`. -/
partial def consChain (stx : Syntax) (acc : Array Syntax := #[]) : Array Syntax × Syntax :=
  if stx.getKind == `«term_::_» then consChain stx[2] (acc.push stx[0]) else (acc, stx)

mutual

/-- `stx` built at type `ty`, or elaborated as usual where it is not a data literal. -/
partial def build (stx : Syntax) (ty : Expr) : TermElabM Expr := do
  match ← tryBuild stx ty with
  | some e => return e
  | none => elabUsual stx ty

/-- `stx` built at type `ty`, if it is a data literal of a form `build` knows. -/
partial def tryBuild (stx : Syntax) (ty : Expr) : TermElabM (Option Expr) := do
  let k := stx.getKind
  if k == ``Lean.Parser.Term.paren then
    return some (← build stx[1] ty)
  if let some n := stx.isNatLit? then
    return if (← whnfR ty).isConstOf ``Nat then some (mkNatLit n) else none
  if let some s := stx.isStrLit? then
    return if (← whnfR ty).isConstOf ``String then some (mkStrLit s) else none
  if k == `«term[_]» then
    return ← listOf (stx[1].getSepArgs.map Sum.inl) (← whnfR ty)
  if k == `«term_::_» then
    let (xs, tl) := consChain stx
    return ← listOf (xs.map Sum.inl |>.push (Sum.inr tl)) (← whnfR ty)
  if k == ``Lean.Parser.Term.tuple then
    if stx[1].getNumArgs == 0 then return none
    return ← tupleOf (#[stx[1][0]] ++ stx[1][2].getSepArgs) (← whnfR ty)
  if k == ``Lean.Parser.Term.anonymousCtor then
    let ty ← whnfR ty
    let .const I _ := ty.getAppFn | return none
    let some (.inductInfo v) := (← getEnv).find? I | return none
    let [c] := v.ctors | return none
    return ← appConst c stx[1].getSepArgs ty
  let (f, args) := if k == ``Lean.Parser.Term.app then (stx[0], stx[1].getArgs) else (stx, #[])
  if args.any fun a ↦ a.getKind matches ``Lean.Parser.Term.namedArgument | ``Lean.Parser.Term.ellipsis then
    return none
  if f.getKind == ``Lean.Parser.Term.dotIdent then
    let ty ← whnfR ty
    let .const I _ := ty.getAppFn | return none
    return ← appConst (I ++ f[1].getId.eraseMacroScopes) args ty
  if f.isIdent then
    let some c ← (try some <$> realizeGlobalConstNoOverload f catch _ => pure none) | return none
    return ← appConst c args ty
  return none

/-- The list of the elements `xs` (each a term, or the list it ends in) at type `ty`. -/
partial def listOf (xs : Array (Sum Syntax Syntax)) (ty : Expr) : TermElabM (Option Expr) := do
  unless ty.isAppOfArity ``List 1 do return none
  let .const _ us := ty.getAppFn | return none
  let α := ty.appArg!
  let mut l := mkApp (.const ``List.nil us) α
  let mut rest := xs
  if let some (.inr tl) := xs.back? then
    l ← build tl ty
    rest := xs.pop
  for x in rest.reverse do
    let .inl a := x | return none
    l := mkApp3 (.const ``List.cons us) α (← build a α) l
  return some l

/-- The tuple `(x₀, x₁, …)` at type `ty`, a product `α × β` with `(x₁, …)` at `β`. -/
partial def tupleOf (xs : Array Syntax) (ty : Expr) : TermElabM (Option Expr) := do
  let some x := xs[0]? | return none
  if xs.size == 1 then return some (← build x ty)
  unless ty.isAppOfArity ``Prod 2 do return none
  let .const _ us := ty.getAppFn | return none
  let some r ← tupleOf (xs.extract 1 xs.size) (← whnfR ty.appArg!) | return none
  return some (mkApp4 (.const ``Prod.mk us) ty.appFn!.appArg! ty.appArg! (← build x ty.appFn!.appArg!) r)

/-- Constant `c` applied to `args` at type `ty`: a constructor of `ty`'s inductive type after its
parameters, or a constant without universe parameters; each argument at its binder's type, the
binders after the parameters exactly the arguments, all explicit. -/
partial def appConst (c : Name) (args : Array Syntax) (ty : Expr) : TermElabM (Option Expr) := do
  let some ci := (← getEnv).find? c | return none
  let some (f, fty) ← (match ci with
    | .ctorInfo v => do
      let ty ← whnfR ty
      let .const I us := ty.getAppFn | return none
      unless I == v.induct && ty.getAppNumArgs == v.numParams do return none
      let ps := ty.getAppArgs
      return some (mkAppN (.const c us) ps, ← instantiateForall (ci.instantiateTypeLevelParams us) ps)
    | _ => return if ci.levelParams.isEmpty then some (.const c [], ci.type) else none
    : TermElabM (Option (Expr × Expr))) | return none
  let mut e := f
  let mut t := fty
  for a in args do
    let t' ← if t.isForall then pure t else whnf t
    let .forallE _ d b bi := t' | return none
    unless bi.isExplicit do return none
    let x ← build a d
    e := mkApp e x
    t := b.instantiate1 x
  if (← if t.isForall then pure t else whnf t).isForall then return none
  return some e

end

@[term_elab dataLit] def elabDataLit : TermElab := fun stx ty? => do
  tryPostponeIfNoneOrMVar ty?
  let some ty := ty? | throwError "data%: the expected type is not known"
  build stx[1] (← instantiateMVars ty)

end

end LeanVM.Guest.DataLit
