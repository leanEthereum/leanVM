import Lean
import LeanVM.Prover.Fast.Arith
import LeanVM.Prover.Fast.Sponge

/-!
# Copies of definitions, compiled with `E`'s word-level arithmetic

A `@[csimp]` lemma acts where code is compiled. The statement's prover (`Statement/Prover/`) and
the verifier's functions it calls (`Statement/LeanVmVerifier.lean`) were compiled with `E`'s
generic product, and their compiled functions call one another, so a lemma here would change
nothing in them. This module recompiles them. For a definition `f`, `f.fast` is the definition
whose value is `f`'s with every product `x * y` and power `x ^ n` in `E` replaced by `mulE x y` and
`powE x n` (`Arith.lean`: they compile on machine words), with `f`'s compiler attributes, and
`f.fast_eq : @f = @f.fast` is proved by `rfl` (`mulE x y` is `x * y` by definition) and marked
`@[csimp]`. Copied callee-first, each copy is compiled with the lemmas of the copies of the
functions it calls, so it calls them; code compiled where the lemmas are visible calls the copies.
The copies' code is the compiler's, from their values: nothing is trusted beyond the compiler.

A recursive definition is not compiled from its value (a recursor): it is copied by hand, its text
with `mulE` for `E`'s product, proved equal by induction and marked `@[csimp]` (`Prover.lean`).
`fast_copy_modules p₁ p₂ …` copies, callee-first, every definition of the modules whose name
starts with one of the prefixes that multiplies in `E` or calls a definition that has or needs a
copy, except a definition that already compiles as another (a `@[csimp]` lemma of
`Statement/Fast/`); its callers wait for a recursive one's hand-written copy, so the copies are
written in rounds. `fast_copy_modules_final` copies them anyway, calling the definition itself;
`fast_copy_modules_complete` fails instead, if one is left.
-/

namespace LeanVM.Prover.Fast

open Lean Meta Elab Command

/-- `E`, the type whose products are replaced. -/
def eType : Expr := mkConst ``LeanVM.Parameters.E

/-- Whether a type is `E`, up to reducible unfolding. -/
def isE (t : Expr) : MetaM Bool := withReducible (isDefEq t eType)

/-- The value with every product and power in `E` replaced by `mulE` and `powE`. -/
def rewriteArith (e : Expr) : MetaM Expr :=
  Meta.transform e (post := fun t ↦ do
    match t.getAppFnArgs with
    | (``HMul.hMul, #[α, β, γ, _, a, b]) =>
      if (← isE α) && (← isE β) && (← isE γ) then
        return .done (mkApp2 (mkConst ``mulE) a b)
      return .continue
    | (``HPow.hPow, #[α, β, γ, _, a, n]) =>
      if (← isE α) && (← withReducible (isDefEq β (mkConst ``Nat))) && (← isE γ) then
        return .done (mkApp2 (mkConst ``powE) a n)
      return .continue
    | _ => return .continue)

/-- Whether a value is a recursor's application (a recursive definition), which the compiler
does not compile. -/
def isRecursiveValue (v : Expr) : Bool :=
  v.getUsedConstants.any fun c ↦
    c == ``WellFounded.fix || c.getString! == "brecOn" || c.getString! == "binductionOn"

/-- The copy's name. -/
def fastName (c : Name) : Name := c.str "fast"

/-- Copy `c` as `c.fast`, its value rewritten, with the `@[csimp]` lemma `c.fast_eq`; `false` if
it is not copied (not a definition, recursive, or unchanged unless `force`). -/
def copyDecl (c : Name) (force : Bool) : MetaM Bool := do
  let .defnInfo info ← getConstInfo c | return false
  if isRecursiveValue info.value then return false
  let v ← rewriteArith info.value
  if v == info.value && !force then return false
  let n := fastName c
  addDecl <| .defnDecl
    { name := n, levelParams := info.levelParams, type := info.type, value := v,
      hints := info.hints, safety := .safe }
  -- The original's compiler attributes (`@[macro_inline]`, `@[inline]`, `@[specialize]`): a
  -- `Word` built by a `@[macro_inline]` definition is a closure over values computed once.
  let env ← getEnv
  if let some kind := Compiler.getInlineAttribute? env c then
    match Compiler.setInlineAttribute env n kind with
    | .ok env => setEnv env
    | .error e => throwError e
  if let some args := Compiler.getSpecializationArgs? env c then
    match Compiler.specializeAttr.setParam (← getEnv) n args with
    | .ok env => setEnv env
    | .error e => throwError e
  compileDecls #[n]
  let lvls := info.levelParams.map Level.param
  let eqName := c.str "fast_eq"
  addDecl <| .thmDecl
    { name := eqName, levelParams := info.levelParams,
      type := ← mkEq (mkConst c lvls) (mkConst n lvls),
      value := ← mkEqRefl (mkConst c lvls) }
  Compiler.CSimp.add eqName .global
  return true

/-- Whether a constant is a definition the copy may replace: not internal, not a matcher, not
already replaced by a `@[csimp]` lemma. -/
def copyable (env : Environment) (c : Name) : Bool :=
  !c.isInternal && !isMatcherCore env c &&
    -- One that already compiles as another (`@[csimp]`, `Statement/Fast/`) keeps that.
    !(Compiler.CSimp.ext.getState env).map.contains c &&
    match env.find? c with
    | some (.defnInfo _) => true
    | _ => false

/-- The constants a definition's code refers to and whether it multiplies in `E`: its value's, or,
for a recursive definition, its unfolding equation's. -/
def codeOf (c : Name) : MetaM (Option (Array Name × Bool)) := do
  let .defnInfo i ← getConstInfo c | return none
  let body ← if isRecursiveValue i.value then
      match ← getUnfoldEqnFor? c (nonRec := true) with
      | some eq => pure (← getConstInfo eq).type
      | none => pure i.value
    else pure i.value
  let mul ← forallTelescope body fun _ b ↦ do return (← rewriteArith b) != b
  return some (body.getUsedConstants, mul)

/-- The candidate definitions of the modules whose name starts with one of the prefixes,
callee-first. -/
def modulesDecls (ps : Array Name) : MetaM (Array Name) := do
  let env ← getEnv
  let mods := env.header.moduleNames
  let mut cands : NameSet := {}
  for (c, _) in env.constants.map₁.toList do
    if let some idx := env.getModuleIdxFor? c then
      if ps.any (·.isPrefixOf mods[idx.toNat]!) && copyable env c then cands := cands.insert c
  -- Callee-first: a depth-first walk over the references among the candidates.
  let mut order : Array Name := #[]
  let mut seen : NameSet := {}
  for c in cands.toList.toArray.qsort Name.lt do
    let mut stack : List (Name × Bool) := [(c, false)]
    while !stack.isEmpty do
      match stack with
      | [] => pure ()
      | (x, done) :: rest =>
        stack := rest
        if done then order := order.push x
        else if !seen.contains x then
          seen := seen.insert x
          stack := (x, true) :: stack
          if let some (refs, _) ← codeOf x then
            for d in refs do
              if cands.contains d && !seen.contains d then stack := (d, false) :: stack
  return order

/-- What `copyModules` does with the callers of a recursive definition that needs a hand-written
copy and has none: wait for it, copy them anyway, or fail. -/
inductive Mode where
  | wait
  | final
  | complete

/-- Copy, callee-first, the definitions of the modules whose name starts with one of the prefixes
that multiply in `E` or call a definition that has or needs a copy (`fast_copy_modules`). -/
def copyModules (ps : Array Name) (mode : Mode) : TermElabM Unit := do
  let order ← modulesDecls ps
  let cands : NameSet := order.foldl (·.insert ·) {}
  -- `needs`: multiplies in `E` or calls a definition that has or needs a copy; `done`: has one.
  let mut needs : NameSet := {}
  let mut done : NameSet := {}
  let mut waiting : Array Name := #[]
  for c in order do
    if (← getEnv).contains (fastName c) then
      needs := needs.insert c; done := done.insert c; continue
    let some (refs, mul) ← codeOf c | continue
    let deps := refs.filter fun d ↦ cands.contains d && d != c
    let env ← getEnv
    unless mul || deps.any needs.contains || refs.any (env.contains <| fastName ·) do continue
    needs := needs.insert c
    if mode matches .wait then
      if deps.any fun d ↦ needs.contains d && !done.contains d then continue
    let .defnInfo i ← getConstInfo c | continue
    if isRecursiveValue i.value then
      waiting := waiting.push c; continue
    if ← copyDecl c true then done := done.insert c
  if mode matches .complete then
    unless waiting.isEmpty do
      throwError "recursive definitions without a hand-written copy: {waiting}"

/-- Copy the definitions of the modules whose name starts with one of the prefixes that need a
copy; the callers of a recursive one without a hand-written copy wait. -/
elab "fast_copy_modules " ps:ident+ : command => liftTermElabM do
  copyModules (ps.map (·.getId)) .wait

/-- `fast_copy_modules`, the callers of a recursive definition without a hand-written copy copied
too: they call the definition itself. -/
elab "fast_copy_modules_final " ps:ident+ : command => liftTermElabM do
  copyModules (ps.map (·.getId)) .final

/-- `fast_copy_modules`, failing if a recursive definition that needs a copy has none. -/
elab "fast_copy_modules_complete " ps:ident+ : command => liftTermElabM do
  copyModules (ps.map (·.getId)) .complete

end LeanVM.Prover.Fast
