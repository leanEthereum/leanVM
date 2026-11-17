/-
  LeanVM.Compiler.StateLit

  `state_lit`: a definition whose maps are written out as tries, each the one of an earlier
  definition with entries added, sharing what they do not change.
-/

module

public import LeanVM.Compiler.Cut
public meta import Lean.Elab.Command
public meta import Lean.Meta.Basic

/-!
# States written out

The kernel shares no evaluation between declarations. A walk's state at a cut written as the state
before it with entries added (`KMap.insertAll`) is evaluated, from the first state on, by every
check that reads it: the cost of a check grows with the state.

`state_lit x : T := e` adds `def x : T := v`, `v` the term `e` in which every `KMap.insertAll m l`,
`PMap.insertAll m l` and `NMap.insertAll m l` is replaced by the trie of `m` (the kernel's weak head
normal form of `m`: a map of an earlier `state_lit`, or an empty one) with the entries of `l` added
as `insert` adds them. The new trie is built here, on terms: a node off the keys added is the very
term of `m`'s trie, so the states of one module share it, in memory and in the `.olean`, and a
check comparing a walk's result with the next state compares only what the walk changed.

A state's trace from event `k`, `traceRest tf k`, is written in the trace's own parts (`restOf`): a
long trace is `(List.flatten [c₀, c₁, …]).toArray`, and its suffix from event `k` is
`List.append (cₘ.drop r) (List.flatten [cₘ₊₁, …])`, the parts the very terms of the trace's
definition. A check then reads no event before the cut, and the walk's own trace, reduced past the
events it reads, has the same tail term.

Keys: a value `⟨[], 0, i⟩` (every value of the guest's renumbered input) has the number `2 * i`
(`vKey`); a value of another shape is refused. Numerals of `ℕ` in the entries become literals.

Nothing here is trusted: `v` is only a definition, and a check that a walk reaches it is the
kernel's.
-/

public meta section

namespace LeanVM.Compiler.StateLit

open LeanVM.Guest Lean Elab Command

/-- `e` with its numerals of `ℕ` as literals. -/
def rawNats (e : Expr) : Expr :=
  e.replace fun x =>
    match_expr x with
    | OfNat.ofNat ty n _ =>
        if ty.isConstOf ``Nat then
          match n with
          | .lit (.natVal k) => some (mkRawNatLit k)
          | _ => none
        else none
    | _ => none

/-- The kernel's weak head normal form. -/
def whnfK (e : Expr) : MetaM Expr := do
  match Kernel.whnf (← getEnv) {} e with
  | .ok w => pure w
  | .error _ => throwError "state_lit: the kernel's weak head normal form failed"

/-- The elements of a list term: `[]`, `a :: l`, `List.flatten`, `++`, or a definition of one. -/
partial def listItems (e : Expr) (acc : Array Expr := #[]) : MetaM (Array Expr) := do
  match_expr e with
  | List.nil _ => return acc
  | List.cons _ a l => listItems l (acc.push a)
  | List.flatten _ ls => (← listItems ls).foldlM (fun acc l => listItems l acc) acc
  | HAppend.hAppend _ _ _ _ a b => listItems b (← listItems a acc)
  | List.append _ a b => listItems b (← listItems a acc)
  | _ =>
    match e.getAppFn with
    | .const c _ =>
      match (← getEnv).find? c with
      | some (.defnInfo d) => listItems (d.value.beta e.getAppArgs) acc
      | _ => throwError "state_lit: not a list: {e}"
    | _ => throwError "state_lit: not a list: {e}"

/-- A natural number literal. -/
def natOf (e : Expr) : MetaM Nat := do
  match (rawNats e) with
  | .lit (.natVal n) => pure n
  | _ => throwError "state_lit: not a numeral: {e}"

/-- The fields of `Prod.mk a b`. -/
def pairOf (e : Expr) : MetaM (Expr × Expr) := do
  match_expr e with
  | Prod.mk _ _ a b => pure (a, b)
  | _ => throwError "state_lit: not a pair: {e}"

/-- The key of a value `⟨[], 0, i⟩`: `2 * i` (`vKey`). -/
def vKeyOf (v : Expr) : MetaM Nat := do
  match_expr v with
  | LeanVM.Guest.Core.V.mk path tag idx =>
      let .true := (path.isAppOfArity ``List.nil 1) | throwError "state_lit: a value with a path: {v}"
      let 0 ← natOf tag | throwError "state_lit: a value with a tag: {v}"
      return 2 * (← natOf idx)
  | _ => throwError "state_lit: not a value: {v}"

/-- A trie term's root value, children. -/
def nodeOf (α t : Expr) : MetaM (Option Expr × Expr × Expr × Expr) := do
  let nil := mkApp (mkConst ``Trie.nil) α
  match_expr t with
  | Trie.nil _ => pure (none, mkApp (mkConst ``Option.none [0]) α, nil, nil)
  | Trie.node _ v l r =>
      match_expr v with
      | Option.some _ a => pure (some a, v, l, r)
      | Option.none _ => pure (none, v, l, r)
      | _ => throwError "state_lit: a trie's value is no option"
  | _ => throwError "state_lit: not a trie node"

/-- `t.set n (f (t.get n))` on trie terms, `Trie.setD`'s shape: the nodes off the path to `n` are
`t`'s own terms. -/
partial def setE (α t : Expr) (n : Nat) (f : Option Expr → MetaM Expr) : MetaM Expr := do
  let (old, v, l, r) ← nodeOf α t
  let node := mkApp4 (mkConst ``Trie.node) α
  if n == 0 then
    return node (mkApp2 (mkConst ``Option.some [0]) α (← f old)) l r
  else if n % 2 == 1 then
    return node v (← setE α l (n / 2) f) r
  else
    return node v l (← setE α r (n / 2 - 1) f)

/-- The trie of a map term `m` (`KMap.mk t`, `PMap.mk t`, `NMap.mk t`), in weak head normal form. -/
def trieOf (m : Expr) : MetaM Expr := do
  let w ← whnfK m
  let some t := w.getAppArgs.back? | throwError "state_lit: not a map: {m}"
  whnfK t

/-- `KMap.insertAll m l` on terms. -/
def kmapAll (κ α m l : Expr) : MetaM Expr := do
  let pairT := mkApp2 (mkConst ``Prod [0, 0]) κ α
  let bucketT := mkApp (mkConst ``List [0]) pairT
  let mut t ← trieOf m
  for x in ← listItems l do
    let x := rawNats x
    let (k, _) ← pairOf x
    let key ← vKeyOf k
    t ← setE bucketT t key fun old =>
      pure (mkApp3 (mkConst ``List.cons [0]) pairT x (old.getD (mkApp (mkConst ``List.nil [0]) pairT)))
  return mkApp3 (mkConst ``KMap.mk) κ α t

/-- `NMap.insertAll m l` on terms. -/
def nmapAll (α m l : Expr) : MetaM Expr := do
  let mut t ← trieOf m
  for x in ← listItems l do
    let (k, a) ← pairOf (rawNats x)
    t ← setE α t (← natOf k) fun _ => pure a
  return mkApp2 (mkConst ``NMap.mk) α t

/-- `PMap.insertAll m l` on terms. -/
def pmapAll (α m l : Expr) : MetaM Expr := do
  let inner := mkApp (mkConst ``Trie) α
  let mut t ← trieOf m
  for x in ← listItems l do
    let (k, a) ← pairOf (rawNats x)
    let (k1, k2) ← pairOf k
    let k2 ← natOf k2
    t ← setE inner t (← natOf k1) fun old => do
      let base ← match old with
        | some o => whnfK o
        | none => pure (mkApp (mkConst ``Trie.nil) α)
      setE α base k2 fun _ => pure a
  return mkApp2 (mkConst ``PMap.mk) α t

/-- `traceRest tf k` in the trace's own parts: a trace `(List.flatten [c₀, …]).toArray` from its
event `k` is `List.append (cₘ.drop r) (List.flatten [cₘ₊₁, …])`, its parts the very terms of the
trace's definition, so that the walk's trace, reduced, and this term share them. -/
def restOf (tf k : Expr) : MetaM Expr := do
  let k ← natOf k
  let w ← whnfK (mkApp (mkConst ``TracedFn.trace) tf)
  let some l := w.getAppArgs.back? | throwError "state_lit: a trace that is no array"
  let eventT := mkConst ``LeanVM.Compiler.Event
  match_expr l with
  | List.flatten _ parts =>
      -- the parts, each with the terms of the list of parts from it
      let mut tails : Array Expr := #[]
      let mut t := parts
      while t.isAppOfArity ``List.cons 3 do
        tails := tails.push t
        t := t.appArg!
      let mut k := k
      for tl in tails do
        let c := tl.appFn!.appArg!
        let n := (← listItems c).size
        if k < n then
          return mkApp3 (mkConst ``List.append [0]) eventT
            (mkApp3 (mkConst ``List.drop [0]) eventT (mkRawNatLit k) c)
            (mkApp2 (mkConst ``List.flatten [0]) eventT tl.appArg!)
        k := k - n
      return mkApp (mkConst ``List.nil [0]) eventT
  | _ => return mkApp3 (mkConst ``List.drop [0]) eventT (mkRawNatLit k) l

/-- `e` with its maps' `insertAll`s and its `traceRest` written out, through constructor
applications. -/
partial def expand (e : Expr) : MetaM Expr := do
  match_expr e with
  | traceRest tf k => restOf tf k
  | KMap.insertAll κ α _ _ m l => kmapAll κ α m l
  | PMap.insertAll α m l => pmapAll α m l
  | NMap.insertAll α m l => nmapAll α m l
  | _ =>
    if e.isApp then
      let args ← e.getAppArgs.mapM expand
      return mkAppN e.getAppFn args
    else return e

/-- `state_lit x : T := e` adds `def x : T := v`, `e` with its maps' `insertAll`s written out. -/
syntax (name := stateLit) (docComment)? "state_lit " ident " : " term " := " term : command

@[command_elab stateLit] def elabStateLit : CommandElab := fun stx => do
  let name := (← getCurrNamespace) ++ stx[2].getId
  let (ty, e) ← liftTermElabM do
    let ty ← Term.elabType stx[4]
    let e ← Term.elabTermEnsuringType stx[6] ty
    Term.synthesizeSyntheticMVarsNoPostponing
    let ty ← instantiateMVars ty
    let e ← instantiateMVars e
    if ty.hasMVar || e.hasMVar then throwError "state_lit: the term or its type is not known"
    pure (ty, e)
  let v ← liftTermElabM (expand e)
  liftCoreM <| addDecl (forceExpose := true)
    (.defnDecl (mkDefinitionValEx name [] ty v .abbrev .safe []))
  if let some doc := stx[0].getOptional? then
    liftTermElabM <| addDocString name (mkNullNode #[]) ⟨doc⟩

end LeanVM.Compiler.StateLit
