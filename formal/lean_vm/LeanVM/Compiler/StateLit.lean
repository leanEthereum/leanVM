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
as `insert` adds them. The new trie is built here, on terms, and holds only what the entries change:
the nodes on the paths to the keys added. A node off those paths is written as a reference to the
node of the earlier definition it is: `Trie.left (Trie.right (KMap.t m))` and the like, `m` a
constant or a projection of one, which the kernel reduces by unfolding that constant and taking
children. So the kernel checks, and the `.olean` holds, each state's change only, and a check
comparing a walk's result with the next state reduces only the references on the paths it
changed. `state_lit full x : T := e` writes the tries out with no reference, for a state that many
checks read whole. The pools (`PMap`) are small and always written out.

A state's trace from event `k`, `traceRest tf k`, is written in the trace's own parts (`restOf`): a
long trace is `(List.flatten [c₀, c₁, …]).toArray`, and its suffix from event `k` is
`List.append (cₘ.drop r) (List.flatten [cₘ₊₁, …])`, the parts the very terms of the trace's
definition. A check then reads no event before the cut, and the walk's own trace, reduced past the
events it reads, has the same tail term.

Keys: a value `⟨[], 0, i⟩` (every value of a renumbered traced input) has the number `2 * i`
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

/-- Whether `t` is a trie written out at its root: `Trie.nil` or `Trie.node`, not a term that
reduces to one. -/
def isNode (t : Expr) : Bool :=
  t.isAppOfArity ``Trie.nil 1 || t.isAppOfArity ``Trie.node 4

/-- `t.set n (f (t.get n))` on trie terms, `Trie.setD`'s shape. `t` is a node, or a reference: a term
that reduces to a node of an earlier definition's trie, read here by the kernel's weak head normal
form. `addr`, if given, is a reference to `t`'s node. A node off the path to `n` is written as the
reference `Trie.left …`/`Trie.right …` to it when its parent's reference is known, else as its own
term. -/
partial def setR (α t : Expr) (addr : Option Expr) (n : Nat) (f : Option Expr → MetaM Expr) :
    MetaM Expr := do
  let (t, addr) ← if isNode t then pure (t, addr) else pure (← whnfK t, some t)
  let (old, v, l, r) ← nodeOf α t
  let node := mkApp4 (mkConst ``Trie.node) α
  -- a child's reference, if known: its own term if it is one, else through its parent's
  let refOf (c : Expr) (side : Name) : Option Expr :=
    if isNode c then addr.map (mkApp2 (mkConst side) α ·) else some c
  -- a child off the path, as the new node holds it
  let off (c : Expr) (side : Name) : Expr :=
    if c.isAppOfArity ``Trie.nil 1 then c else (refOf c side).getD c
  if n == 0 then
    return node (mkApp2 (mkConst ``Option.some [0]) α (← f old)) (off l ``Trie.left) (off r ``Trie.right)
  else if n % 2 == 1 then
    return node v (← setR α l (refOf l ``Trie.left) (n / 2) f) (off r ``Trie.right)
  else
    return node v (off l ``Trie.left) (← setR α r (refOf r ``Trie.right) (n / 2 - 1) f)

/-- `t` with every reference replaced by the node it reduces to, recursively: the trie written out. -/
partial def written (α t : Expr) : MetaM Expr := do
  let t ← if isNode t then pure t else whnfK t
  match_expr t with
  | Trie.node _ v l r => return mkApp4 (mkConst ``Trie.node) α v (← written α l) (← written α r)
  | _ => return t

/-- Whether a map term reduces by unfolding constants and projections only: a constant, or a
projection of one. -/
partial def isAddress (m : Expr) : MetaM Bool := do
  match m with
  | .const .. => return true
  | .proj _ _ e => isAddress e
  | .app .. =>
      let .const fn _ := m.getAppFn | return false
      if (← getEnv).getProjectionFnInfo? fn |>.isNone then return false
      let some e := m.getAppArgs.back? | return false
      isAddress e
  | _ => return false

/-- The trie of a map term `m` (`KMap.mk t`, `PMap.mk t`, `NMap.mk t`), in weak head normal form. -/
def trieOf (m : Expr) : MetaM Expr := do
  let w ← whnfK m
  let some t := w.getAppArgs.back? | throwError "state_lit: not a map: {m}"
  whnfK t

/-- `KMap.insertAll m l` on terms; a reference to `m`'s trie is `KMap.t m` if `m` is an address.
With `full`, the trie written out. -/
def kmapAll (full : Bool) (κ α m l : Expr) : MetaM Expr := do
  let pairT := mkApp2 (mkConst ``Prod [0, 0]) κ α
  let bucketT := mkApp (mkConst ``List [0]) pairT
  let mut t ← trieOf m
  let mut addr : Option Expr := if ← isAddress m then some (mkApp3 (mkConst ``KMap.t) κ α m) else none
  for x in ← listItems l do
    let x := rawNats x
    let (k, _) ← pairOf x
    let key ← vKeyOf k
    t ← setR bucketT t addr key fun old =>
      pure (mkApp3 (mkConst ``List.cons [0]) pairT x (old.getD (mkApp (mkConst ``List.nil [0]) pairT)))
    addr := none
  if let some a := addr then t := a
  if full then t ← written bucketT t
  return mkApp3 (mkConst ``KMap.mk) κ α t

/-- `NMap.insertAll m l` on terms, as `kmapAll`. -/
def nmapAll (full : Bool) (α m l : Expr) : MetaM Expr := do
  let mut t ← trieOf m
  let mut addr : Option Expr := if ← isAddress m then some (mkApp2 (mkConst ``NMap.t) α m) else none
  for x in ← listItems l do
    let (k, a) ← pairOf (rawNats x)
    t ← setR α t addr (← natOf k) fun _ => pure a
    addr := none
  if let some a := addr then t := a
  if full then t ← written α t
  return mkApp2 (mkConst ``NMap.mk) α t

/-- `PMap.insertAll m l` on terms, each trie written out (the pools are small). -/
def pmapAll (α m l : Expr) : MetaM Expr := do
  let inner := mkApp (mkConst ``Trie) α
  let mut t ← trieOf m
  for x in ← listItems l do
    let (k, a) ← pairOf (rawNats x)
    let (k1, k2) ← pairOf k
    let k2 ← natOf k2
    t ← setR inner t none (← natOf k1) fun old => do
      let base ← match old with
        | some o => whnfK o
        | none => pure (mkApp (mkConst ``Trie.nil) α)
      setR α base none k2 fun _ => pure a
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
partial def expand (full : Bool) (e : Expr) : MetaM Expr := do
  match_expr e with
  | traceRest tf k => restOf tf k
  | KMap.insertAll κ α _ _ m l => kmapAll full κ α m l
  | PMap.insertAll α m l => pmapAll α m l
  | NMap.insertAll α m l => nmapAll full α m l
  | _ =>
    if e.isApp then
      let args ← e.getAppArgs.mapM (expand full)
      return mkAppN e.getAppFn args
    else return e

/-- `state_lit x : T := e` adds `def x : T := v`, `e` with its maps' `insertAll`s written out, each
trie by reference to the earlier definition's where it does not change; `state_lit full x : T := e`
writes the tries out in full. -/
syntax (name := stateLit) (docComment)? "state_lit " (&"full")? ident " : " term " := " term : command

@[command_elab stateLit] def elabStateLit : CommandElab := fun stx => do
  let full := !stx[2].isNone
  let name := (← getCurrNamespace) ++ stx[3].getId
  let (ty, e) ← liftTermElabM do
    let ty ← Term.elabType stx[5]
    let e ← Term.elabTermEnsuringType stx[7] ty
    Term.synthesizeSyntheticMVarsNoPostponing
    let ty ← instantiateMVars ty
    let e ← instantiateMVars e
    if ty.hasMVar || e.hasMVar then throwError "state_lit: the term or its type is not known"
    pure (ty, e)
  let v ← liftTermElabM (expand full e)
  liftCoreM <| addDecl (forceExpose := true)
    (.defnDecl (mkDefinitionValEx name [] ty v .abbrev .safe []))
  if let some doc := stx[0].getOptional? then
    liftTermElabM <| addDocString name (mkNullNode #[]) ⟨doc⟩

end LeanVM.Compiler.StateLit
