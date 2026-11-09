module

public import LeanVM.Cost.Bounds.Basic
public meta import Lean.Elab.Tactic

/-!
# Bounds on the guest decoder's prices: tactics

The guest decoder's compiled functions (`Cost/Decoder/`) take closures: the memory's reader `rd`,
a valuation `σ`, the frame map `Vn`, the cursor's length `cl`, the callees' witness functions.
Their prices are bounded in the prices of those closures' applications (`R`, `S`, `F`, …), each a
hypothesis `∀ a, appCost P v [encodeValue a] ≤ R`, beside the closure's spec
`∀ a, RunsApp P v [encodeValue a] (encodeValue (f a))` the price equations take.

* `cost_facts' [h₁, …]`: `cost_facts`, the hypotheses of each `hₖ` discharged first and its data
  read off them: a bound of a function of a closure `rd` names `rd` only in the closure's spec,
  which unification against the context's spec instantiates;
* `limbs_one`: `limbCount t = 1` for every `limbCount t` of the goal that `omega` shows
  word-sized.
-/

namespace LeanVM.Cost.Bounds.Guest

open LeanVM.Cost LeanVM.Cost.Bounds

public section

section Meta

open Lean Meta Elab Tactic

/-- `instantiateAt`, the hypotheses discharged before the data is checked: the data a hypothesis
names (a closure's Lean function) is read off it by the discharge's `assumption`. -/
meta def instantiateAtDeferred (pf s : Expr) : TacticM (Option Expr) := do
  let saved ← saveState
  let (xs, _, concl) ← forallMetaTelescopeReducing (← inferType pf)
  let concl ← whnfR concl
  let some lhs := (if concl.isAppOfArity ``LE.le 4 || concl.isAppOfArity ``LT.lt 4 then
      some concl.appFn!.appArg!
    else if concl.isAppOfArity ``Eq 3 then some concl.appFn!.appArg! else none)
    | return none
  unless ← isDefEq lhs s do
    saved.restore
    return none
  for x in xs do
    let x ← instantiateMVars x
    if x.isMVar then
      let g := x.mvarId!
      if (← isProp (← g.getType)) then
        unless ← discharge g do
          saved.restore
          return none
  for x in xs do
    let x ← instantiateMVars x
    if x.hasExprMVar then
      saved.restore
      return none
  return some (← instantiateMVars (mkAppN pf xs))

/-- `cost_facts' [h₁, …, hₙ]`: as `cost_facts`, the hypotheses of each `hₖ` discharged before its
data is checked (`instantiateAtDeferred`). -/
elab "cost_facts'" " [" hs:term,* "]" : tactic => withMainContext do
  let pfs ← hs.getElems.mapM fun h ↦ elabTerm h none
  let goal ← getMainGoal
  let prices := pricesIn (← instantiateMVars (← goal.getType))
  let mut g := goal
  for s in prices do
    for pf in pfs do
      let r ← g.withContext (instantiateAtDeferred pf s)
      if let some p := r then
        let (_, g') ← (← g.assert `hcost (← inferType p) p).intro1P
        g := g'
        break
  replaceMainGoal [g]

/-- The arguments of the `limbCount`s in `e` (no loose bound variables). -/
meta partial def limbArgs (e : Expr) (acc : Array Expr := #[]) : Array Expr :=
  let acc := if e.isAppOfArity ``limbCount 1 && !e.hasLooseBVars && !acc.contains e.appArg! then
    acc.push e.appArg! else acc
  match e with
  | .app f a => limbArgs a (limbArgs f acc)
  | .lam _ t b _ | .forallE _ t b _ => limbArgs b (limbArgs t acc)
  | .letE _ t v b _ => limbArgs b (limbArgs v (limbArgs t acc))
  | .mdata _ b | .proj _ _ b => limbArgs b acc
  | _ => acc

/-- `limbs_one`: for every `limbCount t` of the goal that `omega` shows word-sized, the hypothesis
`limbCount t = 1`, and the goal rewritten with them (products of limb counts folded). -/
elab "limbs_one" : tactic => withMainContext do
  let tgt ← instantiateMVars (← getMainTarget)
  let mut g ← getMainGoal
  let mut names : Array Ident := #[]
  let mut k := 0
  for t in limbArgs tgt do
    let ts ← Term.exprToSyntax t
    let ty ← elabTerm (← `($ts < 2 ^ 64)) (some (mkSort Level.zero))
    let m ← mkFreshExprMVar ty
    let ok ← try
        let gs ← Tactic.run m.mvarId! (evalTactic (← `(tactic| omega)))
        pure gs.isEmpty
      catch _ => pure false
    if ok then
      let n := Name.mkSimple s!"hlimbs_{k}"
      k := k + 1
      (_, g) ← g.note n (← mkAppM ``limbs_of_lt #[← instantiateMVars m])
      names := names.push (mkIdent n)
  replaceMainGoal [g]
  if !names.isEmpty then
    let mut ls : Array (TSyntax ``Lean.Parser.Tactic.simpLemma) := #[]
    for n in names do
      ls := ls.push (← `(Lean.Parser.Tactic.simpLemma| $n:ident))
    ls := ls.push (← `(Lean.Parser.Tactic.simpLemma| Nat.one_mul))
    ls := ls.push (← `(Lean.Parser.Tactic.simpLemma| Nat.mul_one))
    ls := ls.push (← `(Lean.Parser.Tactic.simpLemma| max_self))
    withMainContext do
      evalTactic (← `(tactic| simp (config := { failIfUnchanged := false }) only [$ls,*]))

end Meta

end

end LeanVM.Cost.Bounds.Guest
