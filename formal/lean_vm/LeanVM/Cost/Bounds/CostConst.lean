module

public import LeanVM.Cost.Compiler
public import LeanVM.Cost.Bounds.Basic
public meta import LeanVM.Cost.Compiler
public meta import LeanVM.Cost.Bounds.Basic
public meta import Lean.Elab.Term
public meta import Lean.Elab.Tactic

/-!
# The compiled functions by their terms

The cost compiler outlines a large or recursive definition on demand, under a name numbered by
its index in the program (`LeanVM.Cost.Auto.<definition>.c<index>`); the index changes whenever
the chain compiled before it changes. `cost_const% f d` names the declaration `d` (`costEq`,
`costIdx`, `costDeps`, `costSpec`, `lam0.costEq`, …) of the function compiled for the term `f` (a
constant applied to its static arguments, the fixed contexts and instances), found by the term, as
the compiler itself finds it: so a proof about an on-demand function survives its renumbering.

`includes_sub` closes `Includes P l'` from an `Includes P l` of the context by a sublist proof
(`Includes.ofSublist`: the compiler sorts the bodies by index, so a callee's list is a sublist of
its caller's), one constructor per body of `l`, where `includes` builds a membership proof per
body of `l'` (quadratic: too slow on the decoder's lists of about a thousand bodies); it falls
back to `includes`.
-/

namespace LeanVM.Cost.Bounds.CostConst

open Lean Elab Term Meta LeanVM.Cost.Compiler

/-- `cost_const% f d`: the declaration `d` of the function the cost compiler compiled for `f`. -/
syntax (name := costConst) "cost_const% " term:max ident : term

/-- Elaborate `cost_const% f d`. -/
@[term_elab costConst] public meta def elabCostConst : TermElab := fun stx _ ↦ do
  let e ← instantiateMVars (← elabTerm stx[1] none)
  let .const h _ := e.getAppFn | throwError "cost_const%: {e} is not a constant application"
  let args := e.getAppArgs
  let some cands := (compiledExt.getState (← getEnv)).find? h
    | throwError "cost_const%: {h} is not compiled"
  for cf in cands do
    if cf.lam?.isNone && args.size == cf.static.size then
      let mut ok := true
      for i in [0:args.size] do
        unless ← isDefEq args[i]! cf.static[i]! do
          ok := false
          break
      if ok then
        let n := cf.body.getPrefix ++ stx[2].getId
        unless (← getEnv).contains n do throwError "cost_const%: no declaration {n}"
        return ← mkConstWithFreshMVarLevels n
  throwError "cost_const%: no compiled function for {e}"

/-- Close `Includes P l'` by a sublist proof from an `Includes P l` of the context. -/
meta def includesSublist (g : MVarId) : MetaM Bool := g.withContext do
  let gTy ← whnfR (← instantiateMVars (← g.getType))
  unless gTy.isAppOfArity ``Includes 2 do return false
  let l' ← LeanVM.Cost.Bounds.depsLiteral gTy.appArg!
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    let hTy ← whnfR (← instantiateMVars d.type)
    unless hTy.isAppOfArity ``Includes 2 do continue
    unless ← isDefEq hTy.appFn!.appArg! gTy.appFn!.appArg! do continue
    let l ← LeanVM.Cost.Bounds.depsLiteral hTy.appArg!
    let pairTy ← mkAppM ``Prod #[mkConst ``Nat, mkConst ``LeanVM.Cost.Term]
    try
      let hs ← sublistProof pairTy l' l
      g.assign (mkAppN (mkConst ``Includes.ofSublist)
        #[hTy.appFn!.appArg!, hTy.appArg!, gTy.appArg!, d.toExpr, hs])
      return true
    catch _ => pure ()
  return false

/-- `includes_sub`: `Includes P l'` from an `Includes P l` of the context, by a sublist proof,
else as `includes`. -/
elab "includes_sub" : tactic => do
  let g ← Tactic.getMainGoal
  unless ← includesSublist g do
    unless ← LeanVM.Cost.Bounds.includesAuto g do
      throwError "includes_sub: no hypothesis holds these bodies"
  Tactic.replaceMainGoal []

end LeanVM.Cost.Bounds.CostConst
