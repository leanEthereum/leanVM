module

public import LeanVM.Cost.AS.Bounds.Newton
public meta import Lean.Elab.Tactic

/-!
# Bounds: the skeletons' shared vocabulary

* `packedSum`: the scalars a skeleton's packed reads and draws carry, which its replay pays per
  scalar (`skelReplay_cost`);
* `LayOk`: an admissible lite layout, the sizes every skeleton price assumes;
* a tactic, `cost_calls [L₁, …]` / `len_facts [L₁, …]`, adding the bounds of a goal's list
  primitives and of named callees, and the lengths the lemmas bound.
-/

namespace LeanVM.Cost.Bounds.AS

open LeanVM.Cost LeanVM.Cost.Bounds LeanVM.Cost.AS LeanVM.Cost.Library LeanVM.Parameters
open LeanVM.Protocol.EndToEnd.Sound

public section

/-- The scalars a skeleton's packed reads and draws carry. -/
@[expose] def packedSum : List Op → ℕ
  | [] => 0
  | .readPacked n :: sk => n + packedSum sk
  | .samplePacked n :: sk => n + packedSum sk
  | _ :: sk => packedSum sk

@[simp] theorem packedSum_nil : packedSum [] = 0 := rfl

theorem packedSum_append : ∀ a b : List Op, packedSum (a ++ b) = packedSum a + packedSum b
  | [], b => by simp
  | op :: a, b => by
    cases op <;> simp only [List.cons_append, packedSum, packedSum_append a b] <;> omega

/-- An admissible lite layout: a stack of at most `2^30`, memory and bytecode of log-size at most
`30`, six tables of log-heights at most `30` and of at most `2^30` rows. -/
@[expose] def LayOk (lay : LayoutLite) : Prop :=
  lay.stackLog ≤ 30 ∧ lay.logMemory ≤ 30 ∧ lay.logBytecode ≤ 30 ∧
    lay.tableLogHeights.length ≤ 6 ∧ (∀ h ∈ lay.tableLogHeights, h ≤ 30) ∧
    lay.tableRows.length ≤ 6 ∧ ∀ r ∈ lay.tableRows, r ≤ 2 ^ 30

/-! ## A tactic for the skeletons' prices -/

section Meta

open Lean Meta Elab Tactic

/-- The values of a literal list of encoded values `[encodeValue a, …]`. -/
meta partial def encArgsOf (e : Expr) : Option (List Expr) :=
  if e.isAppOfArity ``List.nil 1 then some []
  else if e.isAppOfArity ``List.cons 3 then
    let h := e.appFn!.appArg!
    if h.isAppOfArity ``LeanVM.Cost.MachineEncoding.encodeValue 3 then
      (encArgsOf e.appArg!).map (h.appArg! :: ·)
    else none
  else none

/-- The program and the values of every `machineCost P c [encodeValue a, …]` of `e`. -/
meta partial def callsOf (c : Name) (e : Expr) (acc : Array (Expr × List Expr) := #[]) :
    Array (Expr × List Expr) :=
  let acc :=
    if e.isAppOfArity ``LeanVM.Cost.machineCost 3 && !e.hasLooseBVars then
      let args := e.getAppArgs
      if args[1]!.isConstOf c then
        match encArgsOf args[2]! with
        | some xs => if acc.any (fun p ↦ p.2 == xs) then acc else acc.push (args[0]!, xs)
        | none => acc
      else acc
    else acc
  match e with
  | .app f a => callsOf c a (callsOf c f acc)
  | .lam _ t b _ | .forallE _ t b _ => callsOf c b (callsOf c t acc)
  | .letE _ t v b _ => callsOf c b (callsOf c v (callsOf c t acc))
  | .mdata _ b | .proj _ _ b => callsOf c b acc
  | _ => acc

/-- Add the hypothesis `stx` proves, if it elaborates. -/
meta def noteTerm (stx : Syntax) : TacticM Unit := do
  let g ← getMainGoal
  try
    let g' ← g.withContext do
      let pf ← Term.withoutErrToSorry <| Term.withSynthesize <| Term.elabTerm stx none
      let pf ← instantiateMVars pf
      if pf.hasExprMVar || pf.hasSyntheticSorry then return g
      let (_, g') ← g.note `hcost pf
      return g'
    replaceMainGoal [g']
  catch _ => replaceMainGoal [g]

/-- The `machineCost` index of a lemma's conclusion. -/
meta def lemmaIdx (n : Name) : MetaM (Option Name) := do
  let ci ← getConstInfo n
  forallTelescopeReducing ci.type fun _ body ↦ do
    match body.find? (fun x ↦ x.isAppOfArity ``LeanVM.Cost.machineCost 3) with
    | some m => return (m.getArg! 1).constName?
    | none => return none

/-- The function whose length a lemma bounds. -/
meta def lemmaLenFn (n : Name) : MetaM (Option Name) := do
  let ci ← getConstInfo n
  forallTelescopeReducing ci.type fun _ body ↦ do
    match body.find? (fun x ↦ x.isAppOfArity ``List.length 2) with
    | some m => return m.appArg!.getAppFn.constName?
    | none => return none

/-- The arguments of every `List.length (f a₁ … aₙ)` of `e`. -/
meta partial def lenArgsOf (f : Name) (e : Expr) (acc : Array (Array Expr) := #[]) :
    Array (Array Expr) :=
  let acc :=
    if e.isAppOfArity ``List.length 2 && !e.hasLooseBVars && e.appArg!.isAppOf f then
      let args := e.appArg!.getAppArgs
      if acc.any (· == args) then acc else acc.push args
    else acc
  match e with
  | .app fn a => lenArgsOf f a (lenArgsOf f fn acc)
  | .lam _ t b _ | .forallE _ t b _ => lenArgsOf f b (lenArgsOf f t acc)
  | .letE _ t v b _ => lenArgsOf f b (lenArgsOf f v (lenArgsOf f t acc))
  | .mdata _ b | .proj _ _ b => lenArgsOf f b acc
  | _ => acc

/-- `cost_calls [L₁, …]`: for every append, replicate and word-sized `limbCount` of the goal, its
bound as a hypothesis (`append_cost`, `replicate_cost`, `take_cost`, `drop_cost`, `length_cost`,
`limbs_of_lt`); for every call of a
lemma `Lᵢ`'s index on encoded values, `Lᵢ P (by includes) a₁ …` (side conditions by their
`autoParam`s). -/
elab "cost_calls" " [" ls:ident,* "]" : tactic => do
  let tgt ← withMainContext do instantiateMVars (← getMainTarget)
  for (p, xs) in callsOf ``LeanVM.Cost.Auto.List.append.c50.costIdx tgt do
    if let [a, b] := xs then
      noteTerm (← `(append_cost $(← Term.exprToSyntax p) (by includes) $(← Term.exprToSyntax a)
        $(← Term.exprToSyntax b)))
  for (p, xs) in callsOf ``LeanVM.Cost.Auto.List.replicate.c76.costIdx tgt do
    if let [n, a] := xs then
      noteTerm (← `(replicate_cost $(← Term.exprToSyntax p) (by includes) $(← Term.exprToSyntax a)
        $(← Term.exprToSyntax n) (by omega)))
  for (p, xs) in callsOf ``LeanVM.Cost.Auto.List.take.c68.costIdx tgt do
    if let [n, a] := xs then
      noteTerm (← `(take_cost $(← Term.exprToSyntax p) (by includes) $(← Term.exprToSyntax n)
        $(← Term.exprToSyntax a) (by omega)))
  for (p, xs) in callsOf ``LeanVM.Cost.Auto.List.drop.c42.costIdx tgt do
    if let [n, a] := xs then
      noteTerm (← `(drop_cost $(← Term.exprToSyntax p) (by includes) $(← Term.exprToSyntax n)
        $(← Term.exprToSyntax a) (by omega)))
  for (p, xs) in callsOf ``LeanVM.Cost.Auto.List.length.c21.costIdx tgt do
    if let [a] := xs then
      noteTerm (← `(length_cost $(← Term.exprToSyntax p) (by includes) $(← Term.exprToSyntax a)
        (by omega)))
  for t in limbsArgs tgt do
    noteTerm (← `(limbs_of_lt (by omega : $(← Term.exprToSyntax t) < 2 ^ 64)))
  for l in ls.getElems do
    let n ← realizeGlobalConstNoOverloadWithInfo l
    let some c ← lemmaIdx n | throwError "cost_calls: {n} prices no call"
    for (p, xs) in callsOf c tgt do
      let args ← xs.toArray.mapM fun x ↦ Term.exprToSyntax x
      noteTerm (← `($(mkIdent n) $(← Term.exprToSyntax p) (by includes) $args*))

/-- `len_facts [L₁, …]`: for every `List.length (f a₁ …)` of the goal and the hypotheses, `f` the
function a lemma `Lᵢ` bounds the length of, `Lᵢ a₁ …` as a hypothesis. -/
elab "len_facts" " [" ls:ident,* "]" : tactic => do
  evalTactic (← `(tactic| try simp only [List.length_append, List.length_replicate, List.length_cons,
    List.length_nil, List.length_singleton] at *))
  let es ← withMainContext do
    let mut es := #[← instantiateMVars (← getMainTarget)]
    for d in ← getLCtx do
      unless d.isImplementationDetail do es := es.push (← instantiateMVars d.type)
    return es
  for l in ls.getElems do
    let n ← realizeGlobalConstNoOverloadWithInfo l
    let some f ← lemmaLenFn n | throwError "len_facts: {n} bounds no length"
    let mut seen : Array (Array Expr) := #[]
    for e in es do
      seen := lenArgsOf f e seen
    for args in seen do
      let args ← args.mapM fun x ↦ Term.exprToSyntax x
      noteTerm (← `($(mkIdent n) $args*))
  evalTactic (← `(tactic| try simp only [List.length_append, List.length_replicate, List.length_cons,
    List.length_nil, List.length_singleton] at *))

end Meta

end

end LeanVM.Cost.Bounds.AS
