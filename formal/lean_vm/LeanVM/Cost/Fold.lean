module

public import LeanVM.Cost.Rules
public meta import Lean.Meta.Tactic.Simp.Main
public meta import Lean.Meta.LitValues

/-!
# Folding a price's constants

The compiler (`Cost/Compiler.lean`) states each function's price recurrence (`costEq`) with its
right side folded by `foldPrice`: a fixed `simp` set (no `0 +`, lengths of literal lists, fields of
literal pairs, `limbCount` of literals, `max` with `limbCount 0`, …) and `foldSum`, which gathers a sum's
literals at its end (`2 + (a + (b + 1))` becomes `a + b + 3`). The folded equation is proved from
the raw one by `simp`'s proof, or by `rfl` for a closed price (`closedValue?`), so nothing here is
trusted.
-/

namespace LeanVM.Cost

@[expose] public section

/-- Sums nested to the left. -/
theorem add_left_nest (a b c : ℕ) : a + (b + c) = a + b + c := (Nat.add_assoc a b c).symm

end

public meta section

namespace Fold

open Lean Meta Simp

/-- A natural number literal (`OfNat` or raw). -/
def litVal? (e : Expr) : Option Nat :=
  match e.nat? with
  | some n => some n
  | none => match e with
    | .lit (.natVal n) => some n
    | _ => none

/-- **A sum's literals at its end**, on left-nested sums (`add_left_nest` nests them):
`c + x ↦ x + c`, `(x + c) + y ↦ (x + y) + c`, `(x + a) + b ↦ x + (a + b)` for literals. A sum
`T₁ + T₂ + … + c` keeps `whnf` cheap: `Nat.add` recurses on its second argument, a literal. -/
def foldSum : Simproc := fun e ↦ do
  let_expr HAdd.hAdd α _ _ _ x y := e | return .continue
  unless α.isConstOf ``Nat do return .continue
  match litVal? x, litVal? y with
  | some _, some _ => return .continue
  | some _, none =>
    return .visit { expr := ← mkAdd y x, proof? := ← mkAppM ``Nat.add_comm #[x, y] }
  | none, _ =>
    let_expr HAdd.hAdd _ _ _ _ x₁ x₂ := x | return .continue
    let some a := litVal? x₂ | return .continue
    match litVal? y with
    | some b =>
      let e' ← mkAdd x₁ (mkNatLit (a + b))
      let pf ← mkAppM ``Nat.add_assoc #[x₁, x₂, y]
      return .visit { expr := e', proof? := ← mkExpectedTypeHint pf (← mkEq e e') }
    | none =>
      let e' ← mkAdd (← mkAdd x₁ y) x₂
      return .visit { expr := e', proof? := ← mkAppM ``Nat.add_right_comm #[x₁, x₂, y] }

/-- The heads the fold looks into: sums, products, `max`, `if`, the `casesOn`s, lengths of literal
lists. Everything else (the values `encodeValue x`, `limbCount n`, sizes, conditions, a price's callee
`machineCost P j vs`) is kept as it is: the fold changes prices, never values. -/
def priceHeads : List Name :=
  [``HAdd.hAdd, ``HMul.hMul, ``Max.max, ``ite, ``dite, ``cond, ``List.length]

/-- A word-sized literal's `limbCount`: `1`; any other term outside `priceHeads` (and not a `casesOn`):
not visited. -/
def guardData : Simproc := fun e ↦ do
  if e.isAppOfArity ``limbCount 1 then
    if let some n := litVal? e.appArg! then
      if n < 2 ^ 64 then
        let lt ← mkAppM ``LT.lt #[e.appArg!, ← mkAppM ``HPow.hPow #[mkNatLit 2, mkNatLit 64]]
        let pf ← mkAppM ``limbs_of_lt #[← mkDecideProof lt]
        return .done { expr := mkNatLit 1, proof? := pf }
    return .done { expr := e }
  match e.getAppFn with
  | .const n _ =>
    if priceHeads.contains n || isCasesOnRecursor (← getEnv) n then return .continue
    return .done { expr := e }
  | .lam .. => return .continue
  | .bvar _ | .mdata .. => return .continue
  | _ => return .done { expr := e }

/-- The lemmas of the fold. -/
def foldLemmas : List Name :=
  [``Nat.add_zero, ``Nat.zero_add, ``add_left_nest, ``Nat.mul_one, ``Nat.one_mul,
    ``List.length_nil, ``List.length_cons, ``max_self, ``max_limbs_one, ``max_one_limbs]

/-- The simplifier's context and simprocs of the fold. -/
def foldContext (iota : Bool) : MetaM (Simp.Context × SimprocsArray) := do
  let thms ← foldLemmas.foldlM (fun s n ↦ s.addConst n) ({} : SimpTheorems)
  let ctx ← mkContext (config := { iota, proj := true, beta := true, zeta := false })
    (simpTheorems := #[thms]) (congrTheorems := ← getSimpCongrTheorems)
  let addKeys ← withSimpGlobalConfig do
    let a ← mkFreshExprMVar (mkConst ``Nat)
    let b ← mkFreshExprMVar (mkConst ``Nat)
    DiscrTree.mkPath (← mkAdd a b)
  let anyKeys ← withSimpGlobalConfig do
    DiscrTree.mkPath (← mkFreshExprMVar (mkConst ``Nat))
  let s := (← getSimprocs).addCore addKeys `LeanVM.Cost.Fold.foldSum true (.inl foldSum)
  let s := s.addCore anyKeys `LeanVM.Cost.Fold.guardData false (.inl guardData)
  return (ctx, #[s])

/-- The length of a literal list (`List.cons`, `List.nil`). -/
partial def listLength? (e : Expr) : Option Nat :=
  match e.getAppFnArgs with
  | (``List.nil, #[_]) => some 0
  | (``List.cons, #[_, _, t]) => (· + 1) <$> listLength? t
  | _ => none

/-- **A closed price's value**: a price made of literals, sums, products and lengths of literal
lists only, which the fold's `simp` would reduce to that literal. -/
partial def closedValue? (e : Expr) : Option Nat :=
  match litVal? e with
  | some n => some n
  | none => match e.getAppFnArgs with
    | (``HAdd.hAdd, #[α, _, _, _, a, b]) =>
      if α.isConstOf ``Nat then (· + ·) <$> closedValue? a <*> closedValue? b else none
    | (``HMul.hMul, #[α, _, _, _, a, b]) =>
      if α.isConstOf ``Nat then (· * ·) <$> closedValue? a <*> closedValue? b else none
    | (``List.length, #[_, l]) => listLength? l
    | _ => none

/-- **The fold** of a price `e`: the folded price and a proof `e = e'` (`none`: unchanged); with
`iota`, a `casesOn` on a constructor reduced. A closed price (`closedValue?`) is its literal at
once, by `rfl`: `simp` on a large literal's price is slow. -/
def foldPrice (e : Expr) (iota := false) : MetaM Simp.Result := do
  if let some n := closedValue? e then
    if (litVal? e).isSome then return { expr := e }
    let v := mkNatLit n
    return { expr := v, proof? := ← mkExpectedTypeHint (← mkEqRefl v) (← mkEq e v) }
  let (ctx, s) ← foldContext iota
  let (r, _) ← Meta.simp e ctx s
  return r

end Fold

end

end LeanVM.Cost
