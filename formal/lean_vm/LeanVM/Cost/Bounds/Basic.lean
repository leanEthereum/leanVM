module

public import LeanVM.Cost.Library
public meta import Lean.Elab.Tactic
meta import LeanVM.Cost.Compiler

/-!
# Bounds on prices: the method and its library

The compiler gives every compiled function `g` (function `i` of the program) a spec at the
machine's price, `machineCost P i (args x)`, and that price's recurrence, `g.costEq`: an equation
`machineCost P i (args x) = C[x]`, `C` a sum of constants, `limbCount` of the numbers the body
compares or adds, sizes of the arrays it builds, the prices of its callees
(`machineCost P j …`), of the closures it applies (`appCost P v …`), and `casesOn`/`if` on the
values it inspects. A closed-form bound on `g`'s price is proved by:

1. **strong induction on the measure** of the compilation (the same as the spec's), or none for a
   function that is not recursive;
2. `rw [g.costEq P (by includes) …]`: the price as its recurrence (`g.costEq_nil`,
   `g.costEq_cons`, `g.costEq_zero`, `g.costEq_succ`, … at a constructor of the parameter the body
   cases on: the case already reduced); the prices are stated with `g.costIdx`;
3. **case analysis** on what the body inspects (`cases l`, `cases n`, `split`, `generalize … ;
   cases`), until no `casesOn` is left; `simp only [cost_simps]` folds the constants, the lengths
   of literal lists and `limbCount` of word-sized numbers;
4. `cost_facts [bound₁, bound₂, …]`: every price in the goal that a bound of a callee (or the
   induction hypothesis) covers gets that bound as a hypothesis (instantiated by unification, its
   side conditions closed by `omega`, an `Includes` premise from the context);
5. `omega` (or `nlinarith` for products of sizes).

Steps 2–5 never look at the machine's code: the compiler already proved the recurrence. A bound
of a callee composes because it is a theorem about `machineCost P j …` for every program `P`
holding `j`'s bodies (`Includes P j.costDeps`), as the spec is; `includes` derives that premise
from the caller's.

Here: the tactics `includes`, `cost_facts`, `cost_simp`; `limbCount` of word-sized numbers; products
of sizes as atoms (`affine_mul_le`); the recurrence solvers (`le_of_halving` for a binary search,
`le_of_doubling` for a binary tree); the bounds of the library's polymorphic functions
(`listZipWith_le`, `listFoldl_le`), proved once for every element type and closure, and of an
on-demand `List.map` by its recurrence (`listMap_le`).
-/

namespace LeanVM.Cost.Bounds

open LeanVM.Cost LeanVM.Cost.Library

public section

/-! ## The program's bodies: `Includes` of a callee from the caller's -/

section Meta

open Lean Meta Elab Tactic

/-- A proof of `x ∈ l`, `l` a list literal holding `x` syntactically. -/
meta partial def memProof (x l : Expr) : MetaM Expr := do
  unless l.isAppOfArity ``List.cons 3 do throwError "includes: {x} not among the bodies"
  let hd := l.appFn!.appArg!
  let tl := l.appArg!
  let ty ← mkAppM ``Membership.mem #[l, x]
  if hd == x then
    mkExpectedTypeHint (← mkAppOptM ``List.Mem.head #[none, x, tl]) ty
  else
    mkExpectedTypeHint (← mkAppOptM ``List.Mem.tail #[none, x, hd, tl, ← memProof x tl]) ty

/-- A proof of `List.Forall (· ∈ l) l'`, every entry of the literal `l'` in the literal `l`. -/
meta partial def forallMemProof (l l' : Expr) : MetaM Expr := do
  if l'.isAppOfArity ``List.cons 3 then
    let a ← memProof l'.appFn!.appArg! l
    if l'.appArg!.isAppOfArity ``List.cons 3 then
      mkAppM ``And.intro #[a, ← forallMemProof l l'.appArg!]
    else return a
  else if l'.isAppOf ``List.nil then return mkConst ``True.intro
  else throwError "includes: {l'} is not a list of bodies"

/-- A list of bodies as a literal: `f.costDeps` unfolded. -/
meta def depsLiteral (e : Expr) : MetaM Expr := do
  let e ← instantiateMVars e
  if e.isAppOf ``List.cons || e.isAppOf ``List.nil then return e
  match ← unfoldDefinition? e with
  | some e' => return e'
  | none => return e

/-- `Includes P l'` from `hP : Includes P l`, when `l` holds every body of `l'`: by a sublist proof
(`Includes.ofSublist`, one constructor per body of `l`: the compiler sorts the bodies by index), else
by a membership proof per body of `l'`. -/
meta def includesFrom (hP goalTy : Expr) : MetaM Expr := do
  let hTy ← whnfR (← instantiateMVars (← inferType hP))
  let gTy ← whnfR (← instantiateMVars goalTy)
  unless hTy.isAppOfArity ``Includes 2 && gTy.isAppOfArity ``Includes 2 do
    throwError "includes: not an `Includes`"
  unless ← isDefEq hTy.appFn!.appArg! gTy.appFn!.appArg! do throwError "includes: other program"
  let l ← depsLiteral hTy.appArg!
  let l' ← depsLiteral gTy.appArg!
  try
    let pairTy ← mkAppM ``Prod #[mkConst ``Nat, mkConst ``LeanVM.Cost.Term]
    let hs ← LeanVM.Cost.Compiler.sublistProof pairTy l' l
    return mkAppN (mkConst ``Includes.ofSublist) #[hTy.appFn!.appArg!, l, l', hP, hs]
  catch _ =>
    let fa ← forallMemProof l l'
    return mkAppN (mkConst ``Includes.ofForall) #[hTy.appFn!.appArg!, l, l', hP, fa]

/-- Close `Includes P l'` from an `Includes P l` of the context. -/
meta def includesAuto (g : MVarId) : MetaM Bool := g.withContext do
  let goalTy ← g.getType
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    if (← instantiateMVars d.type).isAppOf ``Includes then
      try
        let pf ← includesFrom d.toExpr goalTy
        g.assign pf
        return true
      catch _ => pure ()
  return false

/-- `includes`: close `Includes P l'` from a hypothesis `Includes P l` whose bodies hold `l'`'s
(a callee's `costDeps` from its caller's). -/
elab "includes" : tactic => do
  let g ← getMainGoal
  unless ← includesAuto g do throwError "includes: no hypothesis holds these bodies"
  replaceMainGoal []

/-- Close a side condition of a bound: an `Includes` from the context, else by a tactic. -/
meta def discharge (g : MVarId) : TacticM Bool := do
  if ← includesAuto g then return true
  try
    let tac ← `(tactic| first | assumption | omega | (simp_all; done) | decide)
    let rest ← Tactic.run g (Tactic.evalTactic tac)
    return rest.isEmpty
  catch _ => return false

/-- The prices `machineCost P i vs` and `appCost P v vs` in `e` (no loose bound variables). -/
meta partial def pricesIn (e : Expr) (acc : Array Expr := #[]) : Array Expr :=
  let acc := if (e.isAppOfArity ``machineCost 3 || e.isAppOfArity ``appCost 3) &&
      !e.hasLooseBVars && !acc.contains e then acc.push e else acc
  match e with
  | .app f a => pricesIn a (pricesIn f acc)
  | .lam _ t b _ | .forallE _ t b _ => pricesIn b (pricesIn t acc)
  | .letE _ t v b _ => pricesIn b (pricesIn v (pricesIn t acc))
  | .mdata _ b | .proj _ _ b => pricesIn b acc
  | _ => acc

/-- Instantiate `pf`'s statement `∀ …, lhs ≤ rhs` (or `=`, `<`) at the price `s`: the proof, its
side conditions discharged, if `lhs` unifies with `s`. -/
meta def instantiateAt (pf s : Expr) : TacticM (Option Expr) := do
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
      else
        saved.restore
        return none
  return some (← instantiateMVars (mkAppN pf xs))

/-- `cost_facts [h₁, …, hₙ]`: for every price in the goal (`machineCost P i vs`, `appCost P v vs`,
outside binders) and every `hₖ : ∀ …, lhs ≤ rhs` (or `=`) whose `lhs` unifies with it, add the
instance as a hypothesis; its side conditions are closed from the context (an `Includes` by
`includes`, the rest by `assumption`, `omega`, `simp_all` or `decide`), or the instance is
skipped. Then `omega` (or `nlinarith`) closes a goal that is linear in the prices. -/
elab "cost_facts" " [" hs:term,* "]" : tactic => withMainContext do
  let pfs ← hs.getElems.mapM fun h ↦ elabTerm h none
  let goal ← getMainGoal
  let prices := pricesIn (← instantiateMVars (← goal.getType))
  let mut g := goal
  for s in prices do
    for pf in pfs do
      let r ← g.withContext (instantiateAt pf s)
      if let some p := r then
        let (_, g') ← (← g.assert `hcost (← inferType p) p).intro1P
        g := g'
        break
  replaceMainGoal [g]

end Meta

/-! ## `limbCount` of word-sized numbers -/

theorem limbs_le_add_one (n : ℕ) : limbCount n ≤ n + 1 := by
  have := Nat.log2_le_self n
  unfold limbCount
  omega

@[simp] theorem limbs_zero : limbCount 0 = 1 := rfl

@[simp] theorem limbs_one : limbCount 1 = 1 := rfl

theorem limbs_two_pow {k : ℕ} (hk : k < 64) : limbCount (2 ^ k) = 1 :=
  limbs_of_lt (Nat.pow_lt_pow_right (by norm_num) hk)

theorem limbs_shift {k : ℕ} (hk : k < 64) : limbCount (1 <<< k) = 1 := by
  rw [Nat.one_shiftLeft]; exact limbs_two_pow hk

/-- Numbers below `2^128` have at most two limbs. -/
theorem limbs_le_two {x : ℕ} (h : x < 2 ^ 128) : limbCount x ≤ 2 := by
  unfold limbCount
  rcases Nat.eq_zero_or_pos x with rfl | hx
  · simp
  · have := (Nat.log2_lt (by omega)).2 h
    omega

theorem appCost_fn (P : MachineProgram) (j : ℕ) (us vs : List MachineValue) :
    appCost P (.closure j us) vs = machineCost P j (us ++ vs) + us.length := rfl

/-- `cost_simp`: fold a recurrence's constants: `limbCount` of numbers `omega` shows word-sized, the
lengths of literal lists, a known closure's price as its function's. It may do nothing (the
compiler's equations come folded already; a case split may leave nothing to fold). -/
syntax (name := costSimp) "cost_simp" : tactic

macro_rules
  | `(tactic| cost_simp) => `(tactic| simp (config := { failIfUnchanged := false })
    (disch := omega) only [limbs_of_lt, List.length_nil, List.length_cons, appCost_fn,
    List.nil_append, List.cons_append, Nat.add_zero, Nat.zero_add, Nat.rec_zero, Nat.rec_add_one,
    max_self, max_limbs_one, max_one_limbs])

/-- `cost_simp at h ⊢`. -/
syntax (name := costSimpAt) "cost_simp" " at " Lean.Parser.Tactic.locationHyp : tactic

macro_rules
  | `(tactic| cost_simp at $loc) => `(tactic| simp (config := { failIfUnchanged := false })
    (disch := omega) only [limbs_of_lt, List.length_nil, List.length_cons, appCost_fn,
    List.nil_append, List.cons_append, Nat.add_zero, Nat.zero_add, Nat.rec_zero, Nat.rec_add_one,
    max_self, max_limbs_one, max_one_limbs] at $loc)

#allow_unused_tactic! LeanVM.Cost.Bounds.costSimp LeanVM.Cost.Bounds.costSimpAt

/-- A price affine in `D`, paid `n ≤ C` times, with `D·C` an atom: `omega` reads the result (the
bounds state products of sizes as such atoms, so a sum of bounds stays linear). -/
theorem affine_mul_le (a b D n C : ℕ) (h : n ≤ C) : (a * D + b) * n ≤ a * (D * C) + b * C := by
  have := Nat.mul_le_mul_left (a * D + b) h
  nlinarith

theorem affine_mul_le' (a b c D n C : ℕ) (h : n ≤ C) :
    (a * D + b + c) * n ≤ a * (D * C) + (b + c) * C := by
  have := affine_mul_le a (b + c) D n C h
  rwa [Nat.add_assoc]

/-! ## Recurrence solvers -/

theorem log2_half {n : ℕ} (h : 2 ≤ n) : Nat.log2 (n / 2) + 1 = Nat.log2 n := by
  rw [Nat.log2_def n]; simp [h]

theorem log2_lt_of {n k : ℕ} (hk : 0 < k) (h : n < 2 ^ k) : Nat.log2 n < k := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [Nat.log2_zero]; omega
  · exact (Nat.log2_lt (by omega)).2 h

theorem log2_mono {m n : ℕ} (h : m ≤ n) : Nat.log2 m ≤ Nat.log2 n := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp
  · exact (Nat.le_log2 (by omega)).2 (le_trans (Nat.log2_self_le (by omega)) h)

/-- **Halving** (a binary search): a price that, on arguments of an invariant `I`, either stops at
`b` (always so at measure `0`), or pays `a` and recurs on arguments of `I` of a measure at most
half as large, is at most `b + a·(log₂ m + 1)`. -/
theorem le_of_halving {α : Type} (I : α → Prop) (m T : α → ℕ) (a b : ℕ)
    (hz : ∀ x, I x → m x = 0 → T x ≤ b)
    (h : ∀ x, I x → 0 < m x → T x ≤ b ∨ ∃ y, I y ∧ m y ≤ m x / 2 ∧ T x ≤ a + T y) :
    ∀ x, I x → T x ≤ b + a * (Nat.log2 (m x) + 1) := by
  intro x hx
  induction hm : m x using Nat.strong_induction_on generalizing x with
  | _ n ih =>
    rcases Nat.eq_zero_or_pos (m x) with h0 | hpos
    · have := hz x hx h0; nlinarith
    rcases h x hx hpos with h1 | ⟨y, hy, hmy, h2⟩
    · nlinarith
    · have ihy := ih (m y) (by omega) y hy rfl
      subst hm
      rcases Nat.lt_or_ge (m y) 1 with h0 | h1
      · have := hz y hy (by omega)
        nlinarith
      · have h2x : 2 ≤ m x := by omega
        have := log2_mono hmy
        have := log2_half h2x
        have : a * (Nat.log2 (m y) + 1) + a ≤ a * (Nat.log2 (m x) + 1) := by nlinarith
        omega

/-- **Doubling** (a binary tree of height `k`): `T 0 x ≤ b`, and `T (k + 1) x` at most
`a + c·2^(k+1)` and the prices of two subtrees of height `k`, give `T k x + a ≤ 2^k·(a + b + c·k)`:
`a + b` per leaf, `c` per leaf and level. -/
theorem le_of_doubling {α : Type} (T : ℕ → α → ℕ) (a b c : ℕ) (h0 : ∀ x, T 0 x ≤ b)
    (hs : ∀ k x, ∃ y z, T (k + 1) x ≤ a + c * 2 ^ (k + 1) + T k y + T k z) :
    ∀ k x, T k x + a ≤ 2 ^ k * (a + b + c * k) := by
  intro k
  induction k with
  | zero => intro x; have := h0 x; simp; omega
  | succ k ih =>
    intro x
    obtain ⟨y, z, h⟩ := hs k x
    have hy := ih y
    have hz := ih z
    have h2 : 2 ^ (k + 1) = 2 * 2 ^ k := by ring
    rw [h2] at h ⊢
    nlinarith

/-! ## The library's polymorphic functions -/

section Library

variable (P : MachineProgram) {α β γ : Type} [MachineEncoding α] [MachineEncoding β] [MachineEncoding γ]

/-- **`List.zipWith`** (`listZipWith`): `19` per pair and the closure's price, `7` at the end. -/
theorem listZipWith_le (hP : Includes P listZipWith.costDeps) (f : α → β → γ) (fVal : MachineValue)
    (hf : ∀ a b, RunsApp P fVal [encodeValue a, encodeValue b] (encodeValue (f a b))) (B : ℕ) :
    ∀ (xs : List α) (ys : List β), (∀ a ∈ xs, ∀ b ∈ ys, appCost P fVal [encodeValue a, encodeValue b] ≤ B) →
      machineCost P listZipWith.costIdx [fVal, encodeValue xs, encodeValue ys] ≤
        (B + 19) * min xs.length ys.length + 7 := by
  intro xs
  induction xs with
  | nil => intro ys _; rw [listZipWith.costEq_nil P hP f fVal hf]; omega
  | cons a xs ih =>
    intro ys hB
    rw [listZipWith.costEq_cons P hP f fVal hf]
    cases ys with
    | nil => simp
    | cons b ys =>
      have h1 := ih ys (fun a' ha b' hb ↦ hB a' (by simp [ha]) b' (by simp [hb]))
      have h2 := hB a (by simp) b (by simp)
      simp only [List.length_cons]
      rw [Nat.min_def] at h1 ⊢
      split_ifs at h1 ⊢ <;> nlinarith

/-- **`List.foldl`** (`listFoldl`): `11` per element and the closure's price, `3` at the end; the
closure's price bounded on the accumulators an invariant `I` holds. -/
theorem listFoldl_le (hP : Includes P listFoldl.costDeps) (f : α → β → α) (fVal : MachineValue)
    (hf : ∀ a b, RunsApp P fVal [encodeValue a, encodeValue b] (encodeValue (f a b))) (B : ℕ) (I : α → Prop) :
    ∀ (l : List β) (init : α), I init →
      (∀ acc, I acc → ∀ b ∈ l, I (f acc b) ∧ appCost P fVal [encodeValue acc, encodeValue b] ≤ B) →
      machineCost P listFoldl.costIdx [fVal, encodeValue init, encodeValue l] ≤ (B + 11) * l.length + 3 := by
  intro l
  induction l with
  | nil => intro init _ _; rw [listFoldl.costEq_nil P hP f fVal hf]; omega
  | cons b l ih =>
    intro init hI hB
    rw [listFoldl.costEq_cons P hP f fVal hf]
    obtain ⟨hI', h2⟩ := hB init hI b (by simp)
    have h1 := ih (f init b) hI' (fun acc hacc b' hb ↦ hB acc hacc b' (by simp [hb]))
    simp only [List.length_cons]
    nlinarith

/-- **`List.map`, by its recurrence**: an on-demand `List.map` (compiled once per program, at its
own index `i`) has these two equations (its `costEq_nil` and `costEq_cons`); then `13` per
element and the closure's price, `3` at the end. -/
theorem listMap_le (i : ℕ) {α : Type} [MachineEncoding α] (fVal : MachineValue)
    (h0 : machineCost P i [fVal, encodeValue ([] : List α)] = 3)
    (hs : ∀ (x : α) (l : List α), machineCost P i [fVal, encodeValue (x :: l)] =
      appCost P fVal [encodeValue x] + machineCost P i [fVal, encodeValue l] + 13)
    (B : ℕ) : ∀ l : List α, (∀ a ∈ l, appCost P fVal [encodeValue a] ≤ B) →
      machineCost P i [fVal, encodeValue l] ≤ (B + 13) * l.length + 3 := by
  intro l
  induction l with
  | nil => intro _; rw [h0]; simp
  | cons x l ih =>
    intro hB
    rw [hs]
    have h1 := ih fun a ha ↦ hB a (by simp [ha])
    have h2 := hB x (by simp)
    simp only [List.length_cons]
    nlinarith

/-- **`List.foldl`, an invariant indexed by the elements left** (an accumulator growing along
the fold): `I k acc` with `k` elements left. -/
theorem listFoldl_le_idx (hP : Includes P listFoldl.costDeps) (f : α → β → α) (fVal : MachineValue)
    (hf : ∀ a b, RunsApp P fVal [encodeValue a, encodeValue b] (encodeValue (f a b))) (B : ℕ) (I : ℕ → α → Prop)
    (L : List β)
    (hI : ∀ k acc, I (k + 1) acc → ∀ b ∈ L, I k (f acc b) ∧ appCost P fVal [encodeValue acc, encodeValue b] ≤ B) :
    ∀ (l : List β) (init : α), (∀ b ∈ l, b ∈ L) → I l.length init →
      machineCost P listFoldl.costIdx [fVal, encodeValue init, encodeValue l] ≤ (B + 11) * l.length + 3 := by
  intro l
  induction l with
  | nil => intro init _ _; rw [listFoldl.costEq_nil P hP f fVal hf]; omega
  | cons b l ih =>
    intro init hL hi
    rw [listFoldl.costEq_cons P hP f fVal hf]
    obtain ⟨hI', h2⟩ := hI l.length init hi b (hL b (by simp))
    have h1 := ih (f init b) (fun c hc ↦ hL c (by simp [hc])) hI'
    simp only [List.length_cons]
    nlinarith

end Library

end

end LeanVM.Cost.Bounds
