module

public import LeanVM.Cost.Bounds.Basic
public import LeanVM.Cost.Bounds.Sizes.Transcript
public import LeanVM.Cost.Prices
public meta import Lean.Elab.Tactic

/-!
# Bounds: sorted maps, amortized

A sorted map's insertion (`SortedMap.insert`, `carry`) merges equal-weight levels, a binary
counter: one insertion may merge every level, but `N` insertions merge `O(N log N)` entries in
all. The prices are bounded by a potential (Bentley–Saxe, Tarjan's banker's method):

* `potential D ls = Σ weight·(D − log₂ weight)`: a level's entries each still to be merged at most
  `D − log₂ weight` times, once every weight is below `2^D`;
* **`carry_amortized`**: if `carry` pays `a` per level it visits and `b` per entry it merges
  (`hnil`, `hne`, `heq`, read off a compiled `carry`'s recurrence), then
  `price + b·Φ(after) ≤ b·Φ(before) + b·w·(D − log₂ w) + a·(levels + 1)`, `w` the new level's
  weight: an insertion (`w = 1`) pays `b·D + a·(levels + 1)` amortized;
* the naturals a map compares and adds (positions, weights) up to `2^(D+1)` for `N < 2^D`
  insertions: their `limbCount` at most `limbsBelowTwoPow (D + 1) = (D + 1)/64 + 1` (`limbs_le_wl`), the tactic
  `limbs_bound hW` adding a bound for every `limbCount t` of the goal;
* **`listFoldl_amortized`**: a fold whose step pays at most `A` amortized (its price plus the
  potential after, at most the potential before plus `A`) pays `(A + 11)·n + 3` from a start of
  potential `0`.

The compiled maps (one `carry` per key and value type) instantiate them: the preimage index and
the first answers (`Bounds/Transcript.lean`), the replay's three maps.
-/

namespace LeanVM.Cost.Bounds

open LeanVM.Cost LeanVM.Cost.Library LeanVM.Extraction.Fast

public section

/-! ## The limbs of large naturals -/

/-- **A natural at most `2^E` has at most `E/64 + 1` limbs.** -/
theorem limbs_le_wl {t E : ℕ} (h : t ≤ 2 ^ E) : limbCount t ≤ limbsBelowTwoPow E := by
  unfold limbCount limbsBelowTwoPow
  rcases Nat.eq_zero_or_pos t with rfl | ht
  · simp
  · have hlt : t < 2 ^ (E + 1) := by rw [pow_succ]; omega
    have := (Nat.log2_lt (Nat.pos_iff_ne_zero.1 ht)).2 hlt
    have : Nat.log2 t / 64 ≤ E / 64 := Nat.div_le_div_right (by omega)
    omega

/-- The bound `limbsBelowTwoPow (D + 1)` for the naturals up to twice `2^D`. -/
theorem limbs_le_wl_two {D : ℕ} : ∀ x, x ≤ 2 * 2 ^ D → limbCount x ≤ limbsBelowTwoPow (D + 1) :=
  fun _ h ↦ limbs_le_wl (by rw [pow_succ]; omega)

section Meta

open Lean Meta Elab Tactic

/-- The arguments of the `limbCount` in `e` (no loose bound variables). -/
meta partial def limbsArgs (e : Expr) (acc : Array Expr := #[]) : Array Expr :=
  let acc := if e.isAppOfArity ``limbCount 1 && !e.hasLooseBVars && !acc.contains e.appArg! then
    acc.push e.appArg! else acc
  match e with
  | .app f a => limbsArgs a (limbsArgs f acc)
  | .lam _ t b _ | .forallE _ t b _ => limbsArgs b (limbsArgs t acc)
  | .letE _ t v b _ => limbsArgs b (limbsArgs v (limbsArgs t acc))
  | .mdata _ b | .proj _ _ b => limbsArgs b acc
  | _ => acc

/-- A proof of `ty` by `omega`, if it finds one. -/
meta def omegaProof? (ty : Expr) : TacticM (Option Expr) := do
  let m ← mkFreshExprMVar ty
  try
    let gs ← Tactic.run m.mvarId! (evalTactic (← `(tactic| omega)))
    if gs.isEmpty then return some (← instantiateMVars m) else return none
  catch _ => return none

/-- `limbs_bound hW` (`hW : ∀ x, x ≤ B → limbCount x ≤ W`): for every `limbCount t` of the goal, the
hypothesis `limbCount t = 1` if `omega` shows `t` word-sized, else `limbCount t ≤ W` if it shows
`t ≤ B`. -/
elab "limbs_bound " h:term : tactic => withMainContext do
  let hW ← elabTerm h none
  let tgt ← instantiateMVars (← getMainTarget)
  let mut g ← getMainGoal
  for t in limbsArgs tgt do
    let ts ← Term.exprToSyntax t
    let ty64 ← elabTerm (← `($ts < 2 ^ 64)) (some (mkSort Level.zero))
    if let some pf ← omegaProof? ty64 then
      (_, g) ← g.note `hlimbs (← mkAppM ``limbs_of_lt #[pf])
    else
      let hty ← whnf (← inferType (mkApp hW t))
      if hty.isForall then
        if let some pf ← omegaProof? hty.bindingDomain! then
          (_, g) ← g.note `hlimbs (mkApp2 hW t pf)
  replaceMainGoal [g]

end Meta

section Amortized

variable {α β : Type} [Ord α] [Std.TransOrd α] [Std.LawfulEqOrd α]

/-- **The potential** of levels below `2^D`: each level's weight times `D − log₂ weight`, the
merges its entries may still take part in. -/
@[expose] def potential (D : ℕ) (ls : List (Level α β)) : ℕ :=
  (ls.map fun l ↦ l.weight * (D - Nat.log2 l.weight)).sum

omit [Std.TransOrd α] [Std.LawfulEqOrd α] in
theorem potential_cons (D : ℕ) (l : Level α β) (ls : List (Level α β)) :
    potential D (l :: ls) = l.weight * (D - Nat.log2 l.weight) + potential D ls := by
  simp [potential]

omit [Std.TransOrd α] [Std.LawfulEqOrd α] in
@[simp] theorem potential_nil (D : ℕ) : potential D ([] : List (Level α β)) = 0 := rfl

/-- Every key of the levels satisfies `Q`. -/
@[expose] def KeysIn (Q : α → Prop) (ls : List (Level α β)) : Prop :=
  ∀ l ∈ ls, ∀ e ∈ l.entries, Q e.1

theorem keysIn_merge {Q : α → Prop} {l l' : Level α β} (h : KeysIn Q [l, l']) :
    ∀ e ∈ (l.merge l').entries, Q e.1 := by
  intro e he
  simp only [Level.merge, List.mem_toArray] at he
  rcases mem_mergeNewer he with h1 | h1
  · exact h l (by simp) e (by simpa using h1)
  · exact h l' (by simp) e (by simpa using h1)

/-- The key step of the potential: two levels of weight `2^e` merged, at most `2^(e+1)`
entries paid `b` each, are paid by the potential's drop. -/
theorem merge_potential_le (b D e s s' : ℕ) (hD : e + 1 ≤ D) (hs : s ≤ 2 ^ e) (hs' : s' ≤ 2 ^ e) :
    b * (s + s') + b * (2 ^ (e + 1) * (D - (e + 1))) ≤
      b * (2 ^ e * (D - e)) + b * (2 ^ e * (D - e)) := by
  obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hD
  have e1 : e + 1 + t - (e + 1) = t := by omega
  have e2 : e + 1 + t - e = t + 1 := by omega
  rw [e1, e2, pow_succ]
  have : b * (s + s') ≤ b * (2 * 2 ^ e) := Nat.mul_le_mul_left b (by omega)
  nlinarith

/-- **An insertion's carry, amortized**: `carry l ls` pays `a` per level it visits and `b` per
entry it merges; then its price and `b` times the potential after are at most `b` times the
potential before, `b·w·(D − log₂ w)` for the new level `l` of weight `w`, and `a` per level. -/
theorem carry_amortized (Q : α → Prop) (C : Level α β → List (Level α β) → ℕ) (a b D : ℕ)
    (hnil : ∀ l, l.weight ≤ 2 ^ D → C l [] ≤ a)
    (hne : ∀ l l' ls, l.weight ≤ 2 ^ D → l'.weight ≤ 2 ^ D → l.weight ≠ l'.weight →
      C l (l' :: ls) ≤ a)
    (heq : ∀ l l' ls, l.weight ≤ 2 ^ D → l.weight = l'.weight → KeysIn Q [l, l'] →
      C l (l' :: ls) ≤ a + b * (l.entries.size + l'.entries.size) + C (l.merge l') ls) :
    ∀ (ls : List (Level α β)) (l : Level α β), LevelsGood ls → LevelGood l →
      (∀ l' ∈ ls, l.weight ≤ l'.weight) → KeysIn Q (l :: ls) →
      l.weight + (ls.map (·.weight)).sum ≤ 2 ^ D →
      C l ls + b * potential D (carry l ls) ≤
        b * potential D ls + b * (l.weight * (D - Nat.log2 l.weight)) + a * (ls.length + 1) := by
  intro ls
  induction ls with
  | nil =>
    intro l _ _ _ _ hw
    have := hnil l (by simpa using hw)
    simp only [carry, potential_cons, potential_nil, List.length_nil]
    nlinarith
  | cons l' ls ih =>
    intro l hls hl hle hQ hw
    simp only [List.map_cons, List.sum_cons] at hw
    have hl'w : l'.weight ≤ 2 ^ D := by
      have := List.le_sum_of_mem (List.mem_map_of_mem (f := (·.weight)) (List.mem_cons_self (a := l') (l := ls)))
      simp only [List.map_cons, List.sum_cons] at this
      omega
    rw [carry]
    split
    · rename_i heqw
      obtain ⟨⟨e, he⟩, hs⟩ := hl
      obtain ⟨hpw, hgood⟩ := hls
      rw [List.map_cons, List.pairwise_cons] at hpw
      have hs' := (hgood l' (by simp)).2
      have hmw : (l.merge l').weight = 2 ^ (e + 1) := by
        simp only [Level.merge]; rw [pow_succ]; omega
      have hm : LevelGood (l.merge l') := by
        refine ⟨⟨e + 1, hmw⟩, ?_⟩
        simp only [Level.merge, List.size_toArray]
        have := length_mergeNewer_le l.entries.toList l'.entries.toList
        simp only [Array.length_toList] at this
        omega
      have hle' : ∀ l'' ∈ ls, (l.merge l').weight ≤ l''.weight := by
        intro l'' hl''
        have hlt := hpw.1 l''.weight (List.mem_map_of_mem hl'')
        obtain ⟨⟨f, hf⟩, -⟩ := hgood l'' (by simp [hl''])
        rw [hmw, hf]
        exact pow_two_le_of_lt (by rw [← he, ← hf, heqw]; exact hlt)
      have hQ2 : KeysIn Q [l, l'] := fun x hx ↦ hQ x (by simp at hx ⊢; tauto)
      have hQ' : KeysIn Q (l.merge l' :: ls) := by
        intro x hx
        rcases List.mem_cons.1 hx with rfl | hx
        · exact keysIn_merge hQ2
        · exact hQ x (by simp [hx])
      have hw' : (l.merge l').weight + (ls.map (·.weight)).sum ≤ 2 ^ D := by
        simp only [Level.merge]; omega
      have ih' := ih (l.merge l') ⟨hpw.2, fun x hx ↦ hgood x (by simp [hx])⟩ hm hle' hQ' hw'
      have hc := heq l l' ls (by omega) heqw hQ2
      rw [hmw, Nat.log2_two_pow] at ih'
      rw [potential_cons, ← heqw, he, Nat.log2_two_pow]
      have hD : e + 1 ≤ D := by
        have : 2 ^ (e + 1) ≤ 2 ^ D := by rw [pow_succ]; omega
        exact (Nat.pow_le_pow_iff_right (by norm_num)).1 this
      have hkey := merge_potential_le b D e l.entries.size l'.entries.size hD (by omega) (by omega)
      simp only [List.length_cons]
      nlinarith
    · rename_i hne'
      have := hne l l' ls (by omega) hl'w hne'
      simp only [potential_cons, List.length_cons]
      nlinarith

/-- **An insertion, amortized**: the carry of a new level `l` of weight `1` and one entry (the
level `SortedMap.insert` makes) into a good map of fewer than `2^D` insertions pays
`b·D + a·(levels + 1)` amortized. -/
theorem insert_amortized (Q : α → Prop) (C : Level α β → List (Level α β) → ℕ) (a b D : ℕ)
    (hnil : ∀ l, l.weight ≤ 2 ^ D → C l [] ≤ a)
    (hne : ∀ l l' ls, l.weight ≤ 2 ^ D → l'.weight ≤ 2 ^ D → l.weight ≠ l'.weight →
      C l (l' :: ls) ≤ a)
    (heq : ∀ l l' ls, l.weight ≤ 2 ^ D → l.weight = l'.weight → KeysIn Q [l, l'] →
      C l (l' :: ls) ≤ a + b * (l.entries.size + l'.entries.size) + C (l.merge l') ls)
    (m : SortedMap α β) (hm : smGood m) (hQ : KeysIn Q m.levels) (hN : smWeightSum m < 2 ^ D)
    (l : Level α β) (hw : l.weight = 1) (hs : l.entries.size = 1) (hk : ∀ e ∈ l.entries, Q e.1) :
    C l m.levels + b * potential D (carry l m.levels) ≤
      b * potential D m.levels + b * D + a * (m.levels.length + 1) := by
  have hle : ∀ l' ∈ m.levels, l.weight ≤ l'.weight := by
    intro l' hl'
    obtain ⟨⟨e, he⟩, -⟩ := hm.2 l' hl'
    rw [he, hw]; exact Nat.one_le_two_pow
  have h := carry_amortized Q C a b D hnil hne heq m.levels l hm ⟨⟨0, hw⟩, by omega⟩ hle (by
      intro l' hl e he
      rcases List.mem_cons.1 hl with rfl | hl
      · exact hk e he
      · exact hQ l' hl e he) (by unfold smWeightSum at hN; omega)
  have h1 : Nat.log2 1 = 0 := Nat.log2_two_pow (n := 0)
  rw [hw, h1, Nat.sub_zero, Nat.one_mul] at h
  exact h

/-- An insertion keeps the keys in `Q`. -/
theorem keysIn_insert {Q : α → Prop} {m : SortedMap α β} (hQ : KeysIn Q m.levels) {k : α}
    (hk : Q k) (v : β) : KeysIn Q (m.insert k v).levels := by
  unfold SortedMap.insert
  have : ∀ (ls : List (Level α β)) (l : Level α β), KeysIn Q (l :: ls) → KeysIn Q (carry l ls) := by
    intro ls
    induction ls with
    | nil => intro l h; simpa [carry] using h
    | cons l' ls ih =>
      intro l h
      rw [carry]
      split
      · refine ih _ fun x hx ↦ ?_
        rcases List.mem_cons.1 hx with rfl | hx
        · exact keysIn_merge fun y hy ↦ h y (by simp at hy ⊢; tauto)
        · exact h x (by simp [hx])
      · exact h
  refine this _ _ fun l hl e he ↦ ?_
  rcases List.mem_cons.1 hl with rfl | hl
  · simp at he; rw [he]; exact hk
  · exact hQ l hl e he

omit [Std.TransOrd α] [Std.LawfulEqOrd α] in
/-- A good map's levels: each of at most `2^D` entries and weight, and at most `D` of them, below
`2^D` insertions. -/
theorem smGood_levels_le {m : SortedMap α β} (hm : smGood m) {D : ℕ} (hN : smWeightSum m < 2 ^ D) :
    m.levels.length ≤ D ∧ ∀ l ∈ m.levels, l.entries.size ≤ l.weight ∧ l.weight ≤ 2 ^ D := by
  refine ⟨?_, fun l hl ↦ ⟨(hm.2 l hl).2, ?_⟩⟩
  · have := sm_two_pow_levels_le hm
    have h2 : 2 ^ m.levels.length ≤ 2 ^ D := by omega
    exact (Nat.pow_le_pow_iff_right (by norm_num)).1 h2
  · have := List.le_sum_of_mem (List.mem_map_of_mem (f := (·.weight)) hl)
    unfold smWeightSum at hN
    omega

end Amortized

/-! ## A fold, amortized -/

section Fold

variable (P : MachineProgram) {α β : Type} [MachineEncoding α] [MachineEncoding β]

/-- **`List.foldl`, amortized** (`listFoldl`): a step at an accumulator of invariant `I acc r`
(`r` the elements left) pays at most `A` plus the drop of a potential `Φ`; then the fold pays at
most `Φ init + (A + 11)·n + 3`. -/
theorem listFoldl_amortized (hP : Includes P listFoldl.costDeps) (f : α → β → α) (fVal : MachineValue)
    (hf : ∀ a b, RunsApp P fVal [encodeValue a, encodeValue b] (encodeValue (f a b))) (A : ℕ) (Φ : α → ℕ)
    (I : α → ℕ → Prop) :
    ∀ (l : List β) (init : α), I init l.length →
      (∀ acc r, I acc (r + 1) → ∀ b ∈ l, I (f acc b) r ∧
        appCost P fVal [encodeValue acc, encodeValue b] + Φ (f acc b) ≤ Φ acc + A) →
      machineCost P listFoldl.costIdx [fVal, encodeValue init, encodeValue l] ≤ Φ init + (A + 11) * l.length + 3 := by
  intro l
  induction l with
  | nil => intro init _ _; rw [listFoldl.costEq_nil P hP f fVal hf]; omega
  | cons b l ih =>
    intro init hI hB
    rw [listFoldl.costEq_cons P hP f fVal hf]
    obtain ⟨hI', h2⟩ := hB init l.length (by simpa using hI) b (by simp)
    have h1 := ih (f init b) hI' (fun acc r hacc b' hb ↦ hB acc r hacc b' (by simp [hb]))
    simp only [List.length_cons]
    nlinarith

end Fold

end

end LeanVM.Cost.Bounds
