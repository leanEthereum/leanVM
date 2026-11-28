/-
  LeanVM.Guest.B1.Place.ArmRoots

  The callees of `open_stacked`'s arms, and a check over their subtrees that visits each function once.
-/

module

public import LeanVM.Guest.Memory.CalleeIdx
public import LeanVM.Guest.CoreRef

/-!
# The arms' callees, each subtree checked once

The arms share most of their callees, and their callees share most of their subtrees: a check that recurses
through each callee's subtree (`exactJ`, `noWitJ`) repeats the shared functions in every kernel evaluation. Instead:

* `armRoots`: every arm's callees' indices, each once and in increasing order (`mem_armRoots`);
* `armGrp i last`: the seventy roots from `70 * i` (with `last`, every root from there), each group a kernel
  evaluation of its own (`armRoots_all` joins them);
* `postOrder L`: the functions under the roots `L`, each once, every callee but a self-call before its caller
  (a depth-first walk of the generated callee table, `Data.calleesJ`);
* `goodStep loc`: a pass over that order collecting, in a bit set, the functions passing `loc` whose callees but
  themselves were collected before. For a check `J` by depth whose step is `loc` and the callees (`goodFold`), every
  collected function passes `J` at some depth; a function's check is evaluated once per group.

The order is not trusted: any list gives a sound pass, a bad one only collects less.
-/

namespace LeanVM.Guest.B1.Arm

open LeanVM.Guest.Core LeanVM.Guest.Memory

@[expose] public section

/-- The arms' indices. -/
def armIdxs : List ℕ :=
  [idx% «open_stacked__L0», idx% «open_stacked__L1», idx% «open_stacked__L2», idx% «open_stacked__L3»,
    idx% «open_stacked__L4», idx% «open_stacked__L5», idx% «open_stacked__L6», idx% «open_stacked__L7»,
    idx% «open_stacked__L8», idx% «open_stacked__L9», idx% «open_stacked__L10»]

/-- The bit set of the indices `l`, added to `b`. -/
def bitsOf (b : ℕ) (l : List ℕ) : ℕ := l.foldl (fun b k ↦ b ||| 2 ^ k) b

theorem testBit_bitsOf : ∀ (l : List ℕ) (b i : ℕ), (bitsOf b l).testBit i = true ↔ b.testBit i = true ∨ i ∈ l
  | [], b, i => by simp [bitsOf]
  | k :: l, b, i => by
    rw [bitsOf, List.foldl_cons, ← bitsOf, testBit_bitsOf l, Nat.testBit_or, Nat.testBit_two_pow]
    simp only [Bool.or_eq_true, decide_eq_true_eq, List.mem_cons]
    constructor
    · rintro ((h | rfl) | h) <;> simp [*]
    · rintro (h | rfl | h) <;> simp [*]

/-- The arms' callees, in increasing order. -/
def armRoots : List ℕ :=
  (List.range core_count%).filter (bitsOf 0 (armIdxs.flatMap Data.calleesJ)).testBit

theorem mem_armRoots {j k : ℕ} (hj : j ∈ armIdxs) (hk : k ∈ Data.calleesJ j) (hn : k < coreProgram.length) :
    k ∈ armRoots := by
  rw [coreProgram_length] at hn
  refine List.mem_filter.mpr ⟨List.mem_range.mpr hn, (testBit_bitsOf _ 0 k).mpr (.inr ?_)⟩
  exact List.mem_flatMap.mpr ⟨j, hj, hk⟩

/-- **An arm's callee is a root.** -/
theorem calleeIdx_root {j k : ℕ} {g : String} (hj : j ∈ armIdxs) (h : calleeIdx j g = some k) :
    k ∈ armRoots ∧ Data.nameT.find k = some g := by
  have hs := calleeIdx_spec h
  have hn : k < coreProgram.length := by
    by_contra hc
    rw [List.getElem?_eq_none (Nat.le_of_not_lt hc)] at hs
    exact absurd hs (by simp)
  unfold calleeIdx calleeIdxE at h
  have hname := Data.nameT_find hn
  rw [List.getElem?_eq_getElem hn, Option.map_some, Option.some.injEq] at hs
  exact ⟨mem_armRoots hj (List.mem_of_find?_eq_some h) hn, hname.trans (congrArg some hs)⟩

/-- `l` in chunks of `n`, at most `f` of them. -/
def chunks {α : Type} (n : ℕ) : ℕ → List α → List (List α)
  | 0, _ => []
  | f + 1, l => l.take n :: chunks n f (l.drop n)

theorem chunks_getElem? {α : Type} {n : ℕ} (hn : 0 < n) :
    ∀ (f : ℕ) (l : List α) (k : ℕ), l.length ≤ n * f → ((chunks n f l)[k / n]?).bind (·[k % n]?) = l[k]?
  | 0, l, k, h => by
    obtain rfl : l = [] := List.eq_nil_of_length_eq_zero (by simpa using h)
    simp [chunks]
  | f + 1, l, k, h => by
    by_cases hk : k < n
    · rw [Nat.div_eq_of_lt hk, Nat.mod_eq_of_lt hk]
      simp [chunks, hk]
    · have e : k / n = (k - n) / n + 1 := by
        rw [← Nat.sub_add_cancel (Nat.le_of_not_lt hk), Nat.add_div_right _ hn, Nat.sub_add_cancel (Nat.le_of_not_lt hk)]
      have e' : k % n = (k - n) % n := by
        conv_lhs => rw [← Nat.sub_add_cancel (Nat.le_of_not_lt hk)]
        exact Nat.add_mod_right _ _
      rw [chunks, e, List.getElem?_cons_succ, e', chunks_getElem? hn f (l.drop n) (k - n)
        (by rw [List.length_drop, Nat.mul_succ] at *; omega), List.getElem?_drop,
        Nat.add_sub_cancel' (Nat.le_of_not_lt hk)]

/-- Function `j` of the core IR, by its chunk of `32`: the kernel walks some `j / 32 + 32` cells where
`coreProgram[j]?` walks `j`. -/
noncomputable def coreAt (j : ℕ) : Option Fn :=
  ((chunks 32 (core_count% / 32 + 1) coreProgram)[j / 32]?).bind (·[j % 32]?)

theorem coreAt_eq (j : ℕ) : coreAt j = coreProgram[j]? :=
  chunks_getElem? (by decide) _ _ _ (by rw [coreProgram_length]; omega)

/-- Group `i` of the roots: seventy from `70 * i`, or with `last` every one from there. -/
def armGrp (i : ℕ) (last : Bool := false) : List ℕ :=
  bif last then armRoots.drop (70 * i) else (armRoots.drop (70 * i)).take 70

/-- A property of a list's members from its chunk at `n * k` and the rest after it. -/
theorem forall_drop_chunk {α : Type} {P : α → Prop} {l : List α} {n k : ℕ}
    (hc : ∀ x ∈ (l.drop (n * k)).take n, P x) (ht : ∀ x ∈ l.drop (n * (k + 1)), P x) :
    ∀ x ∈ l.drop (n * k), P x := by
  intro x hx
  rw [← List.take_append_drop n (l.drop (n * k)), List.mem_append, List.drop_drop] at hx
  rw [Nat.mul_succ] at ht
  exact hx.elim (hc x) (ht x)

/-- **Every root, from the six groups.** -/
theorem armRoots_all {P : ℕ → Prop} (h0 : ∀ k ∈ armGrp 0, P k) (h1 : ∀ k ∈ armGrp 1, P k)
    (h2 : ∀ k ∈ armGrp 2, P k) (h3 : ∀ k ∈ armGrp 3, P k) (h4 : ∀ k ∈ armGrp 4, P k)
    (h5 : ∀ k ∈ armGrp 5 true, P k) : ∀ k ∈ armRoots, P k := by
  dsimp only [armGrp, Bool.cond_false, Bool.cond_true] at h0 h1 h2 h3 h4 h5
  have := forall_drop_chunk (l := armRoots) (n := 70) (k := 0) h0 (forall_drop_chunk (k := 1) h1 (forall_drop_chunk (k := 2) h2
    (forall_drop_chunk (k := 3) h3 (forall_drop_chunk (k := 4) h4 h5))))
  rwa [Nat.mul_zero, List.drop_zero] at this

/-- The depth-first walk from `k`, `fuel` calls deep: the functions not in the bit set `acc.2` under `k`, listed
before `acc.1` with each caller before its callees. -/
def postAux : ℕ → List ℕ × ℕ → ℕ → List ℕ × ℕ
  | 0, acc, _ => acc
  | fuel + 1, acc, k =>
    if acc.2.testBit k then acc
    else
      let a := (Data.calleesJ k).foldl (fun a k' ↦ if k' == k then a else postAux fuel a k') (acc.1, acc.2 ||| 2 ^ k)
      (k :: a.1, a.2)

/-- The functions under the roots `L`, each callee but a self-call before its caller. -/
def postOrder (L : List ℕ) : List ℕ := (L.foldl (postAux 32) ([], 0)).1.reverse

/-- `k` joins the bit set `G` when it passes `loc` and its callees but itself are in `G`. -/
def goodStep (loc : ℕ → Bool) (G k : ℕ) : ℕ :=
  if G.testBit k then G
  else if loc k && (Data.calleesJ k).all (fun k' ↦ k' == k || G.testBit k') then G ||| 2 ^ k else G

/-- **Group `i`'s check**: each of its roots is collected by the pass of `loc` over the group's order, or
passes `ex`. -/
noncomputable def armGrpOk (loc ex : ℕ → Bool) (i : ℕ) (last : Bool := false) : Bool :=
  let G := (postOrder (armGrp i last)).foldl (goodStep loc) 0
  (armGrp i last).all fun k ↦ G.testBit k || ex k

theorem J_succ {J : ℕ → ℕ → Bool} {loc : ℕ → Bool} (h0 : ∀ j, J 0 j = false)
    (hJ : ∀ d j, J (d + 1) j = (loc j && (Data.calleesJ j).all fun k ↦ k == j || J d k)) :
    ∀ {d j : ℕ}, J d j = true → J (d + 1) j = true
  | 0, j, h => by rw [h0] at h; cases h
  | d + 1, j, h => by
    rw [hJ] at h ⊢
    simp only [Bool.and_eq_true, List.all_eq_true, Bool.or_eq_true] at h ⊢
    exact ⟨h.1, fun k hk ↦ (h.2 k hk).imp id (J_succ h0 hJ)⟩

theorem goodStep_sound {J : ℕ → ℕ → Bool} {loc : ℕ → Bool} (h0 : ∀ j, J 0 j = false)
    (hJ : ∀ d j, J (d + 1) j = (loc j && (Data.calleesJ j).all fun k ↦ k == j || J d k)) {G d : ℕ}
    (hG : ∀ k, G.testBit k = true → J d k = true) (k : ℕ) :
    ∀ k', (goodStep loc G k).testBit k' = true → J (d + 1) k' = true := by
  intro k' h
  unfold goodStep at h
  split_ifs at h with h1 h2
  · exact J_succ h0 hJ (hG k' h)
  · rw [Nat.testBit_or, Nat.testBit_two_pow, Bool.or_eq_true, decide_eq_true_eq] at h
    rcases h with h | rfl
    · exact J_succ h0 hJ (hG k' h)
    · rw [hJ]
      simp only [Bool.and_eq_true, List.all_eq_true, Bool.or_eq_true] at h2 ⊢
      exact ⟨h2.1, fun x hx ↦ (h2.2 x hx).imp id (hG x)⟩
  · exact J_succ h0 hJ (hG k' h)

/-- **Every function the pass collects passes `J`**, at a depth the list's length bounds. -/
theorem goodFold {J : ℕ → ℕ → Bool} {loc : ℕ → Bool} (h0 : ∀ j, J 0 j = false)
    (hJ : ∀ d j, J (d + 1) j = (loc j && (Data.calleesJ j).all fun k ↦ k == j || J d k)) :
    ∀ (L : List ℕ) {G d : ℕ}, (∀ k, G.testBit k = true → J d k = true) →
      ∀ k, (L.foldl (goodStep loc) G).testBit k = true → J (d + L.length) k = true
  | [], _, _, hG => hG
  | k :: L, _, d, hG => fun k' h ↦ by
    have := goodFold h0 hJ L (goodStep_sound h0 hJ hG k) k' h
    rwa [Nat.add_assoc, Nat.add_comm 1] at this

/-- **Group `i`'s check gives each of its roots `ex` or `J` at some depth.** -/
theorem armGrpOk_sound {J : ℕ → ℕ → Bool} {loc : ℕ → Bool} (h0 : ∀ j, J 0 j = false)
    (hJ : ∀ d j, J (d + 1) j = (loc j && (Data.calleesJ j).all fun k ↦ k == j || J d k)) {ex : ℕ → Bool}
    {i : ℕ} {last : Bool} (h : armGrpOk loc ex i last = true) :
    ∀ k ∈ armGrp i last, ex k = true ∨ ∃ d, J d k = true := by
  intro k hk
  unfold armGrpOk at h
  rcases Bool.or_eq_true _ _ ▸ List.all_eq_true.mp h k hk with h | h
  · exact .inr ⟨_, goodFold h0 hJ _ (d := 0) (by simp) k h⟩
  · exact .inl h

end
end LeanVM.Guest.B1.Arm
