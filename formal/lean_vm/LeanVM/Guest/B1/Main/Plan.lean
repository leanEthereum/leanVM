/-
  LeanVM.Guest.B1.Main.Plan

  The coverage plan of `main`'s completeness: every writer of a region takes a slot of its own,
  its declared slot while one is free, else the next duplicate slot; when every declared claim is
  written as often as it is declared, the slots are a permutation of the region.
-/

module

public import Mathlib.Data.List.Basic
public import Mathlib.Data.List.Count
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.List.Nodup
public import Mathlib.Data.List.GetD
public import Mathlib.Data.Finset.Range
public import LeanVM.Guest.Hints

/-!
# Slots

`assign D W` gives each writer of `W`, in order, a slot of the region `D ++ U`: the first declared
position of its claim still free (`pick`), or a new duplicate, appended to `U`. Every slot holds
its writer's claim (`assign_entry`), no two writers share a slot (`assign_nodup`), and when every
claim is written at least as often as it is declared (`∀ x, D.count x ≤ W.count x`), every slot of
the region is taken (`assign_cover`), so `|W| = |D| + |U|` (`assign_length_total`).
-/

namespace LeanVM.Guest.B1.Main

@[expose] public section

variable {α : Type} [DecidableEq α]

/-- The first declared position of `x` not taken. -/
def pick (D : List α) (taken : List ℕ) (x : α) : Option ℕ :=
  (List.range D.length).find? fun j => decide (D[j]? = some x ∧ j ∉ taken)

/-- The slots of the writers `W` from the taken positions and the duplicates so far, and the final
duplicates. -/
def assign (D : List α) : List ℕ → List α → List α → List ℕ × List α
  | _, dups, [] => ([], dups)
  | taken, dups, x :: W =>
    match pick D taken x with
    | some j => ((j :: (assign D (j :: taken) dups W).1), (assign D (j :: taken) dups W).2)
    | none => ((D.length + dups.length) :: (assign D taken (dups ++ [x]) W).1,
        (assign D taken (dups ++ [x]) W).2)

theorem pick_some {D : List α} {taken : List ℕ} {x : α} {j : ℕ} (h : pick D taken x = some j) :
    j < D.length ∧ D[j]? = some x ∧ j ∉ taken := by
  have h1 := List.find?_some h
  have h2 := List.mem_of_find?_eq_some h
  simp only [decide_eq_true_eq] at h1
  exact ⟨List.mem_range.mp h2, h1⟩

theorem pick_none {D : List α} {taken : List ℕ} {x : α} (h : pick D taken x = none) :
    ∀ j < D.length, D[j]? = some x → j ∈ taken := by
  intro j hj hx
  have := List.find?_eq_none.mp h j (List.mem_range.mpr hj)
  simp only [decide_eq_true_eq, not_and, not_not] at this
  exact this hx

/-- **What `assign` gives**, from any taken declared positions and duplicates: a slot per writer,
the duplicates extended, every slot holding its writer's claim, no slot twice nor among the taken,
each slot declared or a new duplicate, every new duplicate's slot taken, and no writer of a claim
whose declared position stays free made a duplicate. -/
theorem assign_spec (D : List α) : ∀ (W : List α) (taken : List ℕ) (dups : List α),
    (∀ t ∈ taken, t < D.length) → taken.Nodup →
    (assign D taken dups W).1.length = W.length ∧
    (∃ U', (assign D taken dups W).2 = dups ++ U') ∧
    (∀ i < W.length, (D ++ (assign D taken dups W).2)[(assign D taken dups W).1.getD i 0]? = W[i]?) ∧
    ((assign D taken dups W).1 ++ taken).Nodup ∧
    (∀ s ∈ (assign D taken dups W).1, s < D.length ∨
      (D.length + dups.length ≤ s ∧ s < D.length + (assign D taken dups W).2.length)) ∧
    (∀ k, dups.length ≤ k → k < (assign D taken dups W).2.length →
      D.length + k ∈ (assign D taken dups W).1) ∧
    (∀ j < D.length, j ∉ (assign D taken dups W).1 → j ∉ taken → ∀ i < W.length,
      D.length ≤ (assign D taken dups W).1.getD i 0 → D[j]? ≠ W[i]?)
  | [], taken, dups, _, ht => by
    refine ⟨rfl, ⟨[], by simp [assign]⟩, fun i hi => absurd hi (by simp), by simpa [assign] using ht,
      fun s hs => by simp [assign] at hs, fun k h1 h2 => by simp [assign] at h2; omega,
      fun _ _ _ _ i hi => absurd hi (by simp)⟩
  | x :: W, taken, dups, hlt, ht => by
    cases hp : pick D taken x with
    | some j =>
      obtain ⟨hj, hjx, hjt⟩ := pick_some hp
      obtain ⟨i1, i2, i3, i4, i5, i6, i7⟩ := assign_spec D W (j :: taken) dups
        (fun t ht' => by rcases List.mem_cons.mp ht' with rfl | ht'; exacts [hj, hlt t ht'])
        (List.nodup_cons.mpr ⟨hjt, ht⟩)
      simp only [assign, hp]
      refine ⟨by simp [i1], i2, fun i hi => ?_, ?_, ?_, fun k h1 h2 => List.mem_cons_of_mem _ (i6 k h1 h2),
        fun j' hj' hn hnt i hi hge => ?_⟩
      · rcases i with _ | i
        · simp only [List.getD_cons_zero, List.getElem?_cons_zero]
          rw [List.getElem?_append_left hj, hjx]
        · simpa using i3 i (by simpa using hi)
      · rw [List.cons_append]
        exact (List.perm_middle.nodup_iff).mp i4
      · intro s hs
        rcases List.mem_cons.mp hs with rfl | hs
        · exact Or.inl hj
        · exact i5 s hs
      · rcases i with _ | i
        · simp only [List.getD_cons_zero] at hge; omega
        · have hj'ne : j' ≠ j := fun he => hn (he ▸ List.mem_cons_self)
          exact by
            simpa using i7 j' hj' (fun h => hn (List.mem_cons_of_mem _ h))
              (fun h => (List.mem_cons.mp h).elim hj'ne hnt) i (by simpa using hi)
              (by simpa using hge)
    | none =>
      have hall := pick_none hp
      obtain ⟨i1, ⟨U', i2⟩, i3, i4, i5, i6, i7⟩ := assign_spec D W taken (dups ++ [x]) hlt ht
      simp only [assign, hp]
      have hs0 : D.length + dups.length ∉ (assign D taken (dups ++ [x]) W).1 ++ taken := by
        intro h
        rcases List.mem_append.mp h with h | h
        · rcases i5 _ h with h' | ⟨h', -⟩
          · omega
          · simp only [List.length_append, List.length_singleton] at h'; omega
        · have := hlt _ h; omega
      refine ⟨by simp [i1], ⟨[x] ++ U', by rw [i2, List.append_assoc]⟩, fun i hi => ?_, ?_, ?_,
        fun k h1 h2 => ?_, fun j hj hn hnt i hi hge => ?_⟩
      · rcases i with _ | i
        · simp only [List.getD_cons_zero, List.getElem?_cons_zero]
          rw [List.getElem?_append_right (by omega), i2]
          simp
        · simpa using i3 i (by simpa using hi)
      · rw [List.cons_append]
        exact List.nodup_cons.mpr ⟨hs0, i4⟩
      · intro s hs
        rcases List.mem_cons.mp hs with rfl | hs
        · refine Or.inr ⟨le_rfl, ?_⟩
          rw [i2]; simp
        · rcases i5 s hs with h | ⟨h1, h2⟩
          · exact Or.inl h
          · exact Or.inr ⟨by simp at h1; omega, h2⟩
      · rcases Nat.lt_or_ge k (dups.length + 1) with hk | hk
        · rw [show k = dups.length by omega]; exact List.mem_cons_self
        · exact List.mem_cons_of_mem _ (i6 k (by simpa using hk) h2)
      · rcases i with _ | i
        · simp only [List.getElem?_cons_zero]
          intro he
          exact hnt (hall j hj he)
        · simpa using i7 j hj (fun h => hn (List.mem_cons_of_mem _ h)) hnt i (by simpa using hi)
            (by simpa using hge)

theorem count_eq_length_filter_range (x : α) : ∀ l : List α,
    l.count x = ((List.range l.length).filter fun k => decide (l[k]? = some x)).length
  | [] => rfl
  | a :: l => by
    rw [List.length_cons, List.range_succ_eq_map, List.filter_cons, List.count_cons,
      count_eq_length_filter_range x l, List.filter_map]
    by_cases h : a = x <;> simp [h, Function.comp_def]

theorem card_filter_range (x : α) (l : List α) :
    ((Finset.range l.length).filter fun k => l[k]? = some x).card = l.count x := by
  have e : (Finset.range l.length).filter (fun k => l[k]? = some x) =
      ((List.range l.length).filter fun k => decide (l[k]? = some x)).toFinset := by
    ext k; simp [List.mem_range]
  rw [e, List.toFinset_card_of_nodup ((List.nodup_range).filter _), count_eq_length_filter_range]

/-- **Every declared slot is taken** when every claim is written as often as it is declared. -/
theorem assign_cover {D W : List α} (hc : ∀ x, D.count x ≤ W.count x) :
    ∀ j < D.length, j ∈ (assign D [] [] W).1 := by
  intro j hj
  by_contra hn
  obtain ⟨i1, -, i3, i4, -, -, i7⟩ := assign_spec D W [] [] (by simp) List.nodup_nil
  rw [List.append_nil] at i4
  set S := (assign D [] [] W).1 with hS
  set x := D[j] with hx
  have hjx : D[j]? = some x := List.getElem?_eq_getElem hj
  have hmap : ∀ i ∈ (Finset.range W.length).filter (fun i => W[i]? = some x),
      S.getD i 0 ∈ ((Finset.range D.length).filter fun k => D[k]? = some x).erase j := by
    intro i hi
    simp only [Finset.mem_filter, Finset.mem_range] at hi
    have hlt : S.getD i 0 < D.length := by
      by_contra hge
      exact i7 j hj hn (by simp) i hi.1 (by omega) (by rw [hjx, hi.2])
    have he := i3 i hi.1
    rw [List.getElem?_append_left hlt, hi.2] at he
    have hmem : S.getD i 0 ∈ S := by
      rw [List.getD_eq_getElem _ _ (by omega)]; exact List.getElem_mem _
    simp only [Finset.mem_erase, Finset.mem_filter, Finset.mem_range]
    exact ⟨fun h => hn (h ▸ hmem), hlt, he⟩
  have hinj : Set.InjOn (fun i => S.getD i 0)
      ((Finset.range W.length).filter (fun i => W[i]? = some x) : Set ℕ) := by
    intro a ha b hb hab
    rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at ha hb
    simp only at hab
    rw [List.getD_eq_getElem _ _ (by omega), List.getD_eq_getElem _ _ (by omega)] at hab
    exact (List.Nodup.getElem_inj_iff i4).mp hab
  have hle := Finset.card_le_card_of_injOn _ hmap hinj
  rw [card_filter_range, Finset.card_erase_of_mem (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hj, hjx⟩),
    card_filter_range] at hle
  have h1 : 0 < D.count x := List.count_pos_iff.mpr (List.getElem_mem hj)
  have := hc x
  omega

/-- **The writers fill the region exactly**: one slot each, every slot of `D ++ U` once. -/
theorem assign_length_total {D W : List α} (hc : ∀ x, D.count x ≤ W.count x) :
    W.length = D.length + (assign D [] [] W).2.length := by
  obtain ⟨i1, -, -, i4, i5, i6, -⟩ := assign_spec D W [] [] (by simp) List.nodup_nil
  rw [List.append_nil] at i4
  have hcov := assign_cover hc
  have hset : (assign D [] [] W).1.toFinset = Finset.range (D.length + (assign D [] [] W).2.length) := by
    ext s
    simp only [List.mem_toFinset, Finset.mem_range]
    constructor
    · intro hs
      rcases i5 s hs with h | ⟨-, h⟩
      · omega
      · exact h
    · intro hs
      rcases Nat.lt_or_ge s D.length with h | h
      · exact hcov s h
      · have := i6 (s - D.length) (by simp) (by omega)
        rwa [show D.length + (s - D.length) = s by omega] at this
  have := congrArg Finset.card hset
  rw [List.toFinset_card_of_nodup i4, Finset.card_range, i1] at this
  exact this

/-! ## `Hints.plan` is `assign` -/

section Hints

open LeanVM.Guest.Hints

/-- The taken flags of the declared positions. -/
def flagsOf (D : List α) (taken : List ℕ) : List Bool :=
  (List.range D.length).map fun j => decide (j ∈ taken)

omit [DecidableEq α] in
theorem flagsOf_getD (D : List α) (taken : List ℕ) {j : ℕ} (hj : j < D.length) :
    (flagsOf D taken).getD j true = decide (j ∈ taken) := by
  simp [flagsOf, List.getD_eq_getElem?_getD, hj]

omit [DecidableEq α] in
theorem flagsOf_set (D : List α) (taken : List ℕ) (j : ℕ) :
    (flagsOf D taken).set j true = flagsOf D (j :: taken) := by
  apply List.ext_getElem (by simp [flagsOf])
  intro k h1 h2
  simp only [flagsOf, List.length_set, List.length_map, List.length_range] at h1
  rw [List.getElem_set]
  split_ifs with hk
  · subst hk; simp [flagsOf]
  · simp [flagsOf, Ne.symm hk]

variable [BEq α] [LawfulBEq α]

theorem takeSlot_eq (D : List α) (taken : List ℕ) (dups : List α) (x : α) :
    takeSlot D (flagsOf D taken, dups) x =
      match pick D taken x with
      | some j => (j, (flagsOf D (j :: taken), dups))
      | none => (D.length + dups.length, (flagsOf D taken, dups ++ [x])) := by
  have hf : (List.range D.length).find? (fun j => D[j]? == some x && !((flagsOf D taken).getD j true)) =
      pick D taken x := by
    unfold pick
    apply List.find?_congr
    intro j hj
    rw [flagsOf_getD D taken (List.mem_range.mp hj)]
    by_cases h1 : D[j]? = some x <;> by_cases h2 : j ∈ taken <;> simp [h1, h2]
  unfold takeSlot
  rw [hf]
  cases hp : pick D taken x with
  | none => rfl
  | some j => simp only [flagsOf_set D taken j]

/-- The taken positions after `assign`. -/
def assignTaken (D : List α) (taken : List ℕ) (dups : List α) (W : List α) : List ℕ :=
  (assign D taken dups W).1.filter (· < D.length) ++ taken

theorem takeSlots_eq (D : List α) : ∀ (W : List α) (taken : List ℕ) (dups : List α),
    takeSlots D (flagsOf D taken, dups) W = ((assign D taken dups W).1,
      (flagsOf D (assignTaken D taken dups W), (assign D taken dups W).2))
  | [], taken, dups => by simp [takeSlots, assign, assignTaken]
  | x :: W, taken, dups => by
    simp only [takeSlots, takeSlot_eq]
    cases hp : pick D taken x with
    | some j =>
      simp only [assign, hp, takeSlots_eq D W (j :: taken) dups]
      have hj := (pick_some hp).1
      congr 2
      unfold flagsOf assignTaken
      congr 1; funext k
      simp only [assign, hp, List.filter_cons, List.mem_append, List.mem_filter, List.mem_cons]
      by_cases hk : k = j <;> by_cases hk2 : k ∈ taken <;> simp [hk, hk2, hj]
    | none =>
      simp only [assign, hp, takeSlots_eq D W taken (dups ++ [x])]
      congr 2
      unfold flagsOf assignTaken
      congr 1; funext k
      simp only [assign, hp, List.filter_cons, List.mem_append, List.mem_filter]
      by_cases hk2 : k ∈ taken <;> simp [hk2]

omit [BEq α] [LawfulBEq α] in
theorem pick_congr {D : List α} {t1 t2 : List ℕ} (h : ∀ k, k ∈ t1 ↔ k ∈ t2) (x : α) :
    pick D t1 x = pick D t2 x := by
  unfold pick
  congr 1; funext j; simp [h j]

omit [BEq α] [LawfulBEq α] in
theorem assign_congr {D : List α} : ∀ (W : List α) {t1 t2 : List ℕ} (dups : List α),
    (∀ k, k ∈ t1 ↔ k ∈ t2) → assign D t1 dups W = assign D t2 dups W
  | [], _, _, _, _ => rfl
  | x :: W, t1, t2, dups, h => by
    simp only [assign, pick_congr h x]
    cases pick D t2 x with
    | some j =>
      simp only [assign_congr W dups (t1 := j :: t1) (t2 := j :: t2) (fun k => by simp [h k])]
    | none => simp only [assign_congr W (dups ++ [x]) h]

omit [DecidableEq α] [BEq α] [LawfulBEq α] in
theorem flagsOf_congr {D : List α} {t1 t2 : List ℕ} (h : ∀ k, k ∈ t1 ↔ k ∈ t2) :
    flagsOf D t1 = flagsOf D t2 := by
  unfold flagsOf; congr 1; funext j; simp [h j]

omit [BEq α] [LawfulBEq α] in
theorem assign_append (D : List α) : ∀ (W1 W2 : List α) (taken : List ℕ) (dups : List α),
    assign D taken dups (W1 ++ W2) =
      ((assign D taken dups W1).1 ++
        (assign D (assignTaken D taken dups W1) (assign D taken dups W1).2 W2).1,
        (assign D (assignTaken D taken dups W1) (assign D taken dups W1).2 W2).2)
  | [], W2, taken, dups => by simp [assign, assignTaken]
  | x :: W1, W2, taken, dups => by
    rw [List.cons_append]
    cases hp : pick D taken x with
    | some j =>
      have hj := (pick_some hp).1
      simp only [assign, hp, assign_append D W1 W2 (j :: taken) dups, List.cons_append]
      have e : ∀ k, k ∈ assignTaken D (j :: taken) dups W1 ↔
          k ∈ assignTaken D taken dups (x :: W1) := fun k => by
        simp only [assignTaken, assign, hp, List.filter_cons, List.mem_append, List.mem_filter,
          List.mem_cons]
        by_cases hk : k = j <;> simp [hk, hj]
      rw [assign_congr W2 _ e]
    | none =>
      simp only [assign, hp, assign_append D W1 W2 taken (dups ++ [x]), List.cons_append]
      have e : ∀ k, k ∈ assignTaken D taken (dups ++ [x]) W1 ↔
          k ∈ assignTaken D taken dups (x :: W1) := fun k => by
        simp only [assignTaken, assign, hp, List.filter_cons, List.mem_append, List.mem_filter]
        simp
      rw [assign_congr W2 _ e]

theorem takeSlotsAll_eq (D : List α) : ∀ (cs : List (List α)) (taken : List ℕ) (dups : List α),
    (takeSlotsAll D (flagsOf D taken, dups) cs).2 =
      (flagsOf D (assignTaken D taken dups cs.flatten), (assign D taken dups cs.flatten).2)
  | [], taken, dups => by simp [takeSlotsAll, assign, assignTaken]
  | c :: cs, taken, dups => by
    simp only [takeSlotsAll, takeSlots_eq, takeSlotsAll_eq D cs, List.flatten_cons, assign_append]
    refine Prod.ext (flagsOf_congr fun k => ?_) rfl
    simp only [assignTaken, assign_append, List.filter_append, List.mem_append]
    tauto

/-- **`Hints.plan`'s duplicates are `assign`'s** on the raw claims then the children's. -/
theorem plan_dups (D raw : List α) (children : List (List α)) :
    (plan D raw children).dups = (assign D [] [] (raw ++ children.flatten)).2 := by
  have h0 : D.map (fun _ => false) = flagsOf D [] := by
    apply List.ext_getElem (by simp [flagsOf]); intro k h1 h2; simp [flagsOf]
  have e := takeSlotsAll_eq D children (assignTaken D [] [] raw) (assign D [] [] raw).2
  simp only [plan, h0, takeSlots_eq]
  rw [e, assign_append]

end Hints

end
end LeanVM.Guest.B1.Main
