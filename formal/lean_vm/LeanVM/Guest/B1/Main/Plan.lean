/-
  LeanVM.Guest.B1.Main.Plan

  The honest coverage plan (`Hints.coveragePlan`): every claim made takes one slot, the slot holds that
  claim, no slot is taken twice, and, when every declared claim is made as often as it is
  declared (`Limits`), every slot is taken.
-/

module

public import LeanVM.Guest.Limits
public import LeanVM.Guest.AcceptableChild

/-!
# The coverage plan

`Hints.coveragePlan D R Cs` assigns the claims made, the raw ones `R` then each child's `Cs[c]`, slots
in the table `D ++ dups`: a claim takes the first free declared index holding it, else a new
duplicate slot. With `made := R ++ Cs.flatten` and `slots` the slots in taking order:

* `plan_length`, `plan_lt`, `plan_claim`, `plan_nodup`: one slot per claim, inside the table, the
  table's entry there the claim, no slot twice;
* `plan_cover`: if every claim is made at least as often as it is declared, every slot of the
  table is taken (`plan_perm`: the slots are a permutation of the table's indices, whose number
  is the number of claims made);
* `plan_children`: the per-child segments of the slots;
* the two regions of a node under `DeployedLimits` (`xPlan_*`, `sPlan_*`), `planSlots` as the
  two tables' sizes (`coverage_eq`), the number of claims made (`coverage_made`), so
  `coverageSlots` (`planSlots_eq`), and the raw signatures within their regions (`xRaw_le`,
  `sRaw_le`).
-/

namespace LeanVM.Guest.B1.Main

open LeanVM.Node LeanVM.Guest LeanVM.Guest.Hints LeanVM.Guest.Coverage LeanVM.Parameters

@[expose] public section

section Generic

variable {α : Type} [BEq α] [LawfulBEq α]

/-! ## Indices holding a value -/

/-- The indices below `D.length` where `D` holds `x`. -/
def idxOf (D : List α) (x : α) : List ℕ := (List.range D.length).filter fun j ↦ D[j]? == some x

theorem filter_range_succ (p : ℕ → Bool) (n : ℕ) :
    ((List.range (n + 1)).filter p).length =
      (if p 0 then 1 else 0) + ((List.range n).filter fun j ↦ p (j + 1)).length := by
  rw [List.range_succ_eq_map, List.filter_cons, List.filter_map]
  split <;> simp [Function.comp_def]; omega

theorem length_idxOf (D : List α) (x : α) : (idxOf D x).length = D.count x := by
  induction D with
  | nil => simp [idxOf]
  | cons d D ih =>
    rw [idxOf, List.length_cons, filter_range_succ, List.count_cons, ← ih, idxOf]
    simp only [List.getElem?_cons_zero, List.getElem?_cons_succ]
    by_cases h : d = x
    · subst h; simp; omega
    · have : (some d == some x) = false := by simpa using h
      simp [this, beq_iff_eq, h]

/-! ## The taking invariant -/

/-- The state of the plan after the claims `done` took the slots `is`: the declared indices taken
are those of `is`, the table's entry at each slot is its claim, the duplicates' slots all taken,
and of every value, `min (D.count x) (done.count x)` declared indices taken. -/
structure Inv (D : List α) (st : List Bool × List α) (done : List α) (is : List ℕ) : Prop where
  len : st.1.length = D.length
  ilen : is.length = done.length
  claim : ∀ k (hk : k < is.length), (D ++ st.2)[is[k]]? = some (done[k]'(ilen ▸ hk))
  nodup : is.Nodup
  bits : ∀ j < D.length, st.1.getD j false = true ↔ j ∈ is
  lt : ∀ i ∈ is, i < D.length + st.2.length
  dups : ∀ m < st.2.length, D.length + m ∈ is
  taken : ∀ x, ((idxOf D x).filter fun j ↦ st.1.getD j false).length = min (D.count x) (done.count x)

theorem filter_split (l : List ℕ) (b : ℕ → Bool) :
    l.length = (l.filter b).length + (l.filter fun j ↦ !b j).length := by
  rw [List.length_eq_countP_add_countP b, List.countP_eq_length_filter,
    List.countP_eq_length_filter]
  simp

theorem getD_set_self (bs : List Bool) {j : ℕ} (hj : j < bs.length) : (bs.set j true).getD j false = true := by
  simp [List.getD_eq_getElem?_getD, hj]

theorem getD_set_ne (bs : List Bool) {i j : ℕ} (h : i ≠ j) :
    (bs.set j true).getD i false = bs.getD i false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_set_ne (Ne.symm h)]

omit [LawfulBEq α] in
theorem inv_nil (D : List α) : Inv D (D.map fun _ ↦ false, []) [] [] where
  len := by simp
  ilen := rfl
  claim := fun k hk => absurd hk (by simp)
  nodup := List.nodup_nil
  bits := fun j hj => by simp [List.getD_eq_getElem?_getD, hj]
  lt := fun i hi => absurd hi (by simp)
  dups := fun m hm => absurd hm (by simp)
  taken := fun x => by
    simp only [List.count_nil, Nat.min_zero, List.length_eq_zero_iff, List.filter_eq_nil_iff]
    intro j _
    by_cases hj : j < D.length <;> simp [List.getD_eq_getElem?_getD, hj]

theorem idxOf_mem {D : List α} {x : α} {j : ℕ} : j ∈ idxOf D x ↔ j < D.length ∧ D[j]? = some x := by
  simp [idxOf]

theorem filter_or_eq {l : List ℕ} (hl : l.Nodup) {j : ℕ} (hj : j ∈ l) {b : ℕ → Bool}
    (hb : b j = false) :
    (l.filter fun a ↦ b a || decide (a = j)).length = (l.filter b).length + 1 := by
  induction l with
  | nil => exact absurd hj List.not_mem_nil
  | cons a l ih =>
    obtain ⟨ha, hl'⟩ := List.nodup_cons.mp hl
    by_cases haj : a = j
    · subst haj
      have e : (l.filter fun a' ↦ b a' || decide (a' = a)) = l.filter b :=
        List.filter_congr fun a' ha' => by
          have : a' ≠ a := fun h => ha (h ▸ ha')
          simp [this]
      simp [hb, e]
    · have hj' : j ∈ l := (List.mem_cons.mp hj).resolve_left (Ne.symm haj)
      have := ih hl' hj'
      by_cases hba : b a = true
      · simp [hba, this]
      · simp only [Bool.not_eq_true] at hba
        simp [hba, haj, this]

omit [LawfulBEq α] in
theorem nodup_idxOf (D : List α) (x : α) : (idxOf D x).Nodup := List.nodup_range.filter _

/-- **One claim's slot preserves the invariant.** -/
theorem inv_step {D : List α} {st : List Bool × List α} {done : List α} {is : List ℕ} (c : α)
    (h : Inv D st done is) :
    Inv D (takeSlot D st c).2 (done ++ [c]) (is ++ [(takeSlot D st c).1]) := by
  have hbits : ∀ j < D.length, st.1.getD j true = st.1.getD j false := fun j hj => by
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem (by rw [h.len]; exact hj)]
    rfl
  unfold takeSlot
  split
  · rename_i j hj
    have hp := List.find?_some hj
    have hjn : j < D.length := List.mem_range.mp (List.mem_of_find?_eq_some hj)
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at hp
    obtain ⟨hDj, hfree⟩ := hp
    have hDj' : D[j]? = some c := by simpa using hDj
    rw [hbits j hjn] at hfree
    have hji : j ∉ is := fun hm => by
      have := (h.bits j hjn).mpr hm
      rw [this] at hfree
      exact absurd hfree (by simp)
    refine ⟨by simp [h.len], by simp [h.ilen], fun k hk => ?_, ?_, fun i hi => ?_, fun i hi => ?_,
      fun m hm => ?_, fun x => ?_⟩
    · simp only [List.length_append, List.length_singleton] at hk
      rcases Nat.lt_or_ge k is.length with hk' | hk'
      · rw [List.getElem_append_left hk', List.getElem_append_left (by rw [← h.ilen]; exact hk')]
        exact h.claim k hk'
      · have : k = is.length := by omega
        subst this
        rw [show (is ++ [j])[is.length]'(by simp) = j by simp, List.getElem?_append_left hjn, hDj']
        simp [h.ilen]
    · exact List.nodup_append.mpr ⟨h.nodup, List.nodup_singleton _, fun a ha b hb => by
        rw [List.mem_singleton] at hb; subst hb; rintro rfl; exact hji ha⟩
    · by_cases hij : i = j
      · subst hij; rw [getD_set_self _ (by rw [h.len]; exact hjn)]; simp
      · rw [getD_set_ne _ hij, h.bits i hi]; simp [hij]
    · rcases List.mem_append.mp hi with hi | hi
      · exact h.lt i hi
      · rw [List.mem_singleton] at hi; subst hi; omega
    · exact List.mem_append_left _ (h.dups m hm)
    · have e : ((idxOf D x).filter fun j' ↦ (st.1.set j true).getD j' false) =
          ((idxOf D x).filter fun j' ↦ st.1.getD j' false || decide (j' = j)) := by
        refine List.filter_congr fun j' _ => ?_
        by_cases hj' : j' = j
        · subst hj'; rw [getD_set_self _ (by rw [h.len]; exact hjn)]; simp
        · rw [getD_set_ne _ hj']; simp [hj']
      rw [e, List.count_append, List.count_singleton]
      by_cases hcx : c = x
      · subst hcx
        have hjmem : j ∈ idxOf D c := idxOf_mem.mpr ⟨hjn, hDj'⟩
        have hjfree : j ∈ (idxOf D c).filter fun j' ↦ !st.1.getD j' false :=
          List.mem_filter.mpr ⟨hjmem, by rw [hfree]; rfl⟩
        have hsplit := filter_split (idxOf D c) fun j ↦ st.1.getD j false
        have hpos := List.length_pos_of_mem hjfree
        rw [length_idxOf] at hsplit
        rw [filter_or_eq (nodup_idxOf D c) hjmem hfree, h.taken c]
        have := h.taken c
        simp only [beq_self_eq_true, ↓reduceIte]
        omega
      · have e2 : ((idxOf D x).filter fun j' ↦ st.1.getD j' false || decide (j' = j)) =
            ((idxOf D x).filter fun j' ↦ st.1.getD j' false) := by
          refine List.filter_congr fun j' hj' => ?_
          have hj'x := (idxOf_mem.mp hj').2
          have : j' ≠ j := by rintro rfl; rw [hDj'] at hj'x; exact hcx (Option.some.inj hj'x)
          simp [this]
        rw [e2, h.taken x]
        have : (c == x) = false := by simpa using hcx
        simp [this]
  · rename_i hnone
    have hall : ∀ j < D.length, D[j]? = some c → st.1.getD j false = true := by
      intro j hj hD
      have := List.find?_eq_none.mp hnone j (List.mem_range.mpr hj)
      rw [hbits j hj] at this
      simpa [hD] using this
    refine ⟨h.len, by simp [h.ilen], fun k hk => ?_, ?_, fun j hj => ?_,
      fun i hi => ?_, fun m hm => ?_, fun x => ?_⟩
    · simp only [List.length_append, List.length_singleton] at hk
      rcases Nat.lt_or_ge k is.length with hk' | hk'
      · rw [List.getElem_append_left hk', List.getElem_append_left (by rw [← h.ilen]; exact hk'),
          ← List.append_assoc, List.getElem?_append_left (by
            have := h.lt _ (List.getElem_mem hk'); simp; omega)]
        exact h.claim k hk'
      · have : k = is.length := by omega
        subst this
        rw [show (is ++ [D.length + st.2.length])[is.length]'(by simp) = D.length + st.2.length by
          simp, ← List.append_assoc, List.getElem?_append_right (by simp)]
        simp [h.ilen]
    · refine List.nodup_append.mpr ⟨h.nodup, List.nodup_singleton _, fun a ha b hb => ?_⟩
      rw [List.mem_singleton] at hb; subst hb
      have := h.lt a ha; omega
    · rw [h.bits j hj]
      constructor
      · exact fun h' => List.mem_append_left _ h'
      · intro h'
        rcases List.mem_append.mp h' with h' | h'
        · exact h'
        · rw [List.mem_singleton] at h'; omega
    · rcases List.mem_append.mp hi with hi | hi
      · have := h.lt i hi; simp; omega
      · rw [List.mem_singleton] at hi; subst hi; simp
    · simp only [List.length_append, List.length_singleton] at hm
      rcases Nat.lt_or_ge m st.2.length with hm' | hm'
      · exact List.mem_append_left _ (h.dups m hm')
      · have : m = st.2.length := by omega
        subst this; simp
    · rw [h.taken x, List.count_append, List.count_singleton]
      by_cases hcx : c = x
      · subst hcx
        have hsplit := filter_split (idxOf D c) fun j ↦ st.1.getD j false
        rw [length_idxOf] at hsplit
        have h0 : ((idxOf D c).filter fun j ↦ !st.1.getD j false).length = 0 := by
          rw [List.length_eq_zero_iff, List.filter_eq_nil_iff]
          intro j hj
          obtain ⟨hjn, hD⟩ := idxOf_mem.mp hj
          rw [hall j hjn hD]; decide
        have := h.taken c
        simp only [beq_self_eq_true, ↓reduceIte]
        omega
      · have : (c == x) = false := by simpa using hcx
        simp [this]

/-! ## The fold -/

omit [LawfulBEq α] in
theorem takeSlots_cons (D : List α) (st : List Bool × List α) (c : α) (cs : List α) :
    takeSlots D st (c :: cs) = ((takeSlot D st c).1 :: (takeSlots D (takeSlot D st c).2 cs).1,
      (takeSlots D (takeSlot D st c).2 cs).2) := by
  rcases h1 : takeSlot D st c with ⟨i, st'⟩
  rcases h2 : takeSlots D st' cs with ⟨is, st''⟩
  simp [takeSlots, h1, h2]

omit [LawfulBEq α] in
theorem takeSlots_length (D : List α) : ∀ (cs : List α) (st : List Bool × List α),
    (takeSlots D st cs).1.length = cs.length
  | [], _ => rfl
  | c :: cs, st => by rw [takeSlots_cons]; simp [takeSlots_length D cs]

omit [LawfulBEq α] in
theorem takeSlots_append (D : List α) : ∀ (a b : List α) (st : List Bool × List α),
    takeSlots D st (a ++ b) = ((takeSlots D st a).1 ++ (takeSlots D (takeSlots D st a).2 b).1,
      (takeSlots D (takeSlots D st a).2 b).2)
  | [], b, st => by simp [takeSlots]
  | c :: a, b, st => by
    rw [List.cons_append, takeSlots_cons, takeSlots_cons, takeSlots_append D a b]
    simp

omit [LawfulBEq α] in
theorem takeSlotsAll_cons (D : List α) (st : List Bool × List α) (c : List α) (cs : List (List α)) :
    takeSlotsAll D st (c :: cs) = ((takeSlots D st c).1 :: (takeSlotsAll D (takeSlots D st c).2 cs).1,
      (takeSlotsAll D (takeSlots D st c).2 cs).2) := by
  rcases h1 : takeSlots D st c with ⟨i, st'⟩
  rcases h2 : takeSlotsAll D st' cs with ⟨is, st''⟩
  simp [takeSlotsAll, h1, h2]

omit [LawfulBEq α] in
/-- **Taking lists of claims is taking their concatenation**, segment by segment. -/
theorem takeSlotsAll_eq (D : List α) : ∀ (cs : List (List α)) (st : List Bool × List α),
    (takeSlotsAll D st cs).1.flatten = (takeSlots D st cs.flatten).1 ∧
      (takeSlotsAll D st cs).2 = (takeSlots D st cs.flatten).2 ∧
      (takeSlotsAll D st cs).1.map List.length = cs.map List.length
  | [], st => by simp [takeSlotsAll, takeSlots]
  | c :: cs, st => by
    obtain ⟨h1, h2, h3⟩ := takeSlotsAll_eq D cs (takeSlots D st c).2
    rw [takeSlotsAll_cons]
    simp only [List.flatten_cons, takeSlots_append]
    simp [h1, h2, h3, takeSlots_length]

/-- The invariant along a list of claims. -/
theorem inv_takeSlots {D : List α} : ∀ (cs : List α) {st : List Bool × List α} {done : List α}
    {is : List ℕ}, Inv D st done is →
      Inv D (takeSlots D st cs).2 (done ++ cs) (is ++ (takeSlots D st cs).1)
  | [], _, _, _, h => by simpa [takeSlots] using h
  | c :: cs, st, done, is, h => by
    have := inv_takeSlots cs (inv_step c h)
    rw [takeSlots_cons]
    simpa using this

/-! ## The plan -/

/-- The plan's initial state. -/
def st0 (D : List α) : List Bool × List α := (D.map fun _ ↦ false, [])

/-- The claims made, raw then the children's. -/
def made (R : List α) (Cs : List (List α)) : List α := R ++ Cs.flatten

/-- The slots taken, in taking order. -/
def slotsOf (p : CoverageRegion α) : List ℕ := p.directSlots ++ p.childSlots.flatten

omit [LawfulBEq α] in
theorem plan_parts (D R : List α) (Cs : List (List α)) :
    (coveragePlan D R Cs).directSlots = (takeSlots D (st0 D) R).1 ∧
      (coveragePlan D R Cs).childSlots = (takeSlotsAll D (takeSlots D (st0 D) R).2 Cs).1 ∧
      (coveragePlan D R Cs).duplicates = (takeSlotsAll D (takeSlots D (st0 D) R).2 Cs).2.2 := by
  exact ⟨rfl, rfl, rfl⟩

omit [LawfulBEq α] in
theorem plan_slots (D R : List α) (Cs : List (List α)) :
    slotsOf (coveragePlan D R Cs) = (takeSlots D (st0 D) (made R Cs)).1 ∧
      (coveragePlan D R Cs).duplicates = (takeSlots D (st0 D) (made R Cs)).2.2 := by
  obtain ⟨h1, h2, h3⟩ := plan_parts D R Cs
  obtain ⟨e1, e2, -⟩ := takeSlotsAll_eq D Cs (takeSlots D (st0 D) R).2
  rw [slotsOf, made, takeSlots_append, h1, h2, h3, e1, e2]
  exact ⟨rfl, rfl⟩

/-- **The plan's invariant**: the claims made, at their slots in `D ++ dups`. -/
theorem plan_inv (D R : List α) (Cs : List (List α)) :
    Inv D ((takeSlots D (st0 D) (made R Cs)).2) (made R Cs) (slotsOf (coveragePlan D R Cs)) := by
  rw [(plan_slots D R Cs).1]
  have := inv_takeSlots (made R Cs) (inv_nil D)
  simp only [List.nil_append] at this
  exact this

omit [LawfulBEq α] in
theorem plan_dups_eq (D R : List α) (Cs : List (List α)) :
    (takeSlots D (st0 D) (made R Cs)).2.2 = (coveragePlan D R Cs).duplicates := (plan_slots D R Cs).2.symm

/-- **One slot per claim made.** -/
theorem plan_length (D R : List α) (Cs : List (List α)) :
    (slotsOf (coveragePlan D R Cs)).length = (made R Cs).length := (plan_inv D R Cs).ilen

/-- **Every slot is in the table.** -/
theorem plan_lt (D R : List α) (Cs : List (List α)) :
    ∀ i ∈ slotsOf (coveragePlan D R Cs), i < (D ++ (coveragePlan D R Cs).duplicates).length := by
  intro i hi
  have := (plan_inv D R Cs).lt i hi
  rw [plan_dups_eq] at this
  simpa using this

/-- **The table holds each claim at its slot.** -/
theorem plan_claim (D R : List α) (Cs : List (List α)) (k : ℕ)
    (hk : k < (slotsOf (coveragePlan D R Cs)).length) :
    (D ++ (coveragePlan D R Cs).duplicates)[(slotsOf (coveragePlan D R Cs))[k]]? =
      some ((made R Cs)[k]'(plan_length D R Cs ▸ hk)) := by
  have := (plan_inv D R Cs).claim k hk
  rwa [plan_dups_eq] at this

/-- **No slot is taken twice.** -/
theorem plan_nodup (D R : List α) (Cs : List (List α)) : (slotsOf (coveragePlan D R Cs)).Nodup :=
  (plan_inv D R Cs).nodup

/-- **Every slot is taken**, when every declared claim is made as often as it is declared. -/
theorem plan_cover (D R : List α) (Cs : List (List α))
    (hc : ∀ x, D.count x ≤ (made R Cs).count x) :
    ∀ t < (D ++ (coveragePlan D R Cs).duplicates).length, t ∈ slotsOf (coveragePlan D R Cs) := by
  have h := plan_inv D R Cs
  intro t ht
  rw [List.length_append] at ht
  rcases Nat.lt_or_ge t D.length with htn | htn
  · obtain ⟨x, hx⟩ : ∃ x, D[t]? = some x := ⟨D[t], List.getElem?_eq_getElem htn⟩
    have htk := h.taken x
    rw [Nat.min_eq_left (hc x), ← length_idxOf] at htk
    have hall := List.length_filter_eq_length_iff.mp htk
    exact (h.bits t htn).mp (hall t (idxOf_mem.mpr ⟨htn, hx⟩))
  · have := h.dups (t - D.length) (by rw [plan_dups_eq]; omega)
    rwa [Nat.add_sub_cancel' htn] at this

/-- **The slots are the table's indices**, each once. -/
theorem plan_perm (D R : List α) (Cs : List (List α))
    (hc : ∀ x, D.count x ≤ (made R Cs).count x) :
    (slotsOf (coveragePlan D R Cs)).Perm (List.range (D ++ (coveragePlan D R Cs).duplicates).length) :=
  (List.perm_ext_iff_of_nodup (plan_nodup D R Cs) List.nodup_range).mpr fun t =>
    ⟨fun ht => List.mem_range.mpr (plan_lt D R Cs t ht),
      fun ht => plan_cover D R Cs hc t (List.mem_range.mp ht)⟩

/-- **The table has one slot per claim made.** -/
theorem plan_table_length (D R : List α) (Cs : List (List α))
    (hc : ∀ x, D.count x ≤ (made R Cs).count x) :
    (D ++ (coveragePlan D R Cs).duplicates).length = (made R Cs).length := by
  rw [← plan_length, (plan_perm D R Cs hc).length_eq, List.length_range]

/-! ## The segments -/

omit [BEq α] [LawfulBEq α] in
theorem getElem_flatten_sum {β : Type} : ∀ (L : List (List β)) (c k : ℕ) (hc : c < L.length)
    (hk : k < (L[c]).length),
    ∃ h, (L.flatten)[((L.take c).map List.length).sum + k]'h = (L[c])[k]
  | [], c, _, hc, _ => absurd hc (by simp)
  | l :: L, 0, k, _, hk => by
    have hk' : k < l.length := hk
    refine ⟨by simp only [List.flatten_cons, List.length_append]; simp; omega, ?_⟩
    simp only [List.take_zero, List.map_nil, List.sum_nil, Nat.zero_add, List.flatten_cons]
    exact List.getElem_append_left hk'
  | l :: L, c + 1, k, hc, hk => by
    obtain ⟨h, e⟩ := getElem_flatten_sum L c k (by simpa using hc) (by simpa using hk)
    refine ⟨by
      have := h
      simp only [List.take_succ_cons, List.map_cons, List.sum_cons, List.flatten_cons,
        List.length_append] at this ⊢
      omega, ?_⟩
    simp only [List.take_succ_cons, List.map_cons, List.sum_cons, List.flatten_cons,
      List.getElem_cons_succ]
    rw [List.getElem_append_right (by omega)]
    simp only [show l.length + ((L.take c).map List.length).sum + k - l.length =
      ((L.take c).map List.length).sum + k by omega]
    exact e

omit [LawfulBEq α] in
theorem plan_raw_length (D R : List α) (Cs : List (List α)) : (coveragePlan D R Cs).directSlots.length = R.length := by
  rw [(plan_parts D R Cs).1, takeSlots_length]

omit [LawfulBEq α] in
theorem plan_children_lengths (D R : List α) (Cs : List (List α)) :
    (coveragePlan D R Cs).childSlots.map List.length = Cs.map List.length := by
  rw [(plan_parts D R Cs).2.1]
  exact (takeSlotsAll_eq D Cs _).2.2

/-- Where child `c`'s claims start among the slots and the claims made. -/
def base (R : List α) (Cs : List (List α)) (c : ℕ) : ℕ :=
  R.length + ((Cs.take c).map List.length).sum

/-- **Child `c`'s claim `k`**: its slot is the plan's, and the table holds it there. -/
theorem plan_child (D R : List α) (Cs : List (List α)) {c k : ℕ} (hc : c < Cs.length)
    (hk : k < (Cs[c]).length) :
    ∃ (hc' : c < (coveragePlan D R Cs).childSlots.length) (hk' : k < ((coveragePlan D R Cs).childSlots[c]).length)
      (hs : base R Cs c + k < (slotsOf (coveragePlan D R Cs)).length),
      (slotsOf (coveragePlan D R Cs))[base R Cs c + k] = ((coveragePlan D R Cs).childSlots[c])[k] ∧
      (D ++ (coveragePlan D R Cs).duplicates)[((coveragePlan D R Cs).childSlots[c])[k]]? = some ((Cs[c])[k]) := by
  have hl := plan_children_lengths D R Cs
  have hlen : (coveragePlan D R Cs).childSlots.length = Cs.length := by
    simpa using congrArg List.length hl
  have hc' : c < (coveragePlan D R Cs).childSlots.length := by omega
  have hlc : ((coveragePlan D R Cs).childSlots[c]).length = (Cs[c]).length := by
    have := congrArg (·[c]?) hl
    simpa [List.getElem?_map, hc, hc'] using this
  have hk' : k < ((coveragePlan D R Cs).childSlots[c]).length := by omega
  have htake : ((coveragePlan D R Cs).childSlots.take c).map List.length = (Cs.take c).map List.length := by
    rw [List.map_take, hl, ← List.map_take]
  obtain ⟨hf, ef⟩ := getElem_flatten_sum (coveragePlan D R Cs).childSlots c k hc' hk'
  obtain ⟨hf2, ef2⟩ := getElem_flatten_sum Cs c k hc hk
  have hraw := plan_raw_length D R Cs
  have hs : base R Cs c + k < (slotsOf (coveragePlan D R Cs)).length := by
    rw [slotsOf, List.length_append, hraw]; rw [htake] at hf; unfold base; omega
  refine ⟨hc', hk', hs, ?_, ?_⟩
  · have : (slotsOf (coveragePlan D R Cs))[base R Cs c + k] =
        ((coveragePlan D R Cs).childSlots.flatten)[((((coveragePlan D R Cs).childSlots.take c).map List.length).sum + k)]'hf := by
      simp only [slotsOf, base]
      rw [List.getElem_append_right (by rw [hraw]; omega)]
      simp only [hraw, htake]
      congr 1; omega
    rw [this, ef]
  · have hm : (made R Cs)[base R Cs c + k]'(plan_length D R Cs ▸ hs) = (Cs[c])[k] := by
      simp only [made, base]
      rw [List.getElem_append_right (by omega)]
      simp only [show R.length + ((Cs.take c).map List.length).sum + k - R.length =
        ((Cs.take c).map List.length).sum + k by omega]
      exact ef2
    have := plan_claim D R Cs (base R Cs c + k) hs
    rw [hm] at this
    have e : (slotsOf (coveragePlan D R Cs))[base R Cs c + k] = ((coveragePlan D R Cs).childSlots[c])[k] := by
      have : (slotsOf (coveragePlan D R Cs))[base R Cs c + k] =
          ((coveragePlan D R Cs).childSlots.flatten)[((((coveragePlan D R Cs).childSlots.take c).map List.length).sum + k)]'hf := by
        simp only [slotsOf, base]
        rw [List.getElem_append_right (by rw [hraw]; omega)]
        simp only [hraw, htake]
        congr 1; omega
      rw [this, ef]
    rwa [e] at this

/-- **The raw claim `k`**: its slot is the plan's, and the table holds it there. -/
theorem plan_raw (D R : List α) (Cs : List (List α)) {k : ℕ} (hk : k < R.length) :
    ∃ (hk' : k < (coveragePlan D R Cs).directSlots.length) (hs : k < (slotsOf (coveragePlan D R Cs)).length),
      (slotsOf (coveragePlan D R Cs))[k] = (coveragePlan D R Cs).directSlots[k] ∧
      (D ++ (coveragePlan D R Cs).duplicates)[(coveragePlan D R Cs).directSlots[k]]? = some R[k] := by
  have hraw := plan_raw_length D R Cs
  have hk' : k < (coveragePlan D R Cs).directSlots.length := by omega
  have hs : k < (slotsOf (coveragePlan D R Cs)).length := by rw [slotsOf, List.length_append]; omega
  have e : (slotsOf (coveragePlan D R Cs))[k] = (coveragePlan D R Cs).directSlots[k] := by
    simp only [slotsOf]; rw [List.getElem_append_left hk']
  refine ⟨hk', hs, e, ?_⟩
  have := plan_claim D R Cs k hs
  rw [e] at this
  rw [this]
  simp only [made]
  rw [List.getElem_append_left hk]

end Generic

/-! ## A node's two regions -/

section Node

variable (s : NodeStatement) (w : NodeWitness)

/-- The leanXMSS region's plan, as `honestPushes` makes it. -/
def xPlan : CoverageRegion LeanXmssClaim :=
  coveragePlan s.claims.xmss (w.xmssSignatures.map (·.1)) (w.children.map (·.statement.claims.xmss))

/-- The leanSPHINCS region's plan. -/
def sPlan : CoverageRegion LeanSphincsClaim :=
  coveragePlan s.claims.sphincs (w.sphincsSignatures.map (·.1))
    (w.children.map (·.statement.claims.sphincs))

/-- **The coverage table's slots** are the two regions' tables'. -/
theorem coverage_eq : planSlots s w = (s.claims.xmss ++ (xPlan s w).duplicates).length +
    (s.claims.sphincs ++ (sPlan s w).duplicates).length := by
  simp only [planSlots, xPlan, sPlan, List.length_append]
  omega

theorem made_count {α : Type} [BEq α] {R : List α} {Cs : List (List α)} (x : α) :
    (made R Cs).count x = R.count x + (Cs.map fun c ↦ c.count x).sum := by
  simp [made, List.count_append, List.count_flatten]

variable {bytecode : List K} {s w}

theorem xPlan_held (hl : DeployedLimits s w) : ∀ x, s.claims.xmss.count x ≤
    (made (w.xmssSignatures.map (·.1)) (w.children.map (·.statement.claims.xmss))).count x :=
  fun x => by rw [made_count, List.map_map]; exact hl.xmssClaimsHeldWithMultiplicity x

theorem sPlan_held (hl : DeployedLimits s w) : ∀ x, s.claims.sphincs.count x ≤
    (made (w.sphincsSignatures.map (·.1))
      (w.children.map (·.statement.claims.sphincs))).count x :=
  fun x => by rw [made_count, List.map_map]; exact hl.sphincsClaimsHeldWithMultiplicity x

/-- **Under `Limits`, the coverage table has one slot per claim made**, raw or by a child. -/
theorem coverage_made (hl : DeployedLimits s w) : planSlots s w =
    (made (w.xmssSignatures.map (·.1)) (w.children.map (·.statement.claims.xmss))).length +
    (made (w.sphincsSignatures.map (·.1))
      (w.children.map (·.statement.claims.sphincs))).length := by
  rw [coverage_eq, xPlan, sPlan, plan_table_length _ _ _ (xPlan_held hl),
    plan_table_length _ _ _ (sPlan_held hl)]

/-- **Under `DeployedLimits`, the honest run's coverage table is `coverageSlots`**: one slot per
claim made. -/
theorem planSlots_eq (hl : DeployedLimits s w) : planSlots s w = coverageSlots w := by
  rw [coverage_made hl]
  simp only [made, coverageSlots, List.length_append, List.length_map, List.length_flatten,
    List.map_map, List.sum_map_add]
  simp only [Function.comp_def]
  omega

/-- The honest run's coverage table below `2^16`. -/
theorem _root_.LeanVM.Guest.DeployedLimits.planSlotsBelow2Pow16 (hl : DeployedLimits s w) :
    planSlots s w < 2 ^ 16 := by
  rw [planSlots_eq hl]; exact hl.coverageSlotsBelow2Pow16

/-- **The raw leanXMSS signatures are at most the leanXMSS region's slots.** -/
theorem xRaw_le (hl : DeployedLimits s w) :
    w.xmssSignatures.length ≤ s.claims.xmss.length + (xPlan s w).duplicates.length := by
  have h := plan_table_length s.claims.xmss (w.xmssSignatures.map (·.1))
    (w.children.map (·.statement.claims.xmss)) (xPlan_held hl)
  simp only [List.length_append, made, List.length_map] at h
  simp only [xPlan]
  omega

/-- **The raw leanSPHINCS signatures are at most the leanSPHINCS region's slots.** -/
theorem sRaw_le (hl : DeployedLimits s w) :
    w.sphincsSignatures.length ≤ s.claims.sphincs.length + (sPlan s w).duplicates.length := by
  have h := plan_table_length s.claims.sphincs (w.sphincsSignatures.map (·.1))
    (w.children.map (·.statement.claims.sphincs)) (sPlan_held hl)
  simp only [List.length_append, made, List.length_map] at h
  simp only [sPlan]
  omega

end Node

end
end LeanVM.Guest.B1.Main
