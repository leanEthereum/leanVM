/-
  LeanVM.Guest.B1.VerifySub.GroupOrder

  Sorting entries by their `stackOffsets` offsets gives `stackOffsets`' order, and for entries in consecutive groups of one size each, the groups' run heads of that order are the groups sorted as `stackOffsets` sorts them.
-/

module

public import LeanVM.Guest.Hints
public import LeanVM.Guest.B1.Tables.GroupCert

/-!
# Group orders

* `runHeads_flatMap_replicate`: each of distinct neighbours repeated is kept once;
* `mergeSort_off`: the entries sorted by their offsets are `stackOffsets`' order (`mergeSort` of a permutation is its unique sorted form, the offsets strictly increase along `stackOffsets`' order, `tb_stackOffsets_sum`);
* `mergeSort_groups`: on groups of consecutive entries of one size, `stackOffsets`' order is the groups' order, each group's entries in place;
* `runHeads_sortOff`: the run heads of the entries' groups, sorted by offset, are the groups' `stackOffsets` order.
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Guest.Value LeanVM.Protocol.Verifier LeanVM.Guest.B1.Tables

@[expose] public section

/-! ## Run heads -/

theorem runHeads_cons_cons_self (a : ℕ) (l : List ℕ) :
    Hints.runHeads (a :: a :: l) = Hints.runHeads (a :: l) := by
  simp [Hints.runHeads]

theorem runHeads_cons_of_head (a : ℕ) : ∀ (l : List ℕ), l.head? ≠ some a →
    Hints.runHeads (a :: l) = a :: Hints.runHeads l
  | [], _ => rfl
  | b :: l, h => by
    rw [Hints.runHeads]
    split
    · next e => exact absurd (by rw [e]; rfl) h
    · rfl

theorem runHeads_replicate_append (a : ℕ) (l : List ℕ) (h : l.head? ≠ some a) :
    ∀ k, Hints.runHeads (List.replicate (k + 1) a ++ l) = a :: Hints.runHeads l
  | 0 => runHeads_cons_of_head a l h
  | k + 1 => by
    show Hints.runHeads (a :: a :: (List.replicate k a ++ l)) = _
    rw [runHeads_cons_cons_self]
    exact runHeads_replicate_append a l h k

/-- **Distinct neighbours, each repeated, are kept once.** -/
theorem runHeads_flatMap_replicate (c : ℕ → ℕ) : ∀ (l : List ℕ), l.Pairwise (· ≠ ·) →
    (∀ a ∈ l, 1 ≤ c a) → Hints.runHeads (l.flatMap fun a => List.replicate (c a) a) = l
  | [], _, _ => rfl
  | a :: l, hp, hc => by
    obtain ⟨hne, hp⟩ := List.pairwise_cons.mp hp
    have hc' : ∀ b ∈ l, 1 ≤ c b := fun b hb => hc b (List.mem_cons_of_mem _ hb)
    have hh : (l.flatMap fun a => List.replicate (c a) a).head? ≠ some a := by
      cases l with
      | nil => simp
      | cons b l' =>
        obtain ⟨k, hk⟩ : ∃ k, c b = k + 1 := ⟨c b - 1, by have := hc' b List.mem_cons_self; omega⟩
        rw [List.flatMap_cons, hk, List.replicate_succ, List.cons_append, List.head?_cons]
        exact fun e => hne b List.mem_cons_self (Option.some.inj e).symm
    obtain ⟨k, hk⟩ : ∃ k, c a = k + 1 := ⟨c a - 1, by have := hc a List.mem_cons_self; omega⟩
    rw [List.flatMap_cons, hk, runHeads_replicate_append a _ hh k, runHeads_flatMap_replicate c l hp hc']

/-! ## Sorting by offset -/

section
variable (κs : List ℕ)

theorem tbPrec_trans {a b c : ℕ} (h1 : tbPrec κs a b) (h2 : tbPrec κs b c) : tbPrec κs a c := by
  unfold tbPrec at *; omega

/-- **Offsets strictly increase along `stackOffsets`' order.** -/
theorem off_lt {x y : ℕ} (hx : x < κs.length) (hy : y < κs.length) (h : tbPrec κs y x) :
    (stackOffsets κs).1.getD y 0 < (stackOffsets κs).1.getD x 0 := by
  rw [tb_stackOffsets_sum κs hx, tb_stackOffsets_sum κs hy]
  refine Finset.sum_lt_sum_of_subset (i := y) (fun z hz => ?_) ?_ ?_ (Nat.two_pow_pos _) fun _ _ _ => Nat.zero_le _
  · simp only [Finset.mem_filter, Finset.mem_range] at hz ⊢
    exact ⟨hz.1, tbPrec_trans κs hz.2 h⟩
  · simp only [Finset.mem_filter, Finset.mem_range]
    exact ⟨hy, h⟩
  · intro hm
    rw [Finset.mem_filter] at hm
    unfold tbPrec at hm
    omega

/-- **The entries sorted by their offsets are `stackOffsets`' order.** -/
theorem mergeSort_off (f : ℕ → ℕ) (hf : ∀ i < κs.length, f i = (stackOffsets κs).1.getD i 0) :
    (List.range κs.length).mergeSort (fun i j => decide (f i ≤ f j)) =
      (List.range κs.length).mergeSort (stackLe (κs.getD · 0)) := by
  have p1 := List.mergeSort_perm (List.range κs.length) (fun i j => decide (f i ≤ f j))
  have p2 := List.mergeSort_perm (List.range κs.length) (stackLe (κs.getD · 0))
  have hm1 : ∀ a ∈ (List.range κs.length).mergeSort (fun i j => decide (f i ≤ f j)), a < κs.length :=
    fun a ha => List.mem_range.mp (p1.subset ha)
  have hm2 : ∀ a ∈ (List.range κs.length).mergeSort (stackLe (κs.getD · 0)), a < κs.length :=
    fun a ha => List.mem_range.mp (p2.subset ha)
  apply List.Perm.eq_of_pairwise (le := fun a b => f a ≤ f b)
  · intro a b ha hb h1 h2
    have ha' := hm1 a ha
    have hb' := hm2 b hb
    by_contra hne
    have ht : tbPrec κs a b ∨ tbPrec κs b a := by unfold tbPrec; omega
    rw [hf a ha', hf b hb'] at h1 h2
    rcases ht with ht | ht
    · have := off_lt κs hb' ha' ht; omega
    · have := off_lt κs ha' hb' ht; omega
  · exact (List.pairwise_mergeSort (fun a b c (h1 : decide _ = true) (h2 : decide _ = true) => by
        simp only [decide_eq_true_eq] at h1 h2 ⊢; omega)
      (fun a b => by simp only [Bool.or_eq_true, decide_eq_true_eq]; omega) _).imp
      fun h => of_decide_eq_true h
  · have hs := List.pairwise_mergeSort (le := stackLe (κs.getD · 0))
      (fun a b c => by simp only [stackLe, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]; omega)
      (fun a b => by simp only [stackLe, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]; omega)
      (List.range κs.length)
    have hnd : ((List.range κs.length).mergeSort (stackLe (κs.getD · 0))).Pairwise (· ≠ ·) :=
      p2.nodup_iff.mpr List.nodup_range
    refine (hs.and hnd).imp_of_mem fun {a b} ha hb ⟨h, hne⟩ => ?_
    have ha' := hm2 a ha
    have hb' := hm2 b hb
    have hp : tbPrec κs a b := by
      simp only [stackLe, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
      unfold tbPrec; omega
    have := off_lt κs hb' ha' hp
    rw [hf a ha', hf b hb']
    omega
  · exact p1.trans p2.symm

/-! ## Groups -/

variable {m : ℕ} (st kg : ℕ → ℕ)

theorem st_le_of (hmono : ∀ j < m, st j < st (j + 1)) {a b : ℕ} (hab : a ≤ b) (hb : b ≤ m) :
    st a ≤ st b := by
  induction b with
  | zero => rw [Nat.le_zero.mp hab]
  | succ b ih =>
    rcases Nat.eq_or_lt_of_le hab with rfl | h
    · exact le_rfl
    · exact (ih (by omega) (by omega)).trans (hmono b (by omega)).le

theorem flatMap_range_groups (hmono : ∀ j < m, st j < st (j + 1)) :
    ∀ k ≤ m, (List.range k).flatMap (fun j => List.range' (st j) (st (j + 1) - st j)) =
      List.range' (st 0) (st k - st 0)
  | 0, _ => by simp
  | k + 1, hk => by
    rw [List.range_succ, List.flatMap_append, flatMap_range_groups hmono k (by omega), List.flatMap_singleton]
    have h0 := st_le_of st hmono (Nat.zero_le k) (by omega)
    have h1 := hmono k (by omega)
    rw [show st (k + 1) - st 0 = (st k - st 0) + (st (k + 1) - st k) by omega, ← List.range'_append_1,
      show st 0 + (st k - st 0) = st k by omega]

/-- **On groups of consecutive entries of one size, `stackOffsets`' order is the groups' order**, each
group's entries in place. -/
theorem mergeSort_groups (hst0 : st 0 = 0) (hstm : st m = κs.length) (hmono : ∀ j < m, st j < st (j + 1))
    (hκ : ∀ j < m, ∀ x, st j ≤ x → x < st (j + 1) → κs.getD x 0 = kg j) :
    (List.range κs.length).mergeSort (stackLe (κs.getD · 0)) =
      ((List.range m).mergeSort (stackLe kg)).flatMap fun j => List.range' (st j) (st (j + 1) - st j) := by
  have pG := List.mergeSort_perm (List.range m) (stackLe kg)
  have hmG : ∀ j ∈ (List.range m).mergeSort (stackLe kg), j < m := fun j hj => List.mem_range.mp (pG.subset hj)
  have hin : ∀ j < m, ∀ x ∈ List.range' (st j) (st (j + 1) - st j), st j ≤ x ∧ x < st (j + 1) := by
    intro j hj x hx
    rw [List.mem_range'_1] at hx
    have := hmono j hj
    omega
  apply List.Perm.eq_of_pairwise (le := fun a b => stackLe (κs.getD · 0) a b = true)
  · intro a b _ _ h1 h2
    simp only [stackLe, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h1 h2
    omega
  · exact List.pairwise_mergeSort
      (fun a b c => by simp only [stackLe, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]; omega)
      (fun a b => by simp only [stackLe, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]; omega) _
  · rw [List.pairwise_flatMap]
    refine ⟨fun j hj => ?_, ?_⟩
    · refine (List.pairwise_lt_range' (s := st j) (n := st (j + 1) - st j)).imp_of_mem
        fun {x y} hx hy (hxy : x < y) => ?_
      obtain ⟨hx1, hx2⟩ := hin j (hmG j hj) x hx
      obtain ⟨hy1, hy2⟩ := hin j (hmG j hj) y hy
      have e1 := hκ j (hmG j hj) x hx1 hx2
      have e2 := hκ j (hmG j hj) y hy1 hy2
      simp only [stackLe, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]
      omega
    · have hs := List.pairwise_mergeSort (le := stackLe kg)
        (fun a b c => by simp only [stackLe, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]; omega)
        (fun a b => by simp only [stackLe, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]; omega)
        (List.range m)
      have hnd : ((List.range m).mergeSort (stackLe kg)).Pairwise (· ≠ ·) := pG.nodup_iff.mpr List.nodup_range
      refine (hs.and hnd).imp_of_mem fun {a b} ha hb ⟨h, hne⟩ x hx y hy => ?_
      have ha' := hmG a ha
      have hb' := hmG b hb
      obtain ⟨hx1, hx2⟩ := hin a ha' x hx
      obtain ⟨hy1, hy2⟩ := hin b hb' y hy
      have e1 := hκ a ha' x hx1 hx2
      have e2 := hκ b hb' y hy1 hy2
      simp only [stackLe, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
      simp only [stackLe, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]
      rcases h with h | ⟨h1, h2⟩
      · omega
      · have := st_le_of st hmono (show a + 1 ≤ b by omega) hb'.le
        omega
  · refine (List.mergeSort_perm _ _).trans ((List.Perm.flatMap_right _ pG).trans ?_).symm
    rw [flatMap_range_groups st hmono m le_rfl, hst0, hstm, Nat.sub_zero, ← List.range_eq_range']

/-- **The run heads of the entries' groups, sorted by offset, are the groups in `stackOffsets`' order**, the
groups numbered from `c`. -/
theorem runHeads_sortOff (c : ℕ) (grp f : ℕ → ℕ) (hst0 : st 0 = 0) (hstm : st m = κs.length)
    (hmono : ∀ j < m, st j < st (j + 1))
    (hκ : ∀ j < m, ∀ x, st j ≤ x → x < st (j + 1) → κs.getD x 0 = kg j)
    (hgrp : ∀ j < m, ∀ x, st j ≤ x → x < st (j + 1) → grp x = c + j)
    (hf : ∀ i < κs.length, f i = (stackOffsets κs).1.getD i 0) :
    Hints.runHeads (((List.range κs.length).mergeSort fun i j => decide (f i ≤ f j)).map grp) =
      ((List.range m).mergeSort (stackLe kg)).map (c + ·) := by
  have pG := List.mergeSort_perm (List.range m) (stackLe kg)
  have hmG : ∀ j ∈ (List.range m).mergeSort (stackLe kg), j < m := fun j hj => List.mem_range.mp (pG.subset hj)
  rw [mergeSort_off κs f hf, mergeSort_groups κs st kg hst0 hstm hmono hκ, List.map_flatMap]
  have e : ∀ j ∈ (List.range m).mergeSort (stackLe kg),
      (List.range' (st j) (st (j + 1) - st j)).map grp =
        (fun a => List.replicate (st (a - c + 1) - st (a - c)) a) (c + j) := by
    intro j hj
    simp only [Nat.add_sub_cancel_left]
    refine List.eq_replicate_iff.mpr ⟨by simp, fun x hx => ?_⟩
    obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
    rw [List.mem_range'_1] at hy
    exact hgrp j (hmG j hj) y hy.1 (by omega)
  rw [List.flatMap_congr e, ← List.flatMap_map (f := (c + ·))
    (g := fun a => List.replicate (st (a - c + 1) - st (a - c)) a)]
  refine runHeads_flatMap_replicate (fun a => st (a - c + 1) - st (a - c)) _ ?_ fun a ha => ?_
  · exact List.pairwise_map.mpr ((pG.nodup_iff.mpr List.nodup_range).imp fun h e => h (by omega))
  · obtain ⟨j, hj, rfl⟩ := List.mem_map.mp ha
    have := hmono j (hmG j hj)
    simp only [Nat.add_sub_cancel_left]
    omega

end

end
end LeanVM.Guest.B1.VerifySub
