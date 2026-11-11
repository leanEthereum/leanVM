/-
  LeanVM.Guest.B1.Tables.GroupCert

  `stackOffsets` as a sum, and a hinted order of block groups strictly descending in its rank key
  placing every block at its `stackOffsets` offset.
-/

module

public import LeanVM.Guest.B1.Placement.Common

/-!
# Certification by groups (G:2121-2148, at 40f877dc)

`verify_tables` (and `certify_placement`) certify the native order (descending log-size, then
ascending index) by groups: runs of consecutive entries sharing one log-size, ordered by a hinted
permutation strictly descending in a rank key. `tb_stackOffsets_sum`: entry `x`'s `stackOffsets`
offset is the sum of the sizes of the entries before it in the order. `tb_group_offsets`: when the
key orders the groups as the native order does, a group's base is the sum of the groups' sizes
ranked before it and its entries following at their size's stride, every entry's offset is
`stackOffsets`'.
-/

namespace LeanVM.Guest.B1.Tables

open LeanVM.Guest.Value LeanVM.Protocol.Verifier
open Finset

@[expose] public section

/-- `stackOffsets`' strict order: a larger size first, ties by index. -/
def tbPrec (κs : List ℕ) (y x : ℕ) : Prop :=
  κs.getD x 0 < κs.getD y 0 ∨ (κs.getD y 0 = κs.getD x 0 ∧ y < x)

instance (κs : List ℕ) (y x : ℕ) : Decidable (tbPrec κs y x) := by unfold tbPrec; infer_instance

/-- **`stackOffsets`' offsets as sums**: entry `x`'s offset is the sum of the sizes of the entries
before it in the order. -/
theorem tb_stackOffsets_sum (κs : List ℕ) {x : ℕ} (hx : x < κs.length) :
    (stackOffsets κs).1.getD x 0 =
      ∑ y ∈ (range κs.length).filter (tbPrec κs · x), 2 ^ κs.getD y 0 := by
  set n := κs.length
  set size : ℕ → ℕ := (κs.getD · 0) with hsize
  set ord := (List.range n).mergeSort (stackLe size) with hord
  have hperm : ord.Perm (List.range n) := List.mergeSort_perm _ _
  have hnd : ord.Nodup := hperm.nodup_iff.mpr List.nodup_range
  have hlen : ord.length = n := by rw [hperm.length_eq, List.length_range]
  have htrans : ∀ a b c, stackLe size a b = true → stackLe size b c = true →
      stackLe size a c = true := by
    intro a b c hab hbc
    simp only [stackLe, Bool.or_eq_true, decide_eq_true_eq, Bool.and_eq_true] at *
    omega
  have htotal : ∀ a b, (stackLe size a b || stackLe size b a) = true := by
    intro a b
    simp only [stackLe, Bool.or_eq_true, decide_eq_true_eq, Bool.and_eq_true]
    omega
  have hsorted : ord.Pairwise fun a b ↦ stackLe size a b = true :=
    List.pairwise_mergeSort htrans htotal _
  have hmem : x ∈ ord := hperm.mem_iff.mpr (List.mem_range.mpr hx)
  obtain ⟨r, hr, hrx⟩ := List.getElem_of_mem hmem
  have hoff := tb_stackOffsets_fst κs r (by omega)
  rw [show ((List.range κs.length).mergeSort (stackLe (κs.getD · 0))).getD r 0 = x by
    rw [List.getD_eq_getElem _ _ hr]; exact hrx] at hoff
  rw [hoff, tbPrefixSize, ← List.sum_toFinset _ (hnd.sublist (List.take_sublist _ _))]
  refine Finset.sum_congr ?_ fun _ _ ↦ rfl
  ext y
  simp only [List.mem_toFinset, Finset.mem_filter, Finset.mem_range]
  rw [List.pairwise_iff_getElem] at hsorted
  constructor
  · intro hy
    obtain ⟨i, hi, hiy⟩ := List.getElem_of_mem hy
    rw [List.length_take] at hi
    rw [List.getElem_take] at hiy
    have hil : i < ord.length := by omega
    have hyn : y < n := List.mem_range.mp (hperm.subset (hiy ▸ List.getElem_mem hil))
    have hne : y ≠ x := by
      intro he
      rw [← hiy, ← hrx] at he
      exact absurd ((List.Nodup.getElem_inj_iff hnd).mp he) (by omega)
    have := hsorted i r hil hr (by omega)
    rw [hiy, hrx] at this
    simp only [hsize, stackLe, Bool.or_eq_true, decide_eq_true_eq, Bool.and_eq_true] at this
    refine ⟨hyn, ?_⟩
    unfold tbPrec
    rcases this with h | ⟨h1, h2⟩
    · exact Or.inl h
    · exact Or.inr ⟨h1, by omega⟩
  · rintro ⟨hyn, hp⟩
    have hym : y ∈ ord := hperm.mem_iff.mpr (List.mem_range.mpr hyn)
    obtain ⟨i, hi, hiy⟩ := List.getElem_of_mem hym
    refine List.mem_iff_getElem.mpr ⟨i, ?_, ?_⟩
    · rw [List.length_take]
      refine lt_min ?_ hi
      rcases Nat.lt_trichotomy i r with h | h | h
      · exact h
      · subst h
        rw [hiy] at hrx
        subst hrx
        unfold tbPrec at hp
        omega
      · have := hsorted r i hr hi h
        rw [hiy, hrx] at this
        simp only [hsize, stackLe, Bool.or_eq_true, decide_eq_true_eq, Bool.and_eq_true] at this
        unfold tbPrec at hp
        omega
    · rw [List.getElem_take]; exact hiy

/-- **Certification by groups.** Entries `x < n` fall in groups `grp x < m`, group `j` the run
`st j ≤ x < st (j + 1)` of log-size `kg j`; `key` orders the groups as the native order does
(a larger size, ties by the lower first entry). A hinted order `o` of the `m` groups strictly
descending in `key` ranks `x`'s group some `r`; the sum of the sizes of the groups ranked before
`r`, plus `x`'s stride within its group, is `x`'s `stackOffsets` offset. -/
theorem tb_group_offsets {n m : ℕ} (κs : List ℕ) (hlen : κs.length = n)
    (st kg grp key o : ℕ → ℕ)
    (hgrp : ∀ x < n, grp x < m ∧ st (grp x) ≤ x ∧ x < st (grp x + 1))
    (hgrp' : ∀ j < m, ∀ x, st j ≤ x → x < st (j + 1) → x < n ∧ grp x = j)
    (hκ : ∀ x < n, κs.getD x 0 = kg (grp x))
    (hkey : ∀ a < m, ∀ b < m, key b < key a ↔ (kg b < kg a ∨ (kg a = kg b ∧ st a < st b)))
    (ho : ∀ r < m, o r < m) (hdec : ∀ r, r + 1 < m → key (o (r + 1)) < key (o r)) :
    ∀ x < n, ∃ r < m, o r = grp x ∧ (stackOffsets κs).1.getD x 0 =
      (∑ r' ∈ range r, (st (o r' + 1) - st (o r')) * 2 ^ kg (o r')) +
        (x - st (grp x)) * 2 ^ kg (grp x) := by
  -- the order is strictly descending in `key`, hence a bijection of the groups
  have hdec' : ∀ r r', r < r' → r' < m → key (o r') < key (o r) := by
    intro r r' hrr' hr'
    induction r' with
    | zero => omega
    | succ r' ih =>
      rcases Nat.lt_or_ge r r' with h | h
      · exact lt_trans (hdec r' hr') (ih h (by omega))
      · obtain rfl : r = r' := by omega
        exact hdec r hr'
  have hinj : ∀ r < m, ∀ r' < m, o r = o r' → r = r' := by
    intro r hr r' hr' he
    rcases Nat.lt_trichotomy r r' with h | h | h
    · have := hdec' r r' h hr'; rw [he] at this; omega
    · exact h
    · have := hdec' r' r h hr; rw [he] at this; omega
  have hsurj : ∀ j < m, ∃ r < m, o r = j := by
    let f : Fin m → Fin m := fun r ↦ ⟨o r, ho r r.2⟩
    have hfi : Function.Injective f := fun a b hab ↦
      Fin.ext (hinj a a.2 b b.2 (congrArg Fin.val hab))
    have hfb := (Fintype.bijective_iff_injective_and_card f).mpr ⟨hfi, rfl⟩
    intro j hj
    obtain ⟨r, hr⟩ := hfb.2 ⟨j, hj⟩
    exact ⟨r, r.2, congrArg Fin.val hr⟩
  have hkirr : ∀ a < m, ¬ key a < key a := fun a ha h ↦ by
    have := (hkey a ha a ha).mp h; omega
  intro x hx
  obtain ⟨hgx, hstx, hxst⟩ := hgrp x hx
  set j := grp x with hj
  obtain ⟨r, hr, hrj⟩ := hsurj j hgx
  -- the base: the groups of a larger key
  refine ⟨r, hr, hrj, ?_⟩
  have hB : (∑ r' ∈ range r, (st (o r' + 1) - st (o r')) * 2 ^ kg (o r')) =
      ∑ G ∈ (range m).filter (fun G ↦ key j < key G), (st (G + 1) - st G) * 2 ^ kg G := by
    rw [← hrj]
    have himg : (range r).image o = (range m).filter (fun G ↦ key (o r) < key G) := by
      ext G
      simp only [Finset.mem_image, Finset.mem_range, Finset.mem_filter]
      constructor
      · rintro ⟨r', hr', rfl⟩
        exact ⟨ho r' (by omega), hdec' r' r hr' hr⟩
      · rintro ⟨hG, hk⟩
        obtain ⟨r', hr', rfl⟩ := hsurj G hG
        refine ⟨r', ?_, rfl⟩
        rcases Nat.lt_trichotomy r' r with h | h | h
        · exact h
        · subst h; exact absurd hk (hkirr _ hG)
        · have := hdec' r r' h hr'; omega
    rw [← himg, Finset.sum_image fun a ha b hb he ↦
      hinj a (by simp at ha; omega) b (by simp at hb; omega) he]
  -- the order before `x`: the groups of a larger key, then `x`'s group below `x`
  have hsplit : (range κs.length).filter (tbPrec κs · x) =
      (range n).filter (fun y ↦ key j < key (grp y)) ∪ Finset.Ico (st j) x := by
    ext y
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_union, Finset.mem_Ico, hlen]
    constructor
    · rintro ⟨hy, hp⟩
      obtain ⟨hgy, hsty, hyst⟩ := hgrp y hy
      unfold tbPrec at hp
      rw [hκ x hx, hκ y hy, ← hj] at hp
      by_cases hyx : grp y = j
      · right
        rw [hyx] at hp hsty
        omega
      · left
        refine ⟨hy, (hkey _ hgy _ hgx).mpr ?_⟩
        rcases hp with h | ⟨h1, h2⟩
        · exact Or.inl h
        · right
          refine ⟨h1, ?_⟩
          -- distinct groups of one size: their runs are ordered as their entries
          by_contra hge
          have hle : st j ≤ st (grp y) := by omega
          rcases Nat.eq_or_lt_of_le hle with he | hlt
          · -- equal starts: the same group
            have := (hgrp' (grp y) hgy y hsty hyst).2
            have h2' := (hgrp' j hgx (st j) le_rfl (by have := (hgrp' j hgx x hstx hxst); omega)).2
            have h3 := (hgrp' (grp y) hgy (st (grp y)) le_rfl (by omega)).2
            rw [← he] at h3
            exact hyx (h3.symm.trans h2')
          · -- `j`'s run ends before `y`'s starts
            have hjend : st (j + 1) ≤ st (grp y) := by
              by_contra hc
              have := (hgrp' j hgx (st (grp y)) (by omega) (by omega)).2
              have h4 := (hgrp' (grp y) hgy (st (grp y)) le_rfl (by omega)).2
              exact hyx (h4.symm.trans this)
            omega
    · rintro (⟨hy, hk⟩ | ⟨h1, h2⟩)
      · refine ⟨hy, ?_⟩
        obtain ⟨hgy, hsty, hyst⟩ := hgrp y hy
        unfold tbPrec
        rw [hκ x hx, hκ y hy]
        rcases (hkey _ hgy _ hgx).mp hk with h | ⟨h1, h2⟩
        · exact Or.inl h
        · right
          refine ⟨h1, ?_⟩
          have hjend : st (grp y + 1) ≤ st j := by
            by_contra hc
            have := (hgrp' (grp y) hgy (st j) (by omega) (by omega)).2
            have h4 := (hgrp' j hgx (st j) le_rfl (by omega)).2
            have : grp y = j := this.symm.trans h4
            rw [this] at h2; omega
          omega
      · have hyn : y < n := by omega
        refine ⟨hyn, ?_⟩
        have hgy := (hgrp' j hgx y h1 (by omega)).2
        unfold tbPrec
        rw [hκ x hx, hκ y hyn, hgy]
        exact Or.inr ⟨rfl, h2⟩
  have hdisj : Disjoint ((range n).filter (fun y ↦ key j < key (grp y))) (Finset.Ico (st j) x) := by
    rw [Finset.disjoint_left]
    intro y hy hy'
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico] at hy hy'
    have := (hgrp' j hgx y hy'.1 (by omega)).2
    rw [this] at hy
    exact hkirr j hgx hy.2
  rw [tb_stackOffsets_sum κs (by omega), hsplit, Finset.sum_union hdisj, hB]
  congr 1
  · -- the groups of a larger key, entry by entry
    rw [← Finset.sum_fiberwise_of_maps_to (g := grp)
      (t := (range m).filter (fun G ↦ key j < key G)) (fun y hy ↦ by
        simp only [Finset.mem_filter, Finset.mem_range] at hy ⊢
        exact ⟨(hgrp y hy.1).1, hy.2⟩)]
    refine Finset.sum_congr rfl fun G hG ↦ ?_
    simp only [Finset.mem_filter, Finset.mem_range] at hG
    have hfib : ((range n).filter (fun y ↦ key j < key (grp y))).filter (fun y ↦ grp y = G) =
        Finset.Ico (st G) (st (G + 1)) := by
      ext y
      simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
      constructor
      · rintro ⟨⟨hy, -⟩, rfl⟩
        exact ⟨(hgrp y hy).2.1, (hgrp y hy).2.2⟩
      · rintro ⟨h1, h2⟩
        obtain ⟨hy, hgy⟩ := hgrp' G hG.1 y h1 h2
        exact ⟨⟨hy, by rw [hgy]; exact hG.2⟩, hgy⟩
    rw [hfib, Finset.sum_congr rfl (g := fun _ ↦ 2 ^ kg G) (fun y hy ↦ by
      simp only [Finset.mem_Ico] at hy
      have := hgrp' G hG.1 y hy.1 hy.2
      rw [hκ y this.1, this.2]), Finset.sum_const, Nat.card_Ico, smul_eq_mul]
  · rw [Finset.sum_congr rfl (g := fun _ ↦ 2 ^ kg j) (fun y hy ↦ by
      simp only [Finset.mem_Ico] at hy
      have := hgrp' j hgx y hy.1 (by omega)
      rw [hκ y this.1, this.2]), Finset.sum_const, Nat.card_Ico, smul_eq_mul]

end
end LeanVM.Guest.B1.Tables
