/-
  LeanVM.Guest.B1.Place.OsLkMem6

  open_stacked's own buffers in the callees' words `osLk`: membership, reads, regions.
-/

module

public import LeanVM.Guest.B1.Place.OsLay
public import LeanVM.Guest.B1.Place.OsPlace

/-!
# The own buffers in `osLk`

`osLk_mem`: buffer `j ≠ 8` (all but the query bit pointers) is an entry of `osLk`, at its base,
holding its honest words. So every memory holding `osLk` reads them at the buffer's pointer
(`osLk_reads`) and their addresses lie in its region (`osLk_region`). `osOwnL_getD_*`: the honest
words of the buffers the callees read.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Guest.B1.Whir
open LeanVM.Protocol.Verifier hiding Layout
open LeanVM.Guest.B1.Main (Layout MemL RegionL)

@[expose] public section

theorem length_flatMap_two {α : Type} (n : ℕ) (a b : ℕ → α) :
    ((List.range n).flatMap fun i ↦ [a i, b i]).length = 2 * n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [List.range_succ, List.flatMap_append, List.length_append, ih]; simp; ring

theorem getD_flatMap_two {α : Type} (d : α) (a b : ℕ → α) : ∀ (n i : ℕ), i < n →
    ((List.range n).flatMap fun i ↦ [a i, b i]).getD (2 * i) d = a i ∧
      ((List.range n).flatMap fun i ↦ [a i, b i]).getD (2 * i + 1) d = b i
  | 0, _, h => absurd h (by omega)
  | n + 1, i, h => by
    rw [List.range_succ, List.flatMap_append]
    by_cases hi : i < n
    · have := getD_flatMap_two d a b n i hi
      rw [List.getD_append _ _ _ _ (by rw [length_flatMap_two]; omega),
        List.getD_append _ _ _ _ (by rw [length_flatMap_two]; omega)]
      exact this
    · obtain rfl : i = n := by omega
      rw [List.getD_append_right _ _ _ _ (by rw [length_flatMap_two]),
        List.getD_append_right _ _ _ _ (by rw [length_flatMap_two]; omega), length_flatMap_two]
      simp

theorem length_osSizesL (c : OsCfg) : (osSizesL c).length = 18 + 3 * c.levels.length := by
  simp only [osSizesL, List.length_append, length_flatMap_two, List.length_cons, List.length_nil,
    List.length_map, List.length_range]
  ring

theorem length_osOwnL (c : OsCfg) (tr : OsTr) (bp : ℕ → ℕ → E) :
    (osOwnL c tr bp).length = 18 + 3 * c.levels.length := by
  simp only [osOwnL, List.length_append, length_flatMap_two, List.length_cons, List.length_nil,
    List.length_map, List.length_range]
  ring

/-- The buffers after the head's. -/
noncomputable def osOwnR (c : OsCfg) (tr : OsTr) : List (List E) :=
  (List.range c.levels.length).flatMap (fun i ↦ [sqzC c tr i, wpC c tr i]) ++
  ([tailC tr.Lf tr.xsR, ptC tr (c.levels.headD default).folds,
    pt1C tr (c.levels.headD default).folds, bdC c tr, lsC c tr, ichC c tr] ++
  (List.range c.levels.length).map (rcC c tr))

theorem osOwnL_eq6 (c : OsCfg) (tr : OsTr) (bp : ℕ → ℕ → E) :
    osOwnL c tr bp = [capsC c tr, flagsC c tr, fmsgC c tr, rootsC c tr, fchC c tr, betasC c tr,
      musC c tr, qposC c tr, qbpC c bp, winC, oodzC c tr, oodC c tr] ++ osOwnR c tr := by
  simp only [osOwnL, osOwnR, List.append_assoc]

/-- Buffer `j`'s words are the same for all window pointers, but the window pointers'. -/
theorem osOwnL_getD_ne8 (c : OsCfg) (tr : OsTr) (bp bp' : ℕ → ℕ → E) {j : ℕ} (h8 : j ≠ 8) :
    (osOwnL c tr bp).getD j [] = (osOwnL c tr bp').getD j [] := by
  have e : ∀ q : ℕ → ℕ → E, osOwnL c tr q = [capsC c tr, flagsC c tr, fmsgC c tr, rootsC c tr,
      fchC c tr, betasC c tr, musC c tr, qposC c tr] ++ (qbpC c q :: ([winC, oodzC c tr, oodC c tr] ++
        osOwnR c tr)) := fun q ↦ by rw [osOwnL_eq6]; simp
  rw [e, e]
  rcases Nat.lt_or_ge j 8 with hj | hj
  · rw [List.getD_append _ _ _ _ (by simpa using hj), List.getD_append _ _ _ _ (by simpa using hj)]
  · rw [List.getD_append_right _ _ _ _ (by simpa using hj),
      List.getD_append_right _ _ _ _ (by simpa using hj)]
    simp only [List.length_cons, List.length_nil]
    rw [show j - 8 = (j - 9) + 1 by omega, List.getD_cons_succ, List.getD_cons_succ]

theorem osOwnL_getD_head6 (c : OsCfg) (tr : OsTr) (bp : ℕ → ℕ → E) :
    (osOwnL c tr bp).getD 0 [] = capsC c tr ∧ (osOwnL c tr bp).getD 1 [] = flagsC c tr ∧
      (osOwnL c tr bp).getD 6 [] = musC c tr ∧ (osOwnL c tr bp).getD 7 [] = qposC c tr ∧
      (osOwnL c tr bp).getD 8 [] = qbpC c bp ∧ (osOwnL c tr bp).getD 9 [] = winC := by
  rw [osOwnL_eq6]
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem osOwnL_getD_R (c : OsCfg) (tr : OsTr) (bp : ℕ → ℕ → E) (j : ℕ) :
    (osOwnL c tr bp).getD (12 + j) [] = (osOwnR c tr).getD j [] := by
  rw [osOwnL_eq6, List.getD_append_right _ _ _ _ (by simp)]
  simp

theorem osOwnL_getD_lv6 (c : OsCfg) (tr : OsTr) (bp : ℕ → ℕ → E) {i : ℕ}
    (hi : i < c.levels.length) :
    (osOwnL c tr bp).getD (osIxSqz i) [] = sqzC c tr i ∧
      (osOwnL c tr bp).getD (osIxWp i) [] = wpC c tr i := by
  have h := getD_flatMap_two [] (sqzC c tr) (wpC c tr) c.levels.length i hi
  unfold osIxSqz osIxWp
  rw [osOwnL_getD_R, show 13 + 2 * i = 12 + (2 * i + 1) by omega, osOwnL_getD_R, osOwnR,
    List.getD_append _ _ _ _ (by rw [length_flatMap_two]; omega),
    List.getD_append _ _ _ _ (by rw [length_flatMap_two]; omega)]
  exact h

theorem osOwnL_getD_fin6 (c : OsCfg) (tr : OsTr) (bp : ℕ → ℕ → E) {i : ℕ}
    (hi : i < c.levels.length) :
    (osOwnL c tr bp).getD (osIxBD c) [] = bdC c tr ∧
      (osOwnL c tr bp).getD (osIxRC c i) [] = rcC c tr i := by
  have l6 : [tailC tr.Lf tr.xsR, ptC tr (c.levels.headD default).folds,
      pt1C tr (c.levels.headD default).folds, bdC c tr, lsC c tr, ichC c tr].length = 6 := rfl
  have hR : ∀ j, (osOwnR c tr).getD (2 * c.levels.length + j) [] =
      ([tailC tr.Lf tr.xsR, ptC tr (c.levels.headD default).folds,
        pt1C tr (c.levels.headD default).folds, bdC c tr, lsC c tr, ichC c tr] ++
        (List.range c.levels.length).map (rcC c tr)).getD j [] := fun j ↦ by
    rw [osOwnR, List.getD_append_right _ _ _ _ (by rw [length_flatMap_two]; omega),
      length_flatMap_two, Nat.add_sub_cancel_left]
  unfold osIxBD osIxRC
  constructor
  · rw [show 15 + 2 * c.levels.length = 12 + (2 * c.levels.length + 3) by omega, osOwnL_getD_R, hR,
      List.getD_append _ _ _ _ (by rw [l6]; omega)]
    rfl
  · rw [show 18 + 2 * c.levels.length + i = 12 + (2 * c.levels.length + (6 + i)) by omega,
      osOwnL_getD_R, hR, List.getD_append_right _ _ _ _ (by rw [l6]; omega), l6,
      Nat.add_sub_cancel_left, List.getD_eq_getElem _ _ (by simpa using hi)]
    simp

/-- **Buffer `j ≠ 8` is an entry of `osLk`.** -/
theorem osLk_mem (c : OsCfg) (tr : OsTr) (b : ℕ) (Lin : Layout) (bp : ℕ → ℕ → E) {j : ℕ}
    (hj : j < 18 + 3 * c.levels.length) (h8 : j ≠ 8) :
    (osBase c b j, (osOwnL c tr bp).getD j []) ∈ osLk c tr b Lin := by
  unfold osLk
  refine List.mem_append_left _ (List.mem_eraseIdx_iff_getElem?.mpr ⟨j, h8, ?_⟩)
  have h1 : j < (bases b (osSizesL c)).length := by rw [os_length_bases, length_osSizesL]; exact hj
  have h2 : j < (osOwnL c tr fun _ _ ↦ 0).length := by rw [length_osOwnL]; exact hj
  unfold bufL
  rw [List.getElem?_eq_getElem (by simp; omega), List.getElem_zip, osBase,
    List.getD_eq_getElem _ _ h1, osOwnL_getD_ne8 c tr bp (fun _ _ ↦ 0) h8,
    List.getD_eq_getElem _ _ h2]

/-- **A memory holding `osLk` reads buffer `j ≠ 8` at its pointer.** -/
theorem osLk_reads {c : OsCfg} {tr : OsTr} {b : ℕ} {Lin : Layout} {rd : Reader}
    (hm : MemL rd (osLk c tr b Lin)) (bp : ℕ → ℕ → E) {j : ℕ}
    (hj : j < 18 + 3 * c.levels.length) (h8 : j ≠ 8) :
    ReadsAt rd (osPtrAt c b j) ((osOwnL c tr bp).getD j []) := by
  have := hm _ (osLk_mem c tr b Lin bp hj h8)
  exact this

/-- **Buffer `j ≠ 8`'s addresses lie in `osLk`'s region.** -/
theorem osLk_region (c : OsCfg) (tr : OsTr) (b : ℕ) (Lin : Layout) (bp : ℕ → ℕ → E) {j : ℕ}
    (hj : j < 18 + 3 * c.levels.length) (h8 : j ≠ 8) {k : ℕ}
    (hk : k < ((osOwnL c tr bp).getD j []).length) :
    RegionL (osLk c tr b Lin) (osBase c b j + k) :=
  ⟨_, osLk_mem c tr b Lin bp hj h8, by simp, by simpa using hk⟩

end
end LeanVM.Guest.B1
