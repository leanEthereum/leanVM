/-
  LeanVM.Guest.B1.Place.OsLayFacts

  open_stacked's own buffers: their words fit, the memory holding them holds what the body reads,
  the point buffers returned.
-/

module

public import LeanVM.Guest.B1.Place.OsLay
public import LeanVM.Guest.B1.Place.OsPlace
public import LeanVM.Guest.B1.Whir.BrFin2

/-!
# `open_stacked`'s buffers, their facts

* `osOwnL_fit`: each buffer's honest words fit its size.
* `osOwnL_getD_*`: buffer `j`'s words; `memL_readsAt`: a memory holding the buffers holds buffer
  `j`'s words at its pointer `osPtrAt c b j`.
* `osMem_of_memL`: so it holds what the body reads (`OsMem`).
* `osLk_memL`, `osW_memL`: and the callees' words (`osLk`), and level `l`'s query bit pointers
  (`osW`) when the bit pointers are the decoders' (`osBp`).
* `osLoutJ_eq`, `osJs_nodup`, `osJs_lt`: the returned buffers, the point and `point1`.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Guest.B1.Whir
open LeanVM.Protocol.Verifier hiding Layout
open LeanVM.Guest.B1.Main (Layout MemL RegionL)

@[expose] public section

/-! ## Lists of pairs -/

theorem pairs_length {α : Type} (f g : ℕ → α) (n : ℕ) :
    ((List.range n).flatMap fun i ↦ [f i, g i]).length = 2 * n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [List.range_succ, List.flatMap_append, List.length_append, ih]; simp; ring

theorem pairs_getD {α : Type} (f g : ℕ → α) (d : α) : ∀ (n i : ℕ), i < n →
    ((List.range n).flatMap fun i ↦ [f i, g i]).getD (2 * i) d = f i ∧
      ((List.range n).flatMap fun i ↦ [f i, g i]).getD (2 * i + 1) d = g i
  | 0, _, h => absurd h (by omega)
  | n + 1, i, h => by
    rw [List.range_succ, List.flatMap_append]
    by_cases hi : i < n
    · rw [List.getD_append _ _ _ _ (by rw [pairs_length]; omega),
        List.getD_append _ _ _ _ (by rw [pairs_length]; omega)]
      exact pairs_getD f g d n i hi
    · have e : i = n := by omega
      subst e
      rw [List.getD_append_right _ _ _ _ (by rw [pairs_length]),
        List.getD_append_right _ _ _ _ (by rw [pairs_length]; omega), pairs_length]
      simp

theorem forall₂_pairs {α β : Type} {R : α → β → Prop} (f g : ℕ → α) (f' g' : ℕ → β)
    (h : ∀ i, R (f i) (f' i) ∧ R (g i) (g' i)) : ∀ n : ℕ,
    List.Forall₂ R ((List.range n).flatMap fun i ↦ [f i, g i]) ((List.range n).flatMap fun i ↦ [f' i, g' i])
  | 0 => List.Forall₂.nil
  | n + 1 => by
    rw [List.range_succ, List.flatMap_append, List.flatMap_append]
    exact List.rel_append (forall₂_pairs f g f' g' h n)
      (by simpa using List.Forall₂.cons (h n).1 (List.Forall₂.cons (h n).2 List.Forall₂.nil))

theorem forall₂_map_map (f : ℕ → List E) (sz : ℕ → ℕ) : ∀ n : ℕ, (∀ i, (f i).length ≤ sz i) →
    List.Forall₂ (fun c s ↦ c.length ≤ s) ((List.range n).map f) ((List.range n).map sz)
  | 0, _ => List.Forall₂.nil
  | n + 1, h => by
    rw [List.range_succ, List.map_append, List.map_append]
    exact List.rel_append (forall₂_map_map f sz n h)
      (List.Forall₂.cons (h n) List.Forall₂.nil)

/-! ## The buffers -/

variable {c : OsCfg} {tr : OsTr}

theorem osSizesL_length (c : OsCfg) : (osSizesL c).length = 18 + 3 * c.levels.length := by
  simp only [osSizesL, List.length_append, List.length_cons, List.length_nil, List.length_map,
    List.length_range]
  rw [show ((List.range c.levels.length).flatMap fun _ ↦ [(c.maxSq + 1) * 5, c.maxIl]) =
    (List.range c.levels.length).flatMap fun i ↦ [(fun _ ↦ (c.maxSq + 1) * 5) i, (fun _ ↦ c.maxIl) i]
    from rfl, pairs_length]
  ring

theorem osOwnL_length (c : OsCfg) (tr : OsTr) (bp : ℕ → ℕ → E) :
    (osOwnL c tr bp).length = 18 + 3 * c.levels.length := by
  simp only [osOwnL, List.length_append, List.length_cons, List.length_nil, List.length_map,
    List.length_range]
  rw [show ((List.range c.levels.length).flatMap fun i ↦ [sqzC c tr i, wpC c tr i]) =
    (List.range c.levels.length).flatMap fun i ↦ [(fun i ↦ sqzC c tr i) i, (fun i ↦ wpC c tr i) i]
    from rfl, pairs_length]
  ring

/-- **The honest words fit their buffers.** -/
theorem osOwnL_fit (c : OsCfg) (tr : OsTr) (bp : ℕ → ℕ → E)
    (hpt : (tr.point (c.levels.headD default).folds).length ≤ pointCap)
    (htl : tr.Lf.ml ≤ yrLogCap) :
    List.Forall₂ (fun c s ↦ c.length ≤ s) (osOwnL c tr bp) (osSizesL c) := by
  unfold osOwnL osSizesL
  refine List.rel_append (List.rel_append (List.rel_append ?_ ?_) ?_) ?_
  · simp [capsC, flagsC, fmsgC, rootsC, fchC, betasC, musC, qposC, qbpC, winC, oodzC, oodC]
  · exact forall₂_pairs _ _ _ _ (fun i ↦ ⟨by simp [sqzC], by simp [wpC]⟩) _
  · simp only [List.forall₂_cons, List.Forall₂.nil, and_true]
    refine ⟨?_, ?_, ?_, by simp [bdC], by simp [lsC], by simp [ichC]⟩
    · simp only [tailC, List.length_append, tailChs_length, List.length_replicate]; omega
    · simp only [ptC, List.length_append, List.length_replicate]; omega
    · simp only [pt1C, List.length_append, List.length_map, List.length_replicate]; omega
  · exact forall₂_map_map _ _ _ fun i ↦ by simp [rcC]

/-! ## Buffer `j`'s words -/

theorem osOwnL_getD_head (c : OsCfg) (tr : OsTr) (bp : ℕ → ℕ → E) :
    (osOwnL c tr bp).getD 0 [] = capsC c tr ∧ (osOwnL c tr bp).getD 1 [] = flagsC c tr ∧
      (osOwnL c tr bp).getD 2 [] = fmsgC c tr ∧ (osOwnL c tr bp).getD 3 [] = rootsC c tr ∧
      (osOwnL c tr bp).getD 4 [] = fchC c tr ∧ (osOwnL c tr bp).getD 5 [] = betasC c tr ∧
      (osOwnL c tr bp).getD 6 [] = musC c tr ∧ (osOwnL c tr bp).getD 7 [] = qposC c tr ∧
      (osOwnL c tr bp).getD 8 [] = qbpC c bp ∧ (osOwnL c tr bp).getD 9 [] = winC ∧
      (osOwnL c tr bp).getD 10 [] = oodzC c tr ∧ (osOwnL c tr bp).getD 11 [] = oodC c tr :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The head's twelve buffers. -/
noncomputable def osOwnA (c : OsCfg) (tr : OsTr) (bp : ℕ → ℕ → E) : List (List E) :=
  [capsC c tr, flagsC c tr, fmsgC c tr, rootsC c tr, fchC c tr, betasC c tr, musC c tr, qposC c tr,
    qbpC c bp, winC, oodzC c tr, oodC c tr]

/-- The levels' buffers. -/
noncomputable def osOwnF (c : OsCfg) (tr : OsTr) : List (List E) :=
  (List.range c.levels.length).flatMap (fun i ↦ [sqzC c tr i, wpC c tr i])

/-- The tail's and the finish's six. -/
noncomputable def osOwnC (c : OsCfg) (tr : OsTr) : List (List E) :=
  [tailC tr.Lf tr.xsR, ptC tr (c.levels.headD default).folds,
    pt1C tr (c.levels.headD default).folds, bdC c tr, lsC c tr, ichC c tr]

theorem osOwnL_eq (c : OsCfg) (tr : OsTr) (bp : ℕ → ℕ → E) :
    osOwnL c tr bp = osOwnA c tr bp ++ osOwnF c tr ++ osOwnC c tr ++
      (List.range c.levels.length).map (rcC c tr) := rfl

theorem osOwnF_length (c : OsCfg) (tr : OsTr) : (osOwnF c tr).length = 2 * c.levels.length :=
  pairs_length (fun i ↦ sqzC c tr i) (fun i ↦ wpC c tr i) c.levels.length

theorem osOwnL_getD_lv (c : OsCfg) (tr : OsTr) (bp : ℕ → ℕ → E) {i : ℕ} (hi : i < c.levels.length) :
    (osOwnL c tr bp).getD (osIxSqz i) [] = sqzC c tr i ∧
      (osOwnL c tr bp).getD (osIxWp i) [] = wpC c tr i := by
  have hp := pairs_getD (fun i ↦ sqzC c tr i) (fun i ↦ wpC c tr i) [] c.levels.length i hi
  have hl := osOwnF_length c tr
  have hA : (osOwnA c tr bp).length = 12 := rfl
  have hC : (osOwnC c tr).length = 6 := rfl
  rw [osOwnL_eq]
  unfold osIxSqz osIxWp
  constructor
  · rw [List.getD_append _ _ _ _ (by simp only [List.length_append, hA, hl, hC]; omega),
      List.getD_append _ _ _ _ (by simp only [List.length_append, hA, hl]; omega),
      List.getD_append_right _ _ _ _ (by rw [hA]; omega), hA,
      show 12 + 2 * i - 12 = 2 * i by omega]
    exact hp.1
  · rw [List.getD_append _ _ _ _ (by simp only [List.length_append, hA, hl, hC]; omega),
      List.getD_append _ _ _ _ (by simp only [List.length_append, hA, hl]; omega),
      List.getD_append_right _ _ _ _ (by rw [hA]; omega), hA,
      show 13 + 2 * i - 12 = 2 * i + 1 by omega]
    exact hp.2

theorem osOwnL_getD_finC (c : OsCfg) (tr : OsTr) (bp : ℕ → ℕ → E) {t : ℕ} (ht : t < 6) :
    (osOwnL c tr bp).getD (12 + 2 * c.levels.length + t) [] = (osOwnC c tr).getD t [] := by
  have hl := osOwnF_length c tr
  have hA : (osOwnA c tr bp).length = 12 := rfl
  have hC : (osOwnC c tr).length = 6 := rfl
  rw [osOwnL_eq, List.getD_append _ _ _ _ (by simp only [List.length_append, hA, hl, hC]; omega),
    List.getD_append_right _ _ _ _ (by simp only [List.length_append, hA, hl]; omega)]
  simp only [List.length_append, hA, hl]
  rw [show 12 + 2 * c.levels.length + t - (12 + 2 * c.levels.length) = t by omega]

theorem osOwnL_getD_fin (c : OsCfg) (tr : OsTr) (bp : ℕ → ℕ → E) :
    (osOwnL c tr bp).getD (osIxT c) [] = tailC tr.Lf tr.xsR ∧
      (osOwnL c tr bp).getD (osIxPT c) [] = ptC tr (c.levels.headD default).folds ∧
      (osOwnL c tr bp).getD (osIxPT1 c) [] = pt1C tr (c.levels.headD default).folds ∧
      (osOwnL c tr bp).getD (osIxBD c) [] = bdC c tr ∧ (osOwnL c tr bp).getD (osIxLS c) [] = lsC c tr ∧
      (osOwnL c tr bp).getD (osIxICH c) [] = ichC c tr := by
  have h0 := osOwnL_getD_finC c tr bp (t := 0) (by omega)
  have h1 := osOwnL_getD_finC c tr bp (t := 1) (by omega)
  have h2 := osOwnL_getD_finC c tr bp (t := 2) (by omega)
  have h3 := osOwnL_getD_finC c tr bp (t := 3) (by omega)
  have h4 := osOwnL_getD_finC c tr bp (t := 4) (by omega)
  have h5 := osOwnL_getD_finC c tr bp (t := 5) (by omega)
  unfold osIxT osIxPT osIxPT1 osIxBD osIxLS osIxICH
  rw [show 13 + 2 * c.levels.length = 12 + 2 * c.levels.length + 1 by omega,
    show 14 + 2 * c.levels.length = 12 + 2 * c.levels.length + 2 by omega,
    show 15 + 2 * c.levels.length = 12 + 2 * c.levels.length + 3 by omega,
    show 16 + 2 * c.levels.length = 12 + 2 * c.levels.length + 4 by omega,
    show 17 + 2 * c.levels.length = 12 + 2 * c.levels.length + 5 by omega, h1, h2, h3, h4, h5]
  exact ⟨h0, rfl, rfl, rfl, rfl, rfl⟩

theorem osOwnL_getD_rc (c : OsCfg) (tr : OsTr) (bp : ℕ → ℕ → E) {i : ℕ} (hi : i < c.levels.length) :
    (osOwnL c tr bp).getD (osIxRC c i) [] = rcC c tr i := by
  have hl := osOwnF_length c tr
  have hA : (osOwnA c tr bp).length = 12 := rfl
  have hC : (osOwnC c tr).length = 6 := rfl
  unfold osIxRC
  rw [osOwnL_eq, List.getD_append_right _ _ _ _ (by simp only [List.length_append, hA, hl, hC]; omega)]
  simp only [List.length_append, hA, hl, hC]
  rw [show 18 + 2 * c.levels.length + i - (12 + 2 * c.levels.length + 6) = i by omega]
  simp [hi]

/-! ## The memory holding them -/

theorem memL_readsAt {rd : Reader} {b : ℕ} {sizes : List ℕ} {own : List (List E)}
    (hf : List.Forall₂ (fun c s ↦ c.length ≤ s) own sizes) (hm : MemL rd (bufL b sizes own))
    {j : ℕ} (hj : j < sizes.length) :
    ReadsAt rd (ofK (addressOfIndex ((bases b sizes).getD j 0))) (own.getD j []) := by
  have e := os_bufL_getD (b := b) hf hj
  have hlen : j < (bufL b sizes own).length := by
    simp only [bufL, List.length_zip, os_length_bases, hf.length_eq, Nat.min_self]; exact hj
  have hmem : (bufL b sizes own).getD j default ∈ bufL b sizes own := by
    rw [List.getD_eq_getElem _ _ hlen]; exact List.getElem_mem hlen
  rw [e] at hmem
  exact hm _ hmem

theorem osMemL_readsAt {rd : Reader} {b : ℕ} {bp : ℕ → ℕ → E}
    (hpt : (tr.point (c.levels.headD default).folds).length ≤ pointCap) (htl : tr.Lf.ml ≤ yrLogCap)
    (hm : MemL rd (bufL b (osSizesL c) (osOwnL c tr bp))) {j : ℕ}
    (hj : j < 18 + 3 * c.levels.length) :
    ReadsAt rd (osPtrAt c b j) ((osOwnL c tr bp).getD j []) :=
  memL_readsAt (osOwnL_fit c tr bp hpt htl) hm (by rw [osSizesL_length]; exact hj)

/-- **A memory holding the buffers holds what the body reads.** -/
theorem osMem_of_memL {rd : Reader} {b : ℕ} {bp : ℕ → ℕ → E}
    (hpt : (tr.point (c.levels.headD default).folds).length ≤ pointCap) (htl : tr.Lf.ml ≤ yrLogCap)
    (hm : MemL rd (bufL b (osSizesL c) (osOwnL c tr bp))) : OsMem rd (osAtOf c b) c tr := by
  have R := fun j (hj : j < 18 + 3 * c.levels.length) ↦ osMemL_readsAt hpt htl hm hj
  obtain ⟨-, -, g2, g3, g4, g5, g6, g7, -, g9, g10, g11⟩ := osOwnL_getD_head c tr bp
  obtain ⟨gT, gP, gP1, gB, gL, gI⟩ := osOwnL_getD_fin c tr bp
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, fun i hi ↦ ?_, fun i hi ↦ ?_⟩
  · rw [← g4]; exact R 4 (by omega)
  · rw [← g3]; exact R 3 (by omega)
  · rw [← g5]; exact R 5 (by omega)
  · rw [← g6]; exact R 6 (by omega)
  · rw [← g9]; exact R 9 (by omega)
  · rw [← g7]; exact R 7 (by omega)
  · rw [← g10]; exact R 10 (by omega)
  · rw [← g11]; exact R 11 (by omega)
  · rw [← g2]; exact R 2 (by omega)
  · rw [← gT]; exact R _ (by unfold osIxT; omega)
  · rw [← gP]; exact R _ (by unfold osIxPT; omega)
  · rw [← gP1]; exact R _ (by unfold osIxPT1; omega)
  · rw [← gB]; exact R _ (by unfold osIxBD; omega)
  · rw [← gL]; exact R _ (by unfold osIxLS; omega)
  · rw [← gI]; exact R _ (by unfold osIxICH; omega)
  · rw [← (osOwnL_getD_lv c tr bp hi).1]; exact R _ (by unfold osIxSqz; omega)
  · rw [← osOwnL_getD_rc c tr bp hi]; exact R _ (by unfold osIxRC; omega)

/-! ## The callees' words -/

theorem osOwnA_getElem?_ne8 (c : OsCfg) (tr : OsTr) (bp bp' : ℕ → ℕ → E) {i : ℕ} (hi : i ≠ 8) :
    (osOwnA c tr bp)[i]? = (osOwnA c tr bp')[i]? := by
  unfold osOwnA
  match i, hi with
  | 0, _ => simp
  | 1, _ => simp
  | 2, _ => simp
  | 3, _ => simp
  | 4, _ => simp
  | 5, _ => simp
  | 6, _ => simp
  | 7, _ => simp
  | 9, _ => simp
  | 10, _ => simp
  | 11, _ => simp
  | n + 12, _ => simp

theorem osOwnL_getElem?_ne8 (c : OsCfg) (tr : OsTr) (bp bp' : ℕ → ℕ → E) {i : ℕ} (hi : i ≠ 8) :
    (osOwnL c tr bp)[i]? = (osOwnL c tr bp')[i]? := by
  have hA : (osOwnA c tr bp).length = 12 := rfl
  have hA' : (osOwnA c tr bp').length = 12 := rfl
  rw [osOwnL_eq, osOwnL_eq]
  simp only [List.append_assoc]
  by_cases h : i < 12
  · rw [List.getElem?_append_left (by rw [hA]; exact h), List.getElem?_append_left (by rw [hA']; exact h)]
    exact osOwnA_getElem?_ne8 c tr bp bp' hi
  · have e1 : (osOwnA c tr bp ++ (osOwnF c tr ++ (osOwnC c tr ++
        (List.range c.levels.length).map (rcC c tr))))[i]? = (osOwnF c tr ++ (osOwnC c tr ++
        (List.range c.levels.length).map (rcC c tr)))[i - 12]? := by
      rw [List.getElem?_append_right (by rw [hA]; omega), hA]
    have e2 : (osOwnA c tr bp' ++ (osOwnF c tr ++ (osOwnC c tr ++
        (List.range c.levels.length).map (rcC c tr))))[i]? = (osOwnF c tr ++ (osOwnC c tr ++
        (List.range c.levels.length).map (rcC c tr)))[i - 12]? := by
      rw [List.getElem?_append_right (by rw [hA']; omega), hA']
    rw [e1, e2]

/-- **A memory holding the buffers holds the callees' words** (but the bit pointers). -/
theorem osLk_memL {rd : Reader} {b : ℕ} {bp : ℕ → ℕ → E} {Lin : Layout}
    (hm : MemL rd (bufL b (osSizesL c) (osOwnL c tr bp))) (hLin : MemL rd Lin) :
    MemL rd (osLk c tr b Lin) := by
  refine Main.memL_append.mpr ⟨fun q hq ↦ ?_, hLin⟩
  obtain ⟨i, hi, hne, rfl⟩ := List.mem_eraseIdx_iff_getElem.mp hq
  have hl0 : (bufL b (osSizesL c) (osOwnL c tr fun _ _ ↦ 0)).length = 18 + 3 * c.levels.length := by
    simp only [bufL, List.length_zip, os_length_bases, osSizesL_length, osOwnL_length, Nat.min_self]
  have hl1 : (bufL b (osSizesL c) (osOwnL c tr bp)).length = 18 + 3 * c.levels.length := by
    simp only [bufL, List.length_zip, os_length_bases, osSizesL_length, osOwnL_length, Nat.min_self]
  have hi1 : i < (bufL b (osSizesL c) (osOwnL c tr bp)).length := by omega
  have e : (bufL b (osSizesL c) (osOwnL c tr fun _ _ ↦ 0))[i]'hi =
      (bufL b (osSizesL c) (osOwnL c tr bp))[i]'hi1 := by
    have h1 := osOwnL_getElem?_ne8 c tr (fun _ _ ↦ 0) bp hne
    have hi2 : i < (osOwnL c tr fun _ _ ↦ 0).length := by rw [osOwnL_length]; omega
    have hi3 : i < (osOwnL c tr bp).length := by rw [osOwnL_length]; omega
    rw [List.getElem?_eq_getElem hi2, List.getElem?_eq_getElem hi3, Option.some.injEq] at h1
    simp only [bufL, List.getElem_zip, h1]
  rw [e]
  exact hm _ (List.getElem_mem hi1)


theorem loadHolds_shift {rd : Reader} {B off k : ℕ} {v : E}
    (h : LoadHolds rd (ofK (addressOfIndex B)) (off + k) v) : LoadHolds rd (ofK (addressOfIndex (B +
        off))) k v := by
  refine ⟨ofK_isInK _, ?_⟩
  rw [Main.addr_ofK, Nat.add_assoc]
  have := h.2
  rwa [Main.addr_ofK] at this

/-- **A memory holding the buffers holds level `l`'s query bit pointers**, the bit pointers the
decoders' placed at `ps`. -/
theorem osW_memL {fs : String → ℕ} {cert : String → V → ℕ} {rd : Reader} {b : ℕ} {ps : ℕ → ℕ}
    (hpt : (tr.point (c.levels.headD default).folds).length ≤ pointCap) (htl : tr.Lf.ml ≤ yrLogCap)
    (hs : OsSizes c) {l : ℕ} (hl : l < c.levels.length)
    (hm : MemL rd (bufL b (osSizesL c) (osOwnL c tr (osBp fs cert c ps)))) :
    MemL rd (osW fs cert c b l (ps l)) := by
  intro q hq
  simp only [osW, List.mem_singleton] at hq
  subst hq
  intro k hk
  simp only [List.length_map, List.length_range] at hk
  have R := osMemL_readsAt hpt htl hm (j := 8) (by omega)
  rw [(osOwnL_getD_head c tr _).2.2.2.2.2.2.2.2.1] at R
  have hpos := hs.pos
  have hend := off_end (off := fun i ↦ (lvAt c i).posOff)
    (span := fun i ↦ (lvAt c i).squeezes * (192 / (lvAt c i).depth)) hpos (c.levels.length - 1 - l) l
    (by omega)
  have hend' : (lvAt c l).posOff + (lvAt c l).squeezes * (192 / (lvAt c l).depth) ≤ c.posLen := hend
  have hown : ownerOf (fun i ↦ (lvAt c i).posOff) c.levels.length ((lvAt c l).posOff + k) = l := by
    have := ownerOf_eq (off := fun i ↦ (lvAt c i).posOff)
      (span := fun i ↦ (lvAt c i).squeezes * (192 / (lvAt c i).depth)) hpos (i := l)
      (k := (lvAt c l).posOff + k) (by omega) (by
        show (lvAt c l).posOff + k < (lvAt c l).posOff + (lvAt c l).squeezes * (192 / (lvAt c l).depth)
        omega) (c.levels.length - 1 - l) (by omega)
    rwa [show l + 1 + (c.levels.length - 1 - l) = c.levels.length by omega] at this
  have h1 := readsAt_map_range R (k := (lvAt c l).posOff + k) (by omega)
  simp only [hown, Nat.add_sub_cancel_left, show k < (lvAt c l).squeezes * (192 / (lvAt c l).depth) from hk,
    ↓reduceIte] at h1
  simp only [List.getElem_map, List.getElem_range]
  exact loadHolds_shift h1

/-! ## The returned buffers -/

theorem osJs_nodup (c : OsCfg) : [osIxPT c, osIxPT1 c].Nodup := by
  simp [osIxPT, osIxPT1]

theorem osJs_lt (c : OsCfg) : ∀ j ∈ [osIxPT c, osIxPT1 c], j < (osSizesL c).length := by
  intro j hj
  rw [osSizesL_length]
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
  rcases hj with rfl | rfl <;> simp [osIxPT, osIxPT1] <;> omega

/-- **The returned buffers**: the point and `point1`. -/
theorem osLoutJ_eq (c : OsCfg) (tr : OsTr) (bp : ℕ → ℕ → E) (b : ℕ) :
    osLoutJ b (osSizesL c) (osOwnL c tr bp) [osIxPT c, osIxPT1 c] =
      [(osBase c b (osIxPT c), ptC tr (c.levels.headD default).folds),
        (osBase c b (osIxPT1 c), pt1C tr (c.levels.headD default).folds)] := by
  obtain ⟨-, gP, gP1, -⟩ := osOwnL_getD_fin c tr bp
  have h1 := osJs_lt c (osIxPT c) (by simp)
  have h2 := osJs_lt c (osIxPT1 c) (by simp)
  simp only [osLoutJ, List.map_cons, List.map_nil, gP, gP1, osBase, os_bases_getD _ _ _ h1,
    os_bases_getD _ _ _ h2]

end
end LeanVM.Guest.B1
