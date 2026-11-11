/-
  LeanVM.Guest.B1.Place.OsLkMem

  What a memory holding the callees' words holds, and where those words lie.
-/

module

public import LeanVM.Guest.B1.Place.OsLayFacts

/-!
# The callees' words

`osLk c tr b Lin` is the own buffers but the window pointers, and the caller's words.

* `osLk_readsAt`, `osMem_of_memLk`: a memory holding it holds each of those buffers, so what the
  body reads (`OsMem`), and the row weights its callees read (`osLk_wp`).
* `regionL_osLk`: its words lie in the caller's or in the own buffers; `regionL_osW`: level `l`'s
  window pointers lie in the own buffers (in `query_win_ptrs`).
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Guest.B1.Whir
open LeanVM.Protocol.Verifier hiding Layout
open LeanVM.Guest.B1.Main (Layout MemL RegionL)

@[expose] public section

variable {c : OsCfg} {tr : OsTr}

theorem bufL_os_length (c : OsCfg) (tr : OsTr) (b : ℕ) (bp : ℕ → ℕ → E) :
    (bufL b (osSizesL c) (osOwnL c tr bp)).length = 16 + c.levels.length := by
  simp only [bufL, List.length_zip, os_length_bases, osSizesL_length, osOwnL_length, Nat.min_self]

theorem bufL_os_get_ne6 (c : OsCfg) (tr : OsTr) (b : ℕ) (bp bp' : ℕ → ℕ → E) {i : ℕ} (hne : i ≠ 6)
    (hi : i < (bufL b (osSizesL c) (osOwnL c tr bp)).length)
    (hi' : i < (bufL b (osSizesL c) (osOwnL c tr bp')).length) :
    (bufL b (osSizesL c) (osOwnL c tr bp))[i]'hi = (bufL b (osSizesL c) (osOwnL c tr bp'))[i]'hi' := by
  have h1 := osOwnL_getElem?_ne6 c tr bp bp' hne
  have hi2 : i < (osOwnL c tr bp).length := by rw [osOwnL_length]; rw [bufL_os_length] at hi; omega
  have hi3 : i < (osOwnL c tr bp').length := by rw [osOwnL_length]; rw [bufL_os_length] at hi; omega
  rw [List.getElem?_eq_getElem hi2, List.getElem?_eq_getElem hi3, Option.some.injEq] at h1
  simp only [bufL, List.getElem_zip, h1]

/-- **A memory holding the callees' words holds each own buffer but the window pointers.** -/
theorem osLk_readsAt {rd : Reader} {b : ℕ} {Lin : Layout}
    (hpt : (tr.point (c.levels.headD default).folds).length ≤ pointCap) (htl : tr.Lf.ml ≤ yrLogCap)
    (hm : MemL rd (osLk c tr b Lin)) {j : ℕ} (hj : j < 16 + c.levels.length) (hne : j ≠ 6) :
    ReadsAt rd (osPtrAt c b j) ((osOwnL c tr fun _ _ ↦ 0).getD j []) := by
  have hf := osOwnL_fit c tr (fun _ _ ↦ 0) hpt htl
  have hjs : j < (osSizesL c).length := by rw [osSizesL_length]; exact hj
  have e := os_bufL_getD (b := b) hf hjs
  have hl : j < (bufL b (osSizesL c) (osOwnL c tr fun _ _ ↦ 0)).length := by
    rw [bufL_os_length]; exact hj
  have hmem : (bufL b (osSizesL c) (osOwnL c tr fun _ _ ↦ 0)).getD j default ∈
      (bufL b (osSizesL c) (osOwnL c tr fun _ _ ↦ 0)).eraseIdx 6 := by
    rw [List.getD_eq_getElem _ _ hl]
    exact List.mem_eraseIdx_iff_getElem.mpr ⟨j, hl, hne, rfl⟩
  rw [e] at hmem
  have := hm _ (List.mem_append_left _ hmem)
  exact this

/-- **A memory holding the callees' words holds what the body reads.** -/
theorem osMem_of_memLk {rd : Reader} {b : ℕ} {Lin : Layout}
    (hpt : (tr.point (c.levels.headD default).folds).length ≤ pointCap) (htl : tr.Lf.ml ≤ yrLogCap)
    (hm : MemL rd (osLk c tr b Lin)) : OsMem rd (osAtOf c b) c tr := by
  have R := fun j (hj : j < 16 + c.levels.length) (hne : j ≠ 6) ↦ osLk_readsAt hpt htl hm hj hne
  obtain ⟨g0, g1, g2, g3, g4, g5, -, g7, g8, g9⟩ := osOwnL_getD_head c tr fun _ _ ↦ 0
  obtain ⟨gT, gP, gP1, gB, gL, gI⟩ := osOwnL_getD_fin c tr fun _ _ ↦ 0
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← g2]; exact R 2 (by omega) (by omega)
  · rw [← g1]; exact R 1 (by omega) (by omega)
  · rw [← g3]; exact R 3 (by omega) (by omega)
  · rw [← g4]; exact R 4 (by omega) (by omega)
  · rw [← g7]; exact R 7 (by omega) (by omega)
  · rw [← g5]; exact R 5 (by omega) (by omega)
  · rw [← g8]; exact R 8 (by omega) (by omega)
  · rw [← g9]; exact R 9 (by omega) (by omega)
  · rw [← g0]; exact R 0 (by omega) (by omega)
  · rw [← gT]; exact R _ (by unfold osIxT; omega) (by unfold osIxT; omega)
  · rw [← gP]; exact R _ (by unfold osIxPT; omega) (by unfold osIxPT; omega)
  · rw [← gP1]; exact R _ (by unfold osIxPT1; omega) (by unfold osIxPT1; omega)
  · rw [← gB]; exact R _ (by unfold osIxBD; omega) (by unfold osIxBD; omega)
  · rw [← gL]; exact R _ (by unfold osIxLS; omega) (by unfold osIxLS; omega)
  · rw [← gI]; exact R _ (by unfold osIxICH; omega) (by unfold osIxICH; omega)

theorem osLk_wp {rd : Reader} {b : ℕ} {Lin : Layout}
    (hpt : (tr.point (c.levels.headD default).folds).length ≤ pointCap) (htl : tr.Lf.ml ≤ yrLogCap)
    (hm : MemL rd (osLk c tr b Lin)) {i : ℕ} (hi : i < c.levels.length) :
    ReadsAt rd ((osAtOf c b).wp i) (wpC c tr i) := by
  rw [← osOwnL_getD_lv c tr (fun _ _ ↦ 0) hi]
  exact osLk_readsAt hpt htl hm (by unfold osIxWp; omega) (by unfold osIxWp; omega)

/-- **The callees' words lie in the caller's or in the own buffers.** -/
theorem regionL_osLk {b : ℕ} {Lin : Layout} (bp : ℕ → ℕ → E) {i : ℕ}
    (h : RegionL (osLk c tr b Lin) i) :
    RegionL Lin i ∨ RegionL (bufL b (osSizesL c) (osOwnL c tr bp)) i := by
  obtain ⟨q, hq, h1, h2⟩ := h
  rcases List.mem_append.mp hq with hq | hq
  · right
    obtain ⟨j, hj, hne, rfl⟩ := List.mem_eraseIdx_iff_getElem.mp hq
    have hj' : j < (bufL b (osSizesL c) (osOwnL c tr bp)).length := by
      rw [bufL_os_length]; rw [bufL_os_length] at hj; exact hj
    refine ⟨_, List.getElem_mem hj', ?_, ?_⟩ <;>
      rw [← bufL_os_get_ne6 c tr b (fun _ _ ↦ 0) bp hne hj hj'] <;> assumption
  · exact Or.inl ⟨q, hq, h1, h2⟩

/-- **Level `l`'s window pointers lie in `query_win_ptrs`.** -/
theorem regionL_osW {cert : String → V → ℕ} {D : ℕ → ℕ → ℕ → ℕ} {b : ℕ} (bp : ℕ → ℕ → E)
    (hs : OsSizes c) {l p : ℕ} (hl : l < c.levels.length) {i : ℕ}
    (h : RegionL (osW cert c D b l p) i) : RegionL (bufL b (osSizesL c) (osOwnL c tr bp)) i := by
  obtain ⟨q, hq, h1, h2⟩ := h
  simp only [osW, List.mem_singleton] at hq
  subst hq
  simp only [List.length_map, List.length_range] at h1 h2
  have hend := off_end (off := fun i ↦ (lvAt c i).posOff)
    (span := fun i ↦ (lvAt c i).squeezes * (192 / (lvAt c i).depth)) hs.pos (c.levels.length - 1 - l) l
    (by omega)
  have hend' : (lvAt c l).posOff + (lvAt c l).squeezes * (192 / (lvAt c l).depth) ≤
      c.levels.length * ligPosCap := hend
  have h8 : 6 < (bufL b (osSizesL c) (osOwnL c tr bp)).length := by rw [bufL_os_length]; omega
  refine ⟨_, List.getElem_mem h8, ?_, ?_⟩
  · simp only [bufL, List.getElem_zip]
    have : (bases b (osSizesL c))[6]'(by simp [os_length_bases, osSizesL_length]; omega) = osBase c b 6 := by
      unfold osBase; rw [List.getD_eq_getElem]
    rw [this]; omega
  · simp only [bufL, List.getElem_zip]
    have e1 : (bases b (osSizesL c))[6]'(by simp [os_length_bases, osSizesL_length]; omega) = osBase c b 6 := by
      unfold osBase; rw [List.getD_eq_getElem]
    have e2 : ((osOwnL c tr bp)[6]'(by rw [osOwnL_length]; omega)).length =
        c.levels.length * ligPosCap := by
      have := (osOwnL_getD_head c tr bp).2.2.2.2.2.2.1
      rw [List.getD_eq_getElem _ _ (by rw [osOwnL_length]; omega)] at this
      rw [this]; simp [qbpC]
    rw [e1, e2]; omega

end
end LeanVM.Guest.B1
