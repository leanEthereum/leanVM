/-
  LeanVM.Guest.B1.Whir.OsAsm1

  `open_stacked`'s buffers with the decoders' pointers, against the callees' words.
-/

module

public import LeanVM.Guest.B1.Whir.OsCalls
public import LeanVM.Guest.B1.Whir.OsPoint
public import LeanVM.Guest.B1.Whir.OsGlued

/-!
# The decoders' pointers in the buffers (TRIAGE #36)

The buffers with the decoders' pointers `Q` hold those without (`osLk`'s), and each level's
window `osW l (ps l)` of `Q = qbpC ps`, all within the buffers' region.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Guest.B1.Main (MemL RegionL)

@[expose] public section

namespace OsData

variable {fs : String → ℕ} {cert : String → V → ℕ} {cfg : OsCfg} {d : OsData}

theorem ownQ_set (Q : List E) : d.ownQ cfg Q = (d.ownQ cfg []).set 8 Q := rfl

/-- The buffers' entries without the decoders' pointers: those with them, or empty. -/
theorem bufL_ownQ_nil {b : ℕ} {Q : List E} {q : ℕ × List E} (hq : q ∈ bufL b (osSizes cfg) (d.ownQ cfg [])) :
    q ∈ bufL b (osSizes cfg) (d.ownQ cfg Q) ∨ q.2 = [] := by
  unfold bufL at hq ⊢
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hq
  simp only [List.length_zip] at hi
  by_cases h8 : i = 8
  · subst h8; right; simp [List.getElem_zip, ownQ]
  · left
    refine List.mem_iff_getElem.mpr ⟨i, by simp [ownQ_length] at hi ⊢; omega, ?_⟩
    simp only [List.getElem_zip]
    congr 1
    rw [List.getElem_of_eq (ownQ_set Q), List.getElem_set_ne (Ne.symm h8)]

/-- **The buffers with the decoders' pointers hold those without.** -/
theorem memL_ownQ_nil {rd : Reader} {b : ℕ} {Q : List E} (h : MemL rd (bufL b (osSizes cfg) (d.ownQ cfg Q))) :
    MemL rd (bufL b (osSizes cfg) (d.ownQ cfg [])) := by
  intro q hq
  rcases bufL_ownQ_nil (Q := Q) hq with h1 | h1
  · exact h q h1
  · rw [h1]; exact readsAt_nil _ _

theorem regionL_ownQ_nil {b : ℕ} {Q : List E} {i : ℕ} (h : RegionL (bufL b (osSizes cfg) (d.ownQ cfg [])) i) :
    RegionL (bufL b (osSizes cfg) (d.ownQ cfg Q)) i := by
  obtain ⟨q, hq, h1, h2⟩ := h
  rcases bufL_ownQ_nil (Q := Q) hq with h3 | h3
  · exact ⟨q, h3, h1, h2⟩
  · rw [h3] at h2; simp at h2; omega

/-- **A level's window of the decoders' pointers.** -/
theorem memL_osW (hlay : OsLayoutOk cfg) {rd : Reader} {b : ℕ} {ps : ℕ → ℕ}
    (h : MemL rd (bufL b (osSizes cfg) (d.ownQ cfg (qbpC cfg fs cert ps)))) {l : ℕ} (hl : l < cfg.levels.length) :
    MemL rd (osW fs cert cfg b l (ps l)) := by
  intro q hq
  rw [osW, List.mem_singleton] at hq
  subst hq
  have h8 := os_memL_bufL h (ownQ_length _) (j := 8) (by rw [os_length_osSizes]; omega)
  have e : (d.ownQ cfg (qbpC cfg fs cert ps)).getD 8 [] = qbpC cfg fs cert ps := rfl
  rw [e] at h8
  have hw := os_seg_readsAt (n := cfg.levels.length) (off := fun l => (cfg.lv l).posOff)
    (c := fun l => qbpSeg cfg fs cert l (ps l)) h8
    (fun a c hac hc => by simp only [qbpSeg, List.length_map, List.length_range]; exact hlay.pos a c hac hc)
    (fun a ha => by simp only [qbpSeg, List.length_map, List.length_range]; exact hlay.posFit a ha) hl
  rw [ofK_gpow_mul] at hw
  exact hw

theorem regionL_osW (hlay : OsLayoutOk cfg) {b : ℕ} {ps : ℕ → ℕ} {l p : ℕ} (hl : l < cfg.levels.length) {i : ℕ}
    (h : RegionL (osW fs cert cfg b l p) i) :
    RegionL (bufL b (osSizes cfg) (d.ownQ cfg (qbpC cfg fs cert ps))) i := by
  obtain ⟨q, hq, h1, h2⟩ := h
  rw [osW, List.mem_singleton] at hq
  subst hq
  refine ⟨_, os_bufL_mem (ownQ_length _) (j := 8) (by rw [os_length_osSizes]; omega), ?_, ?_⟩
  · simp only at h1 ⊢; omega
  · have e : (d.ownQ cfg (qbpC cfg fs cert ps)).getD 8 [] = qbpC cfg fs cert ps := rfl
    rw [e, qbpC, os_length_segC]
    simp only [qbpSeg, List.length_map, List.length_range] at h2
    have := hlay.posFit l hl
    simp only at h2 ⊢; omega

/-- The point buffer's words. -/
theorem ownQ_getD_pt (Q : List E) : (d.ownQ cfg Q).getD (11 + 2 * cfg.levels.length + 1) [] = d.ptC cfg := by
  have lA : ([d.capsC cfg, d.flagsC cfg, d.fmsgC cfg, d.rootsC cfg, d.fchC cfg, d.betasC cfg, d.qwC cfg, d.qposC cfg,
      Q, d.oodzC cfg, d.oodC cfg] : List (List E)).length = 11 := rfl
  have lF : ((List.range cfg.levels.length).flatMap fun l => [d.sqzC cfg l, d.rewC cfg l]).length =
      2 * cfg.levels.length := by simp [List.length_flatMap, List.map_const']; ring
  unfold ownQ
  simp only [List.append_assoc]
  rw [← lA, ← lF, Nat.add_assoc, os_getD_skip, os_getD_skip]
  rfl

end OsData

/-- **The last level of the list.** -/
theorem os_lvsLast_eq (cfg : OsCfg) (xs : List E) : ∀ (Hs : List OsLvH) lvl cv p w osp roots, Hs ≠ [] →
    osLvsLast cfg xs lvl p roots Hs =
      (((osLvsList cfg xs lvl cv p w osp roots Hs).getLastD default).lvl,
        ((osLvsList cfg xs lvl cv p w osp roots Hs).getLastD default).p,
        ((osLvsList cfg xs lvl cv p w osp roots Hs).getLastD default).roots,
        ((osLvsList cfg xs lvl cv p w osp roots Hs).getLastD default).H)
  | [], _, _, _, _, _, _, h => absurd rfl h
  | [H], lvl, cv, p, w, osp, roots, _ => rfl
  | H :: H' :: Hs, lvl, cv, p, w, osp, roots, _ => by
    rw [osLvsLast, os_lvsLast_eq cfg xs (H' :: Hs) (lvl + 1) _ _ _ _ _ (by simp)]
    rfl

end
end LeanVM.Guest.B1
