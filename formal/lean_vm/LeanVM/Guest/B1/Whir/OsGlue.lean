/-
  LeanVM.Guest.B1.Whir.OsGlue

  The levels of a run of the stacked opening, as a list: indices, roots, consecutive levels.
-/

module

public import LeanVM.Guest.B1.Whir.OsMem

/-!
# The levels' list (TRIAGE #36)

`os_lvs_get`: a level is the list's entry at its index; `os_chain_next`: along a run, a level
before the last has the next one after it in the list, its roots one longer, the new root the
level's; `OsData.rt_succ`: the next level's root has the scalars the level reads.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.VerifySub

@[expose] public section

/-- **A level is the list's entry at its index.** -/
theorem os_lvs_get (cfg : OsCfg) (xs : List E) (Hs : List OsLvH) (cv : Digest) (p : ℕ) (w : WhirState)
    (osp : List Opening) (roots : List (Digest × ℕ × ℕ)) :
    ∀ L ∈ osLvsList cfg xs 0 cv p w osp roots Hs,
      (osLvsList cfg xs 0 cv p w osp roots Hs).getD L.lvl default = L ∧
        L.lvl < (osLvsList cfg xs 0 cv p w osp roots Hs).length := by
  intro L hL
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hL
  have e := os_lvsList_lvl cfg xs Hs 0 cv p w osp roots i hi
  rw [e, Nat.zero_add, List.getD_eq_getElem _ _ hi]
  exact ⟨rfl, hi⟩

/-- **The next level along a run.** -/
theorem os_chain_next {cfg : OsCfg} {μ lane : ℕ} {xs : List E} {Lall : List Whir.Level} {e : WhirEnd}
    {sp' : St} {Q : List (ℕ × List (ℕ × Opening))} : ∀ (Hs : List OsLvH) lvl cv p w osp roots,
      OsChain cfg μ lane xs Lall e sp' Q lvl cv p w osp roots Hs → roots.length = lvl + 1 →
      ∀ L ∈ osLvsList cfg xs lvl cv p w osp roots Hs, L.roots.length = L.lvl + 1 ∧
        (L.lvl ≠ cfg.yrLevel → ∃ L' ∈ osLvsList cfg xs lvl cv p w osp roots Hs, L'.lvl = L.lvl + 1 ∧
          L'.roots = L.roots ++ [(L.H.root, (cfg.lv (L.lvl + 1)).depth, 3 * 2 ^ (cfg.lv (L.lvl + 1)).folds)])
  | [], _, _, _, _, _, _, h, _ => h.elim
  | H :: Hs, lvl, cv, p, w, osp, roots, h, hr => by
    obtain ⟨-, -, hl, hn⟩ := h
    intro L hL
    simp only [osLvsList, List.mem_cons] at hL
    rcases hL with rfl | hL
    · refine ⟨hr, fun hy => ?_⟩
      have hch := hn hy
      cases Hs with
      | nil => exact hch.elim
      | cons H' Hs' =>
        refine ⟨⟨lvl + 1, osHCvEnd cfg lvl xs p H.cv1, osHPEnd cfg lvl p, osHWEnd cfg lvl xs p H, H.osq,
          osHRootsEnd cfg lvl roots H, H'⟩, List.mem_cons_of_mem _ (by simp [osLvsList]), rfl, ?_⟩
        show osHRootsEnd cfg lvl roots H = _
        rw [osHRootsEnd, ite_neg' hy]
    · by_cases hy : lvl = cfg.yrLevel
      · obtain ⟨rfl, -⟩ := hl hy
        simp [osLvsList] at hL
      · have ih := os_chain_next Hs _ _ _ _ _ _ (hn hy) (by rw [osHRootsEnd, ite_neg' hy]; simp [hr]) L hL
        refine ⟨ih.1, fun hy' => ?_⟩
        obtain ⟨L', hL', h1, h2⟩ := ih.2 hy'
        exact ⟨L', List.mem_cons_of_mem _ hL', h1, h2⟩

namespace OsData

variable {cfg : OsCfg} {d : OsData}

theorem lv_mem {l : ℕ} (hl : l < d.Hs.length) : d.lv cfg l ∈ d.lvs cfg ∧ (d.lv cfg l).lvl = l := by
  have hlen : (d.lvs cfg).length = d.Hs.length := os_lvsList_length cfg d.xs d.Hs 0 _ _ _ _ _
  unfold lv
  rw [List.getD_eq_getElem _ _ (by omega)]
  refine ⟨List.getElem_mem _, ?_⟩
  have := os_lvsList_lvl cfg d.xs d.Hs 0 d.cv0 2 (osW0 d.target d.xs) d.os (d.roots0 cfg) l (by unfold lvs at hlen; omega)
  simp only [Nat.zero_add] at this
  exact this

/-- **Level `0`'s root is the commitment's.** -/
theorem rt_zero (hn : d.Hs ≠ []) : d.rt cfg 0 = d.root := by
  cases h : d.Hs with
  | nil => exact absurd h hn
  | cons H Hs => simp [rt, lv, lvs, h, osLvsList, roots0]

/-- **The next level's root has the scalars the level reads.** -/
theorem rt_succ {μ lane : ℕ} {Lall : List Whir.Level} {e : WhirEnd} {sp' : St}
    {Q : List (ℕ × List (ℕ × Opening))}
    (hch : OsChain cfg μ lane d.xs Lall e sp' Q 0 d.cv0 2 (osW0 d.target d.xs) d.os (d.roots0 cfg) d.Hs)
    (hyr : cfg.yrLevel = d.Hs.length - 1) {l : ℕ} (hl : l + 1 < d.Hs.length) :
    digestScalars (d.rt cfg (l + 1)) = (osHW cfg l d.xs (d.lv cfg l).p 0, osHW cfg l d.xs (d.lv cfg l).p 1) := by
  obtain ⟨hm, hlv⟩ := lv_mem (cfg := cfg) (d := d) (l := l) (by omega)
  have hy : (d.lv cfg l).lvl ≠ cfg.yrLevel := by rw [hlv]; omega
  obtain ⟨hlen, hnx⟩ := os_chain_next d.Hs 0 _ _ _ _ _ hch rfl _ hm
  obtain ⟨L', hL', h1, h2⟩ := hnx hy
  obtain ⟨hg, -⟩ := os_lvs_get cfg d.xs d.Hs _ _ _ _ _ L' hL'
  have hL'e : d.lv cfg (l + 1) = L' := by
    unfold lv lvs; rw [← hlv, ← h1]; exact hg
  have hok := (os_chain_mem d.Hs 0 _ _ _ _ _ hch _ hm).ok
  have hr := hok.root hy
  rw [hlv] at hr
  unfold rt
  rw [hL'e, h2, hlv, List.getD_eq_getElem _ _ (by simp; omega), List.getElem_append_right (by omega)]
  simp only [hlen, hlv, Nat.sub_self, List.getElem_cons_zero]
  exact digestScalars_digestOfScalars hr

end OsData

end
end LeanVM.Guest.B1
