/-
  LeanVM.Guest.B1.Whir.OsGlued

  The claims a run of the stacked opening glues, as `osGluedOf` of one record per level.
-/

module

public import LeanVM.Guest.B1.Whir.OsBodyMemOf

/-!
# The glued claims (TRIAGE #36)

`os_chain_glued`: along a run, the state after the levels glues each level's record
(`osRecOf`: its batching challenge, its positions, its out-of-domain point but at the last level),
`osGluedOf` of them at level `0`.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.VerifySub

@[expose] public section

theorem os_foldRounds_glued : ∀ {n : ℕ} {w : WhirState} {lf : List E} {s : St} {res : WhirState × List E}
    {s' : St}, Runs (foldRounds n w lf) s res s' → res.1.glued = w.glued
  | 0, w, lf, s, res, s', h => by
    obtain ⟨rfl, -⟩ := os_inv_pure h
    rfl
  | n + 1, w, lf, s, res, s', h => by
    simp only [foldRounds] at h
    obtain ⟨ch, s1, -, h2⟩ := os_inv_bind h
    obtain ⟨q, s2, -, h4⟩ := os_inv_bind h2
    have := os_foldRounds_glued h4
    exact this

/-- A level's record. -/
def osRecOf (cfg : OsCfg) (xs : List E) (L : OsLvP) : OsRec :=
  ⟨osHLam cfg L.lvl xs L.p L.H.cv1, osHQs cfg L.lvl xs L.p L.H.cv1,
    if L.lvl = cfg.yrLevel then none
    else some (sqAll (cfg.lv L.lvl).logCols (osHCv12 cfg L.lvl xs L.p L.H.cv1)).1⟩

/-- **The glued claims along a run.** -/
theorem os_chain_glued {cfg : OsCfg} {μ lane : ℕ} {xs : List E} {Lall : List Whir.Level} {e : WhirEnd}
    {sp' : St} {Q : List (ℕ × List (ℕ × Opening))}
    (hspec : ∀ i < Lall.length, LvSpec cfg μ i (Lall.getD i default) (Lall.drop (i + 1)))
    (hlen : Lall.length = cfg.levels.length) : ∀ (Hs : List OsLvH) lvl cv p w osp roots,
      lvl + Hs.length ≤ cfg.levels.length →
      OsChain cfg μ lane xs Lall e sp' Q lvl cv p w osp roots Hs →
      (osLvsEnd cfg xs lvl cv p w roots Hs).2.2.glued =
        w.glued ++ ((osLvsList cfg xs lvl cv p w osp roots Hs).map fun L =>
          osRecGlued μ (osLevelF cfg L.lvl) (osRecOf cfg xs L)).flatten
  | [], _, _, _, _, _, _, _, h => h.elim
  | H :: Hs, lvl, cv, p, w, osp, roots, hle, h => by
    obtain ⟨hok, -, hl, hn⟩ := h
    simp only [List.length_cons] at hle
    have hs := hspec lvl (by rw [hlen]; omega)
    obtain ⟨-, -, -, -, -, hlc, -⟩ := hs
    have hg1 : H.w1.glued = w.glued := os_foldRounds_glued hok.folds
    have hF : H.w1.folds.length = osLevelF cfg lvl := hok.w1len
    have hstep : (osHWEnd cfg lvl xs p H).glued = w.glued ++ osRecGlued μ (osLevelF cfg lvl)
        (osRecOf cfg xs ⟨lvl, cv, p, w, osp, roots, H⟩) := by
      unfold osHWEnd osHPending osRecOf osRecGlued
      simp only
      by_cases hy : lvl = cfg.yrLevel
      · simp only [ite_pos' hy, List.nil_append, os_glue_one]
        rw [hg1, hF, hlc]
      · simp only [ite_neg' hy, List.singleton_append, os_glue_two]
        rw [hg1, hF, hlc, List.append_assoc]
        rfl
    by_cases hy : lvl = cfg.yrLevel
    · obtain ⟨rfl, -⟩ := hl hy
      show (osHWEnd cfg lvl xs p H).glued = _
      rw [hstep]
      simp [osLvsList]
    · have ih := os_chain_glued hspec hlen Hs _ _ _ _ _ _ (by omega) (hn hy)
      show (osLvsEnd cfg xs (lvl + 1) _ _ (osHWEnd cfg lvl xs p H) _ Hs).2.2.glued = _
      rw [ih, hstep]
      simp [osLvsList, List.append_assoc]

/-- **The head's pointers and sizes** at its honest values. -/
theorem os_head_sig {cfg : OsCfg} {fs0 fs1 target r0 r1 cur : E} {cv : Digest} {x0 x1 : E} {P : OsPtrs} {σ : Val}
    (hv : ∀ j < 61, σ (.n j) = (osHeadVals cfg fs0 fs1 target r0 r1 cur cv x0 x1 P).getD j 0) :
    OsPtrsAt σ P ∧ ∀ i < 11, σ (.n (39 + 2 * i)) = osGw ((osHeadSizes cfg).getD i 0) ∧
      σ (.n (40 + 2 * i)) = (osPtrList P).getD i 0 := by
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, fun i hi => ?_⟩
  all_goals first
    | (rw [hv _ (by decide)]; rfl)
    | skip
  interval_cases i <;> exact ⟨by rw [hv _ (by decide)]; rfl, by rw [hv _ (by decide)]; rfl⟩

/-- **The run facts the memory facts use**, from the levels' data along a run. -/
theorem OsData.runOk_of {cfg : OsCfg} {d : OsData} {μ r lane : ℕ} {Lall : List Whir.Level} (hok : OsCfgOk cfg μ r Lall)
    {e : WhirEnd} {sp' : St} {Q : List (ℕ × List (ℕ × Opening))} (hlen : d.Hs.length = cfg.levels.length)
    (hch : OsChain cfg μ lane d.xs Lall e sp' Q 0 d.cv0 2 (osW0 d.target d.xs) d.os (d.roots0 cfg) d.Hs)
    (hchst : d.chst.length = cfg.yrLog - 1) : d.RunOk cfg := by
  have hn := hok.len2
  refine ⟨hlen, fun l hl => ?_, OsData.rt_zero (by intro h; rw [h] at hlen; simp at hlen; omega),
    fun l hl => OsData.rt_succ hch (by rw [hlen]; exact hok.yrLevel) (by omega), hchst, OsData.fch_len hok hch,
    fun l hl j hj => OsData.fch_eq hch (by omega) hj⟩
  obtain ⟨hm, hlv⟩ := OsData.lv_mem (cfg := cfg) (d := d) (l := l) (by omega)
  have hok' := (os_chain_mem d.Hs 0 _ _ _ _ _ hch _ hm).ok
  rw [hlv] at hok'
  exact hok'.chs.2

end
end LeanVM.Guest.B1
