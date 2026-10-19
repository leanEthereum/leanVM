/-
  LeanVM.Guest.B1.Whir.OsAsm2

  On a memory holding `open_stacked`'s buffers: each level's record, the residual chains' words,
  the residual's value's words.
-/

module

public import LeanVM.Guest.B1.Whir.OsAsm1

/-!
# The finish's words (TRIAGE #36)

`OsData.recOk`: each level's record (`osRecOf`) is what the buffers hold (`OsRecOk`);
`OsData.resFacts`: what each residual chain loop's iterations read; `OsData.ffFacts`:
`fold_final_msg`'s message and point.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.Main (MemL RegionL)
open LeanVM.Guest.B1.VerifySub

@[expose] public section

namespace OsData

variable {cfg : OsCfg} {d : OsData}

theorem qpos_at (hlay : OsLayoutOk cfg) {rd : Reader} {ptr : E} (hr : ReadsAt rd ptr (d.qposC cfg)) {l : ℕ}
    (hl : l < cfg.levels.length) {j : ℕ} (hj : j < (cfg.lv l).squeezes * (192 / (cfg.lv l).depth)) :
    LoadHolds rd ptr ((cfg.lv l).posOff + j) (eOfNat (osPosOf (cfg.lv l).depth (d.cv3 cfg l) j)) := by
  have h := os_seg_readsAt (n := cfg.levels.length) (off := fun l => (cfg.lv l).posOff)
    (c := fun l => (List.range ((cfg.lv l).squeezes * (192 / (cfg.lv l).depth))).map fun i =>
      eOfNat (osPosOf (cfg.lv l).depth (d.cv3 cfg l) i)) hr
    (fun a c hac hc => by simp only [List.length_map, List.length_range]; exact hlay.pos a c hac hc)
    (fun a ha => by simp only [List.length_map, List.length_range]; exact hlay.posFit a ha) hl
  have := h j (by simpa using hj)
  rw [loadHolds_mul_gen_pow] at this
  simpa using this

/-- **A level's record**, on a memory holding the buffers. -/
theorem recOk {μ r : ℕ} {Lall : List Whir.Level} (hok : OsCfgOk cfg μ r Lall) (hlay : OsLayoutOk cfg)
    {rd : Reader} {σ : Val} {b : ℕ} {Q : List E} (hbr : OsBufReads rd cfg d b Q) (hP : OsPtrsAt σ (osPtrsOf cfg b))
    {l : ℕ} (hl : l < cfg.levels.length) (hlv : (d.lv cfg l).lvl = l) :
    OsRecOk rd σ cfg l (osRecOf cfg d.xs (d.lv cfg l)) := by
  have hspec := hok.spec l (by rw [hok.len]; exact hl)
  obtain ⟨-, -, -, -, -, -, -, -, -, hqs, -⟩ := hspec
  unfold osRecOf
  rw [hlv]
  refine ⟨by simp [osHQs], fun j hj => ?_, fun j hj => ?_, by simp, fun h => ?_, fun z hz => ?_⟩
  · rw [hP.qpos]
    have := qpos_at hlay hbr.qpos hl (j := j) (by omega)
    unfold osHQs; rw [os_getD_map_range _ hj]; exact this
  · rw [hP.qw]; exact qw_at hlay hbr.qw hl j hj
  · have hy : l = cfg.yrLevel := by by_contra hy; simp [hy] at h
    rw [hP.betas]
    have := os_readsAt_getD hbr.betas (k := l) (by simp [betasC, hl])
    rw [betasC, os_getD_map_range _ hl, beta, ite_pos' hy] at this
    exact this
  · have hy : l ≠ cfg.yrLevel := by intro hy; simp [hy] at hz
    simp only [hy, ↓reduceIte, Option.some.injEq] at hz
    subst hz
    have hl1 : l + 1 < cfg.levels.length := by have := hok.yrLevel; omega
    refine ⟨?_, length_sqAll _ _, ?_, ?_⟩
    · rw [hP.betas]
      have := os_readsAt_getD hbr.betas (k := l) (by simp [betasC, hl])
      rw [betasC, os_getD_map_range _ hl, beta, ite_neg' hy] at this
      exact this
    · rw [hP.oodz]; exact oodz_readsAt hlay hbr.oodz hl1
    · rw [hP.ood]; exact (ood_at hbr.ood hl1).1

/-- **What a residual chain loop's iterations read.** -/
theorem resFacts {μ r : ℕ} {Lall : List Whir.Level} (hok : OsCfgOk cfg μ r Lall) (hlay : OsLayoutOk cfg) {rd : Reader} {b : ℕ} {Q : List E} (hbr : OsBufReads rd cfg d b Q) {l : ℕ}
    (hl : l < cfg.levels.length) :
    (∀ x < (cfg.lv l).queries, LoadHolds rd ((osPtrsOf cfg b).qpos * gen ^ x) (cfg.lv l).posOff
      ((d.qposC cfg).getD ((cfg.lv l).posOff + x) 0)) ∧
    (∀ t < (cfg.lv l).logCols, LoadHolds rd (osPtrAt cfg b (11 + 2 * cfg.levels.length + 2)) (l * 22 + t)
      (d.rowA cfg l t)) ∧
    (∀ t < (cfg.lv l).logCols, LoadHolds rd (osPtrAt cfg b (11 + 2 * cfg.levels.length + 3)) (l * 22 + t)
      (d.rowB cfg l t)) ∧
    (∀ x < (cfg.lv l).queries, LoadHolds rd (osPtrAt cfg b (11 + 2 * cfg.levels.length + 5 + l) * gen ^ x) 0
      (d.chain cfg l x)) ∧
    (∀ x < (cfg.lv l).queries, LoadHolds rd ((osPtrsOf cfg b).qw * gen ^ x) (l * cfg.maxQ) (d.lam cfg l ^ x)) ∧
    (∀ x < (cfg.lv l).queries, LoadHolds rd (osPtrAt cfg b (11 + 2 * cfg.levels.length + 5 + l) * gen ^ x) 1
      (d.chain cfg l x + d.lam cfg l ^ x * resProd (d.rowA cfg l) (d.rowB cfg l) (cfg.lv l).vals
        ((d.qposC cfg).getD ((cfg.lv l).posOff + x) 0) (cfg.lv l).logCols)) := by
  have hc22 := hlay.cols l hl
  have hqm := hlay.qw l hl
  have hrow : ∀ t < (cfg.lv l).logCols, l * 22 + t < cfg.levels.length * 22 := fun t ht => by
    have : l * 22 + 22 ≤ cfg.levels.length * 22 := by rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ hl
    omega
  have hposlen : ∀ x < (cfg.lv l).queries, (cfg.lv l).posOff + x < (d.qposC cfg).length := fun x hx => by
    rw [qposC, os_length_segC]
    have := hlay.posFit l hl
    obtain ⟨-, -, -, -, -, -, -, -, -, hqs, -⟩ := hok.spec l (by rw [hok.len]; exact hl)
    omega
  refine ⟨fun x hx => ?_, fun t ht => ?_, fun t ht => ?_, fun x hx => ?_, fun x hx => ?_, fun x hx => ?_⟩
  · rw [loadHolds_mul_gen_pow, Nat.add_comm x]
    exact os_readsAt_getD hbr.qpos (hposlen x hx)
  · exact os_readsAt_getD hbr.ba (by rw [baC, os_length_segC]; exact hrow t ht)
  · exact os_readsAt_getD hbr.bb (by rw [bbC, os_length_segC]; exact hrow t ht)
  · rw [loadHolds_mul_gen_pow, Nat.add_zero]
    have := os_readsAt_getD (hbr.chv l hl) (k := x) (by simp only [chvC, List.length_map, List.length_range]; omega)
    rwa [chvC, os_getD_map_range _ (by omega)] at this
  · rw [loadHolds_mul_gen_pow, Nat.add_comm x]; exact qw_at hlay hbr.qw hl x hx
  · rw [loadHolds_mul_gen_pow]
    have := os_readsAt_getD (hbr.chv l hl) (k := x + 1) (by simp only [chvC, List.length_map, List.length_range]; omega)
    rw [chvC, os_getD_map_range _ (by omega)] at this
    rw [show d.chain cfg l (x + 1) = _ from Finset.sum_range_succ _ x] at this
    exact this

/-- **The glued claims after the levels, one record per level.** -/
theorem glued_eq {μ r lane : ℕ} {Lall : List Whir.Level} (hok : OsCfgOk cfg μ r Lall) {e : WhirEnd} {sp' : St}
    {Q : List (ℕ × List (ℕ × Opening))} (hlen : d.Hs.length = cfg.levels.length)
    (hch : OsChain cfg μ lane d.xs Lall e sp' Q 0 d.cv0 2 (osW0 d.target d.xs) d.os (d.roots0 cfg) d.Hs) :
    (osLvsEnd cfg d.xs 0 d.cv0 2 (osW0 d.target d.xs) (d.roots0 cfg) d.Hs).2.2.glued =
      osGluedOf μ cfg ((d.lvs cfg).map (osRecOf cfg d.xs)) := by
  rw [os_chain_glued hok.spec hok.len d.Hs 0 _ _ _ _ _ (by omega) hch]
  rw [show (osW0 d.target d.xs).glued = [] from rfl, List.nil_append, osGluedOf]
  congr 1
  apply List.ext_getElem (by simp [lvs])
  intro i h1 h2
  simp only [List.getElem_map, List.getElem_zipIdx, Nat.zero_add]
  have := os_lvsList_lvl cfg d.xs d.Hs 0 d.cv0 2 (osW0 d.target d.xs) d.os (d.roots0 cfg) i (by simpa [lvs] using h2)
  simp only [Nat.zero_add] at this
  unfold lvs
  rw [this]

end OsData

end
end LeanVM.Guest.B1
