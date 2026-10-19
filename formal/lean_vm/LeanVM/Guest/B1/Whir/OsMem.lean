/-
  LeanVM.Guest.B1.Whir.OsMem

  On a memory holding `open_stacked`'s buffers at the allocator's pointers, each buffer's words.
-/

module

public import LeanVM.Guest.B1.Whir.OsLay

/-!
# The buffers on a memory (TRIAGE #36)

`os_bufReads`: a memory holding the buffers' honest words `ownQ` from `b` reads each at its
pointer `osPtrAt cfg b j` (`OsBufReads`).
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.Main (Layout MemL RegionL)

@[expose] public section

/-- What a memory holding the buffers reads at their pointers from `b`, the decoders' pointers
`Q`. -/
structure OsBufReads (rd : Reader) (cfg : OsCfg) (d : OsData) (b : ℕ) (Q : List E) : Prop where
  caps : ReadsAt rd (osPtrAt cfg b 0) (d.capsC cfg)
  flags : ReadsAt rd (osPtrAt cfg b 1) (d.flagsC cfg)
  fmsg : ReadsAt rd (osPtrAt cfg b 2) (d.fmsgC cfg)
  roots : ReadsAt rd (osPtrAt cfg b 3) (d.rootsC cfg)
  fch : ReadsAt rd (osPtrAt cfg b 4) (d.fchC cfg)
  betas : ReadsAt rd (osPtrAt cfg b 5) (d.betasC cfg)
  qw : ReadsAt rd (osPtrAt cfg b 6) (d.qwC cfg)
  qpos : ReadsAt rd (osPtrAt cfg b 7) (d.qposC cfg)
  qbp : ReadsAt rd (osPtrAt cfg b 8) Q
  oodz : ReadsAt rd (osPtrAt cfg b 9) (d.oodzC cfg)
  ood : ReadsAt rd (osPtrAt cfg b 10) (d.oodC cfg)
  sqz : ∀ l < cfg.levels.length, ReadsAt rd (osPtrAt cfg b (11 + 2 * l)) (d.sqzC cfg l)
  rew : ∀ l < cfg.levels.length, ReadsAt rd (osPtrAt cfg b (11 + 2 * l + 1)) (d.rewC cfg l)
  tch : ReadsAt rd (osPtrAt cfg b (11 + 2 * cfg.levels.length)) (d.tchC cfg)
  pt : ReadsAt rd (osPtrAt cfg b (11 + 2 * cfg.levels.length + 1)) (d.ptC cfg)
  ba : ReadsAt rd (osPtrAt cfg b (11 + 2 * cfg.levels.length + 2)) (d.baC cfg)
  bb : ReadsAt rd (osPtrAt cfg b (11 + 2 * cfg.levels.length + 3)) (d.bbC cfg)
  ich : ReadsAt rd (osPtrAt cfg b (11 + 2 * cfg.levels.length + 4)) (d.ichC cfg)
  chv : ∀ l < cfg.levels.length, ReadsAt rd (osPtrAt cfg b (11 + 2 * cfg.levels.length + 5 + l)) (d.chvC cfg l)

theorem os_flatMap_pair_getD {α : Type} (f g : ℕ → α) (x : α) :
    ∀ n l, l < n → ((List.range n).flatMap fun i => [f i, g i]).getD (2 * l) x = f l ∧
      ((List.range n).flatMap fun i => [f i, g i]).getD (2 * l + 1) x = g l
  | 0, _, h => absurd h (by omega)
  | n + 1, l, h => by
    have hlen : ((List.range n).flatMap fun i => [f i, g i]).length = 2 * n := by
      simp [List.length_flatMap, List.map_const']; ring
    rw [List.range_succ, List.flatMap_append]
    by_cases hl : l < n
    · rw [oq_getD_app_lt (by omega), oq_getD_app_lt (by omega)]
      exact os_flatMap_pair_getD f g x n l hl
    · obtain rfl : l = n := by omega
      rw [oq_getD_app_ge (by omega), oq_getD_app_ge (by omega), hlen]
      simp

theorem os_getD_skip {α : Type} (l l' : List α) (n : ℕ) (x : α) :
    (l ++ l').getD (l.length + n) x = l'.getD n x := by
  rw [oq_getD_app_ge (by omega), Nat.add_sub_cancel_left]

/-- A memory holding a function's buffers reads buffer `j` at its pointer. -/
theorem os_memL_bufL {rd : Reader} {b : ℕ} {sizes : List ℕ} {own : List (List E)}
    (hm : MemL rd (bufL b sizes own)) (hl : own.length = sizes.length) {j : ℕ} (hj : j < sizes.length) :
    ReadsAt rd (ofK (gpow ((bases b sizes).getD j 0))) (own.getD j []) := by
  have hb : (bases b sizes).length = sizes.length := os_length_bases b sizes
  have hmem : ((bases b sizes).getD j 0, own.getD j []) ∈ bufL b sizes own := by
    unfold bufL
    rw [List.getD_eq_getElem _ _ (by omega), List.getD_eq_getElem _ _ (by omega)]
    exact List.mem_iff_getElem.mpr ⟨j, by simp; omega, by simp⟩
  exact hm _ hmem

/-- **The buffers on a memory holding them.** -/
theorem os_bufReads {rd : Reader} {cfg : OsCfg} {d : OsData} {b : ℕ} {Q : List E}
    (hm : MemL rd (bufL b (osSizes cfg) (d.ownQ cfg Q))) : OsBufReads rd cfg d b Q := by
  set n := cfg.levels.length with hn
  set A : List (List E) := [d.capsC cfg, d.flagsC cfg, d.fmsgC cfg, d.rootsC cfg, d.fchC cfg, d.betasC cfg,
    d.qwC cfg, d.qposC cfg, Q, d.oodzC cfg, d.oodC cfg] with hA
  set F : List (List E) := (List.range n).flatMap fun l => [d.sqzC cfg l, d.rewC cfg l] with hF
  set T : List (List E) := [d.tchC cfg, d.ptC cfg, d.baC cfg, d.bbC cfg, d.ichC cfg] with hT
  set M : List (List E) := (List.range n).map (d.chvC cfg) with hM
  have lA : A.length = 11 := rfl
  have lF : F.length = 2 * n := by
    simp [hF, List.length_flatMap, List.map_const']; ring
  have lT : T.length = 5 := rfl
  have lM : M.length = n := by simp [hM]
  have hown : d.ownQ cfg Q = A ++ (F ++ (T ++ M)) := by
    simp only [OsData.ownQ, List.append_assoc]; rfl
  have hS := os_length_osSizes cfg
  have hl : (d.ownQ cfg Q).length = (osSizes cfg).length := by
    rw [hown, hS]; simp only [List.length_append, lA, lF, lT, lM]; omega
  have R : ∀ j, j < 11 + 2 * n + 5 + n → ReadsAt rd (osPtrAt cfg b j) ((d.ownQ cfg Q).getD j []) := fun j hj =>
    os_memL_bufL hm hl (by rw [hS]; exact hj)
  have gA : ∀ j < 11, ReadsAt rd (osPtrAt cfg b j) (A.getD j []) := fun j hj => by
    have := R j (by omega)
    rwa [hown, oq_getD_app_lt (by rw [lA]; exact hj)] at this
  have gF : ∀ l < n, ReadsAt rd (osPtrAt cfg b (11 + 2 * l)) (d.sqzC cfg l) ∧
      ReadsAt rd (osPtrAt cfg b (11 + 2 * l + 1)) (d.rewC cfg l) := fun l hl' => by
    have h1 := R (11 + 2 * l) (by omega)
    have h2 := R (11 + 2 * l + 1) (by omega)
    have e := os_flatMap_pair_getD (fun i => d.sqzC cfg i) (fun i => d.rewC cfg i) [] n l hl'
    rw [hown, ← lA, os_getD_skip, oq_getD_app_lt (by rw [lF]; omega)] at h1
    rw [hown, ← lA, Nat.add_assoc, os_getD_skip, oq_getD_app_lt (by rw [lF]; omega)] at h2
    exact ⟨by rw [← e.1]; exact h1, by rw [← e.2]; exact h2⟩
  have gT : ∀ k < 5, ReadsAt rd (osPtrAt cfg b (11 + 2 * n + k)) (T.getD k []) := fun k hk => by
    have := R (11 + 2 * n + k) (by omega)
    have e : (d.ownQ cfg Q).getD (11 + 2 * n + k) [] = T.getD k [] := by
      rw [hown, ← lA, ← lF, Nat.add_assoc, os_getD_skip, os_getD_skip, oq_getD_app_lt (by rw [lT]; exact hk)]
    rw [e] at this
    exact this
  have gM : ∀ l < n, ReadsAt rd (osPtrAt cfg b (11 + 2 * n + 5 + l)) (d.chvC cfg l) := fun l hl' => by
    have := R (11 + 2 * n + 5 + l) (by omega)
    have e : (d.ownQ cfg Q).getD (11 + 2 * n + 5 + l) [] = d.chvC cfg l := by
      rw [hown, ← lA, ← lF, ← lT, Nat.add_assoc, Nat.add_assoc, os_getD_skip, os_getD_skip, os_getD_skip]
      simp [hM, List.getD_eq_getElem?_getD, hl']
    rw [e] at this
    exact this
  exact ⟨gA 0 (by omega), gA 1 (by omega), gA 2 (by omega), gA 3 (by omega), gA 4 (by omega), gA 5 (by omega),
    gA 6 (by omega), gA 7 (by omega), gA 8 (by omega), gA 9 (by omega), gA 10 (by omega),
    fun l hl' => (gF l hl').1, fun l hl' => (gF l hl').2, gT 0 (by omega), gT 1 (by omega), gT 2 (by omega),
    gT 3 (by omega), gT 4 (by omega), gM⟩

/-- Level `l`'s squeeze run's buffer's words. -/
theorem os_ownQ_getD_sqz {cfg : OsCfg} {d : OsData} {Q : List E} {l : ℕ} (hl : l < cfg.levels.length) :
    (d.ownQ cfg Q).getD (11 + 2 * l) [] = d.sqzC cfg l := by
  have lA : ([d.capsC cfg, d.flagsC cfg, d.fmsgC cfg, d.rootsC cfg, d.fchC cfg, d.betasC cfg, d.qwC cfg, d.qposC cfg,
      Q, d.oodzC cfg, d.oodC cfg] : List (List E)).length = 11 := rfl
  have lF : ((List.range cfg.levels.length).flatMap fun l => [d.sqzC cfg l, d.rewC cfg l]).length =
      2 * cfg.levels.length := by simp [List.length_flatMap, List.map_const']; ring
  unfold OsData.ownQ
  simp only [List.append_assoc]
  rw [← lA, os_getD_skip, oq_getD_app_lt (by rw [lF]; omega)]
  exact (os_flatMap_pair_getD _ _ _ _ l hl).1

end
end LeanVM.Guest.B1
