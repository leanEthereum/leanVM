/-
  LeanVM.Guest.B1.VsC.Os.LeftLpAt

  A level's `level_positions` call in `open_stacked`'s node, and `query_win_ptrs`' words.
-/

module

public import LeanVM.Guest.B1.VsC.Os.LeftLqAt
public import LeanVM.Guest.B1.VsC.LpComplete

/-!
# A level's `level_positions` call in the node, and the window pointers

`osLpF al c l cc j`: level `l`'s decoder `j`'s run, `level_positions` placed at the cursor `cc`
(`lpDqFrame` past the decoder's `cert dq (.n 5)`).

`HonRun.lpEntry_os`: level `l`'s `level_positions` (`lpA_b2c`, in `lpTable` by `HonRun.lpOk_os`)
completes placed at `OsHelperVals`' arguments and returns, on the window tables, the buffers
(`OsMemA`, the positions `posW` wrote) and its window pointers at the level's offset of
`query_win_ptrs`; it claims its decoders' runs and its `Out` is their words, which
`HonRun.lqEntry_os` reads.

`osWq al c lpc`: `query_win_ptrs`' words, level `l`'s `level_positions` at the cursor `lpc l`:
entry `posOff + k` of level `l` is `ptrAt (osLpF al c l (lpc l) (k / P) + k % P * qwN d cd)`
(`osWq_at`, the levels' segments disjoint by `HonStatic.pos`). `osWords_qbp`: a memory holding
the node's words holds them at `query_win_ptrs`.
-/

namespace LeanVM.Guest.B1.VsC

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.B1
open LeanVM.Guest.Complete LeanVM.Guest.Value LeanVM.Guest.B1.Whir LeanVM.Protocol LeanVM.Protocol.Verifier

@[expose] public section

/-- Level `l`'s decoder `j`'s run, its `level_positions` placed at the cursor `cc`. -/
noncomputable def osLpF (al : String → Bool) (c : OsCfg) (l cc j : ℕ) : ℕ :=
  lpDqFrame B2C.fs al (dqwName (osLvA c l).depth (osLvA c l).capDepth) (lpLoopOf (osPositionsName (osLvA c l)))
    (osLvA c l).squeezes cc j + B2C.cert (dqwName (osLvA c l).depth (osLvA c l).capDepth) (.n 5)

/-- An arm's levels' squeeze counts in `level_positions`' range. -/
def OsLpRegOk (m : ℕ) : Bool :=
  (List.range 4).all fun ri => (osCfgR m ri).levels.all fun lv => decide (1 ≤ lv.squeezes) && decide (lv.squeezes < 2 ^ 20)

set_option maxRecDepth 100000 in
theorem osLpRegOk_all : (List.range 15).all OsLpRegOk = true := by decide +kernel

theorem osLpReg {m ri l : ℕ} (hm : m < 15) (hri : ri < 4) (hl : l < (osCfgR m ri).levels.length) :
    1 ≤ (osLvA (osCfgR m ri) l).squeezes ∧ (osLvA (osCfgR m ri) l).squeezes < 2 ^ 20 := by
  have h := List.all_eq_true.mp osLpRegOk_all m (List.mem_range.mpr hm)
  simp only [OsLpRegOk, List.all_eq_true, List.mem_range, Bool.and_eq_true, decide_eq_true_eq] at h
  have hmem : (osCfgR m ri).levels.getD l default ∈ (osCfgR m ri).levels := by
    rw [List.getD_eq_getElem _ _ hl]; exact List.getElem_mem hl
  exact h ri hri _ hmem

/-! ## `query_win_ptrs`' words -/

theorem find?_range_eq {p : ℕ → Bool} {l : ℕ} (hp : p l = true) (hq : ∀ l' < l, p l' = false) :
    ∀ n, l < n → (List.range n).find? p = some l
  | 0, h => absurd h (Nat.not_lt_zero _)
  | n + 1, h => by
    rw [List.range_succ, List.find?_append]
    by_cases hl : l < n
    · rw [find?_range_eq hp hq n hl]
      rfl
    · have e : l = n := by omega
      subst e
      have h0 : (List.range l).find? p = none :=
        List.find?_eq_none.mpr fun x hx => by simp [hq x (List.mem_range.mp hx)]
      rw [h0]
      simp [hp]

/-- Level `l`'s segment of `query_positions` and `query_win_ptrs`. -/
def osSeg (c : OsCfg) (l i : ℕ) : Bool :=
  decide ((osLvA c l).posOff ≤ i ∧ i < (osLvA c l).posOff + (osLvA c l).squeezes * sqPer (osLvA c l))

/-- Entry `i` of `query_win_ptrs`: in level `l`'s segment, its query's window pointer. -/
noncomputable def osWqAt (al : String → Bool) (c : OsCfg) (lpc : ℕ → ℕ) (i : ℕ) : E :=
  ((List.range c.levels.length).find? fun l => osSeg c l i).elim 0 fun l =>
    ptrAt (osLpF al c l (lpc l) ((i - (osLvA c l).posOff) / sqPer (osLvA c l)) +
      (i - (osLvA c l).posOff) % sqPer (osLvA c l) * qwN (osLvA c l).depth (osLvA c l).capDepth)

/-- **`query_win_ptrs`' words**, level `l`'s `level_positions` at the cursor `lpc l`. -/
noncomputable def osWq (al : String → Bool) (c : OsCfg) (lpc : ℕ → ℕ) : List E :=
  (List.range (osPosTotal c)).map (osWqAt al c lpc)

theorem osWq_length (al : String → Bool) (c : OsCfg) (lpc : ℕ → ℕ) : (osWq al c lpc).length = osPosTotal c := by
  simp [osWq]

/-- **Level `l`'s window pointers in `query_win_ptrs`.** -/
theorem osWq_at {al : String → Bool} {c : OsCfg} (hS : HonStatic c) (lpc : ℕ → ℕ) {l k : ℕ}
    (hl : l < c.levels.length) (hk : k < (osLvA c l).squeezes * sqPer (osLvA c l)) :
    ∃ h : (osLvA c l).posOff + k < (osWq al c lpc).length, (osWq al c lpc)[(osLvA c l).posOff + k]'h =
      ptrAt (osLpF al c l (lpc l) (k / sqPer (osLvA c l)) + k % sqPer (osLvA c l) *
        qwN (osLvA c l).depth (osLvA c l).capDepth) := by
  obtain ⟨hlt, htop⟩ := chain_disj (a := fun l => (osLvA c l).posOff)
    (w := fun l => (osLvA c l).squeezes * sqPer (osLvA c l)) hS.pos
  have htl : (osLvA c l).posOff + (osLvA c l).squeezes * sqPer (osLvA c l) ≤ osPosTotal c := htop l hl
  have hb : (osLvA c l).posOff + k < osPosTotal c := by omega
  refine ⟨by rw [osWq_length]; exact hb, ?_⟩
  simp only [osWq, List.getElem_map, List.getElem_range]
  have hf : (List.range c.levels.length).find? (fun l' => osSeg c l' ((osLvA c l).posOff + k)) = some l := by
    refine find?_range_eq ?_ (fun l' hl' => ?_) _ hl
    · simp only [osSeg, decide_eq_true_eq]
      omega
    · have h3 : (osLvA c l').posOff + (osLvA c l').squeezes * sqPer (osLvA c l') ≤ (osLvA c l).posOff :=
        hlt l' l (by omega) hl hl'
      simp only [osSeg, decide_eq_false_iff_not, not_and, not_lt]
      omega
  simp only [osWqAt, hf, Option.elim_some, Nat.add_sub_cancel_left]

/-- **A memory holding `open_stacked`'s words holds `wq` at `query_win_ptrs`.** -/
theorem osWords_qbp {c : OsCfg} {b : ℕ} {own : List (List E)} {wq : List E} {rd : Reader}
    (hown : List.Forall₂ (fun w s ↦ w.length = s) own (osSizesL c)) (hq : osIxQbpA < (osSizesL c).length)
    (h : HoldsWords rd (osWords c b own wq)) : ReadsAt rd (osPtrA c b osIxQbpA) wq := by
  have h1 : ReadsAt rd (ofK (addressOfIndex ((bases b (osSizesL c)).getD osIxQbpA 0))) ((osOwnW own wq).getD osIxQbpA []) :=
    h ((bases b (osSizesL c)).getD osIxQbpA 0, (osOwnW own wq).getD osIxQbpA [])
      (List.mem_map.mpr ⟨osIxQbpA, List.mem_range.mpr hq, rfl⟩)
  have hol : osIxQbpA < own.length := by rw [hown.length_eq]; exact hq
  have e : (osOwnW own wq).getD osIxQbpA [] = wq := by
    rw [osOwnW, List.getD_eq_getElem?_getD, List.getElem?_set_self hol, Option.getD_some]
  rw [e] at h1
  exact h1

/-- **Level `l`'s window pointers on a memory holding `query_win_ptrs`' words.** -/
theorem osWq_loads {al : String → Bool} {c : OsCfg} (hS : HonStatic c) (lpc : ℕ → ℕ) {b : ℕ} {rd : Reader}
    (h : ReadsAt rd (osPtrA c b osIxQbpA) (osWq al c lpc)) {l : ℕ} (hl : l < c.levels.length) :
    ∀ k < (osLvA c l).squeezes * sqPer (osLvA c l), LoadHolds rd (osPtrA c b osIxQbpA * gen ^ (osLvA c l).posOff) k
      (ptrAt (osLpF al c l (lpc l) (k / sqPer (osLvA c l)) + k % sqPer (osLvA c l) *
        qwN (osLvA c l).depth (osLvA c l).capDepth)) := by
  intro k hk
  obtain ⟨hb, he⟩ := osWq_at (al := al) hS lpc hl hk
  rw [loadHolds_mul_gen_pow, ← he]
  exact h _ hb

end
end LeanVM.Guest.B1.VsC

namespace LeanVM.Guest.B1.Whir.HonRun

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest LeanVM.Guest.B1 LeanVM.Guest.B1.VsC
open LeanVM.Guest.Memory LeanVM.Guest.Complete LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

variable {μ r : ℕ} {target : E} {S : KeccakState} {root : Digest} {xs : List E}
  {os : List (List Opening)} {w : WhirEnd} {cfg : List Whir.Level} {Ls : List LvAt}
  (hR : HonRun μ r target S root xs os w cfg Ls)
include hR

set_option hygiene false in
local notation "CC" => osCfgR (μ - minOpenLog) (r - 1)

set_option hygiene false in
local notation "LV" => osLvA (osCfgR (μ - minOpenLog) (r - 1)) l

set_option hygiene false in
local notation "HH" => hR.osHonest (cur := cur) (tabs := tabs)

/-- **Level `l`'s `level_positions` specialization is in `lpTable`.** -/
theorem lpOk_os {l : ℕ} (hl : l < (CC).levels.length) : LpOk (LV) := by
  have hy := hR.yr
  by_cases hlt : l < (CC).yrLevel
  · obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, h, -⟩ := hR.mid hlt
    exact h
  · have he : l = (CC).yrLevel := by omega
    subst he
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, h, -⟩ := hR.fin
    exact h

/-- **Level `l`'s `level_positions` in `open_stacked`'s node**: at the helpers' honest values
(the buffers at `b`, the window tables at `it`), on a region holding the buffers and the tables,
on every memory holding the tables, the buffers and the level's window pointers, it completes
placed, claiming its decoders' runs and holding their words. -/
theorem lpEntry_os {cur tabs : E} {al : String → Bool} (kd : ℕ) (hkd : 7 ≤ kd) {l : ℕ}
    (hl : l < (CC).levels.length) (b it : ℕ) (Rg : ℕ → Prop)
    (hRb : ∀ j < (osSizesL CC).length, ∀ i < (osSizesL CC).getD j 0, Rg ((bases b (osSizesL CC)).getD j 0 + i))
    (hRt : ∀ n < 2 ^ winTabBits, Rg (it + n)) (fp cc : ℕ) (hfc : fp + B2C.fs (osPositionsName (LV)) ≤ cc) :
    ∃ e, (∀ F, (∀ f, B2C.fs f ≤ F) → e ≤ cc + ((LV).squeezes + 1) * (3 * F + 64)) ∧ CallAtA B2C.fs al B2C.cert kd (osPositionsName (LV))
      (((HH).D l).w0 :: ((HH).D l).capL ++ [osPtrA CC b osIxQposA * gen ^ (LV).posOff,
        osPtrA CC b osIxQbpA * gen ^ (LV).posOff, ptrAt it, gen ^ (LV).squeezes])
      ((⟨((HH).D l).capL, []⟩ : Fs).squeezeN ((LV).squeezes - 1)).2.cap Rg
      (fun i => ∃ j < (LV).squeezes, osLpF al CC l cc j ≤ i ∧
        i < osLpF al CC l cc j + 128 / (LV).depth * qwN (LV).depth (LV).capDepth)
      (fun rd => ∀ j < (LV).squeezes, ReadsAt rd (ptrAt (osLpF al CC l cc j))
        (qwRunList (LV).depth (LV).capDepth (sqSample ((HH).D l).w0 ((HH).D l).capL j)))
      (fun rd => WinTabs rd (ptrAt it) ∧ OsMemA rd CC b (HH).own ∧
        ∀ k < (LV).squeezes * sqPer (LV), LoadHolds rd (osPtrA CC b osIxQbpA * gen ^ (LV).posOff) k
          (ptrAt (osLpF al CC l cc (k / sqPer (LV)) + k % sqPer (LV) * qwN (LV).depth (LV).capDepth)))
      PostQuiet (B2C.fs (osPositionsName (LV))) fp cc e := by
  have hm := hR.m11
  have hr := hR.r4
  obtain ⟨hS1, hS20⟩ := osLpReg hm hr hl
  obtain ⟨-, -, -, hpt, hqpos, hqbp, -, hqbpl⟩ := osLqReg hm hr hl
  obtain ⟨hP, -, -⟩ := osPos_le hm hr hl
  have hS := honStatic_all _ _ hm hr
  have hqpl : osIxQposA < (osSizesL CC).length := by rw [hS.len]; simp only [osIxQposA]; omega
  have hA : LpAE B2C.fs al B2C.cert kd (osPositionsName (LV)) (lpLoopOf (osPositionsName (LV)))
      (dqwName (LV).depth (LV).capDepth) (LV).depth (LV).capDepth := lpAE_b2c al kd _ (hR.lpOk_os hl).1
  have e3 : osPtrA CC b osIxQposA * gen ^ (LV).posOff = ptrAt ((bases b (osSizesL CC)).getD osIxQposA 0 + (LV).posOff) :=
    ptrAt_mul_gen _ _
  have e4 : osPtrA CC b osIxQbpA * gen ^ (LV).posOff = ptrAt ((bases b (osSizesL CC)).getD osIxQbpA 0 + (LV).posOff) :=
    ptrAt_mul_gen _ _
  obtain ⟨e, hbe, he⟩ := hA (LV).squeezes ((HH).D l).w0 ((HH).D l).capL
    ((bases b (osSizesL CC)).getD osIxQposA 0 + (LV).posOff) ((bases b (osSizesL CC)).getD osIxQbpA 0 + (LV).posOff) it
    Rg hS1 hS20 ((HH).capL_len l hl) hkd
    (fun k hk => by rw [Nat.add_assoc]; exact hRb _ hqpl _ (by rw [hqpos]; omega))
    (fun k hk => by rw [Nat.add_assoc]; exact hRb _ hqbpl _ (by rw [hqbp]; omega)) hRt fp cc hfc
  rw [← e3, ← e4] at he
  refine ⟨e, fun F hF => le_trans hbe (Nat.add_le_add_left (Nat.mul_le_mul_left _ (by
    have := hF (dqwName (LV).depth (LV).capDepth); have := hF (lpLoopOf (osPositionsName (LV)))
    have := hF (tailKey (lpLoopOf (osPositionsName (LV)))); omega)) _),
    he.mono (fun _ h => h) (fun _ h => h) (fun _ h => h) (fun rd hp => ?_) (fun _ _ _ h => h)⟩
  obtain ⟨hw, hmem, hptr⟩ := hp
  refine ⟨hw, fun k hk => ?_, fun k hk => ?_⟩
  · simp only [List.length_map, List.length_range] at hk
    simp only [List.getElem_map, List.getElem_range]
    have hk1 : k / (128 / (LV).depth) < (LV).squeezes := (Nat.div_lt_iff_lt_mul hP).mpr hk
    have hpw := (HH).posW l hl (k / (128 / (LV).depth)) hk1 (k % (128 / (LV).depth)) (Nat.mod_lt _ hP)
    rw [show (LV).posOff + k / osPerA CC l * osPerA CC l + k % osPerA CC l = (LV).posOff + k by
      rw [Nat.add_assoc, Nat.div_add_mod']] at hpw
    have h10 := hmem osIxQposA hqpl (by decide)
    have hlen10 : (osOwnA (HH).own osIxQposA).length = osPosTotal CC :=
      (forall₂_getD (HH).own_len osIxQposA).trans hqpos
    have hb : (LV).posOff + k < (osOwnA (HH).own osIxQposA).length := by rw [hlen10]; omega
    have h := h10 _ hb
    rw [← List.getD_eq_getElem _ 0 hb] at h
    unfold osOwnA at h hpw
    rw [hpw] at h
    exact (loadHolds_mul_gen_pow rd _ _ _ _).mpr h
  · simp only [List.length_map, List.length_range] at hk
    simp only [List.getElem_map, List.getElem_range]
    exact hptr k hk

end
end LeanVM.Guest.B1.Whir.HonRun
