/-
  LeanVM.Guest.B1.VsC.Os.LeftLqAt

  A level's `level_queries` call in `open_stacked`'s node: at the helpers' honest values, reading
  the node's buffers and its `level_positions` decoders' windows.
-/

module

public import LeanVM.Guest.B1.VsC.Os.LeftLqMem

/-!
# A level's `level_queries` call in the node

`OsLqRegOk`: at every arm, rate and level, what `level_queries` reads lies in `open_stacked`'s
buffers (the rounds in `coefs`, the final coefficients in the final lane, the positions and
pointers in `query_positions` and `query_win_ptrs`) and its windows of `qwN d cd` words in the
decoders' runs (one kernel decision, `osLqReg`).

`HonRun.lqEntry_os`: level `l`'s `level_queries` completes placed at `OsHelperVals`' arguments and
returns (the buffers at `b`), on a region holding the buffers and the decoders' runs at `F j`, on
every memory holding the buffers (`OsMemA`), query `k`'s window pointer `lqWp d cd F k` at the
level's offset of `query_win_ptrs`, and decoder `j`'s run at `F j`; its pops the level's Merkle
hints stream by stream.
-/

namespace LeanVM.Guest.B1.VsC

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.B1
open LeanVM.Guest.Complete LeanVM.Guest.Value LeanVM.Guest.B1.Whir LeanVM.Protocol LeanVM.Protocol.Verifier

@[expose] public section

/-- What an arm's levels' `level_queries` read fits the buffers and the decoders' runs. -/
def OsLqRegOk (m : ℕ) : Bool :=
  (List.range 4).all fun ri => (List.range (osCfgR m ri).levels.length).all fun l =>
    decide (2 * ((osLvA (osCfgR m ri) l).foldsOff + (oqSA (osCfgR m ri) l).folds) ≤
        (osSizesL (osCfgR m ri)).getD osIxCoefsA 0) &&
      ((oqSA (osCfgR m ri) l).final != 1 ||
        decide ((oqSA (osCfgR m ri) l).nHs ≤ (osSizesL (osCfgR m ri)).getD (osIxLaneA (osCfgR m ri)) 0)) &&
      decide (oqNpw (oqSA (osCfgR m ri) l) + 2 = qwN (osLvA (osCfgR m ri) l).depth (osLvA (osCfgR m ri) l).capDepth) &&
      decide ((osLvA (osCfgR m ri) l).posOff + (osLvA (osCfgR m ri) l).squeezes * (128 / (osLvA (osCfgR m ri) l).depth) ≤
        osPosTotal (osCfgR m ri)) &&
      decide ((osSizesL (osCfgR m ri)).getD osIxQposA 0 = osPosTotal (osCfgR m ri)) &&
      decide ((osSizesL (osCfgR m ri)).getD osIxQbpA 0 = osPosTotal (osCfgR m ri)) &&
      decide (osIxLaneA (osCfgR m ri) < (osSizesL (osCfgR m ri)).length) &&
      decide (osIxQbpA < (osSizesL (osCfgR m ri)).length)

set_option maxRecDepth 100000 in
theorem osLqRegOk_all : (List.range 15).all OsLqRegOk = true := by decide +kernel

/-- **What a level's `level_queries` reads fits the buffers and the decoders' runs.** -/
theorem osLqReg {m ri l : ℕ} (hm : m < 15) (hri : ri < 4) (hl : l < (osCfgR m ri).levels.length) :
    2 * ((osLvA (osCfgR m ri) l).foldsOff + (oqSA (osCfgR m ri) l).folds) ≤
        (osSizesL (osCfgR m ri)).getD osIxCoefsA 0 ∧
      ((oqSA (osCfgR m ri) l).final = 1 →
        (oqSA (osCfgR m ri) l).nHs ≤ (osSizesL (osCfgR m ri)).getD (osIxLaneA (osCfgR m ri)) 0) ∧
      oqNpw (oqSA (osCfgR m ri) l) + 2 = qwN (osLvA (osCfgR m ri) l).depth (osLvA (osCfgR m ri) l).capDepth ∧
      (osLvA (osCfgR m ri) l).posOff + (osLvA (osCfgR m ri) l).squeezes * (128 / (osLvA (osCfgR m ri) l).depth) ≤
        osPosTotal (osCfgR m ri) ∧
      (osSizesL (osCfgR m ri)).getD osIxQposA 0 = osPosTotal (osCfgR m ri) ∧
      (osSizesL (osCfgR m ri)).getD osIxQbpA 0 = osPosTotal (osCfgR m ri) ∧
      osIxLaneA (osCfgR m ri) < (osSizesL (osCfgR m ri)).length ∧ osIxQbpA < (osSizesL (osCfgR m ri)).length := by
  have h := List.all_eq_true.mp osLqRegOk_all m (List.mem_range.mpr hm)
  simp only [OsLqRegOk, List.all_eq_true, List.mem_range, Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true,
    bne_iff_ne, ne_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩ := h ri hri l hl
  exact ⟨h1, fun hf => h2.resolve_left (not_not.mpr hf), h3, h4, h5, h6, h7, h8⟩

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

/-- **Level `l`'s `level_queries` in `open_stacked`'s node**: at the helpers' honest values
(`OsHelperVals`, the buffers at `b`), on a region holding the buffers and the decoders' runs at
`F j`, on every memory holding the buffers, the level's window pointers `lqWp d cd F k` at its
offset of `query_win_ptrs` and the decoders' runs, it completes placed, its pops the level's Merkle
hints stream by stream. -/
theorem lqEntry_os {cur tabs : E} {fs : String → ℕ} {al : String → Bool} {cert : String → V → ℕ} (kd : ℕ) {l : ℕ}
    (hl : l < (CC).levels.length) (b : ℕ) (F : ℕ → ℕ) (Rg : ℕ → Prop)
    (hRb : ∀ j < (osSizesL CC).length, ∀ i < (osSizesL CC).getD j 0, Rg ((bases b (osSizesL CC)).getD j 0 + i))
    (hRw : ∀ j < (LV).squeezes, ∀ i < 128 / (LV).depth * qwN (LV).depth (LV).capDepth, Rg (F j + i))
    (fp cc : ℕ) (hfc : fp + fs (osQueriesName CC l LV) ≤ cc) :
    ∃ e, (∀ F, (∀ f, fs f ≤ F) → e ≤ cc + ((LV).queries + 2) * (3 * F + 2048)) ∧ CallAtA fs al cert kd (osQueriesName CC l LV)
      [if l = (CC).yrLevel then 0 else ((HH).D l).lam, if l = (CC).yrLevel then 0 else ((HH).D l).lamInv,
        osPtrA CC b osIxCoefsA * gen ^ (2 * (LV).foldsOff), osHsPtrA CC b l,
        osPtrA CC b osIxQposA * gen ^ (LV).posOff, osPtrA CC b osIxQbpA * gen ^ (LV).posOff]
      [(osRootA (HH).own l).1, (osRootA (HH).own l).2, ((HH).D l).batched,
        (if l = (CC).yrLevel then 0 else ((HH).D l).lam) ^ (LV).queries] Rg
      (fun _ => False) (fun _ => True)
      (fun rd => OsMemA rd CC b (HH).own ∧
        (∀ k < (LV).queries, LoadHolds rd (osPtrA CC b osIxQbpA * gen ^ (LV).posOff) k
          (ptrAt (lqWp (LV).depth (LV).capDepth F k))) ∧
        ∀ j < (LV).squeezes, ReadsAt rd (ptrAt (F j))
          (qwRunList (LV).depth (LV).capDepth (sqSample ((HH).D l).w0 ((HH).D l).capL j)))
      (fun rd t => SameStreams (t.pops coreProgram rd)
          (Hints.levelHints (l == 0) (LV).depth (os.getD l []).length (os.getD l [])) ∧
        t.Every (ExactAt coreProgram rd))
      (fs (osQueriesName CC l LV)) fp cc e := by
  have hm := hR.m11
  have hr := hR.r4
  have hS := honStatic_all _ _ hm hr
  obtain ⟨hcf, hnh, hnpw, hpt, hqpos, hqbp, hlane, hqbpl⟩ := osLqReg hm hr hl
  obtain ⟨hP, hqS, -⟩ := osPos_le hm hr hl
  obtain ⟨-, hpd, -, hcdd, -⟩ := hR.cdpd hl
  have hpd' : (oqSA CC l).pd + (LV).capDepth = (LV).depth := by
    simp only [osLvA] at hpd hcdd ⊢
    omega
  have hlen := hS.len
  have hcfl : osIxCoefsA < (osSizesL CC).length := by rw [hlen]; simp only [osIxCoefsA]; omega
  have hqpl : osIxQposA < (osSizesL CC).length := by rw [hlen]; simp only [osIxQposA]; omega
  have hhsl : osIxHsA < (osSizesL CC).length := by rw [hlen]; simp only [osIxHsA]; omega
  obtain ⟨hql, hqo⟩ := hR.qs_os (cur := cur) (tabs := tabs) hl
  have hqq : oqQA CC l = (LV).queries := hql.symm.trans (hR.phase_len_os hl)
  set lam' : E := if l = (CC).yrLevel then 0 else ((HH).D l).lam
  set li' : E := if l = (CC).yrLevel then 0 else ((HH).D l).lamInv with hli'
  set B : ℕ → ℕ := fun j => (bases b (osSizesL CC)).getD j 0
  set icf := B osIxCoefsA + 2 * (LV).foldsOff
  set ihs := (if l = (CC).yrLevel then B (osIxLaneA CC) else B osIxHsA + l * hsStride) with hihs
  set ipos := B osIxQposA + (LV).posOff
  set iptr := B osIxQbpA + (LV).posOff
  set wp := lqWp (LV).depth (LV).capDepth F
  have e1 : osPtrA CC b osIxCoefsA * gen ^ (2 * (LV).foldsOff) = ptrAt icf := ptrAt_mul_gen _ _
  have e2 : osHsPtrA CC b l = ptrAt ihs := by
    unfold osHsPtrA
    rw [hihs]
    split_ifs
    · rfl
    · exact ptrAt_mul_gen _ _
  have e3 : osPtrA CC b osIxQposA * gen ^ (LV).posOff = ptrAt ipos := ptrAt_mul_gen _ _
  have e4 : osPtrA CC b osIxQbpA * gen ^ (LV).posOff = ptrAt iptr := ptrAt_mul_gen _ _
  have hreg : (lqCall lam' ((hdOf μ r Ls).root l) (LV).depth (oqSA CC l).pd (os.getD l [])
      ((HH).rounds l) ((HH).hsv l) wp icf ihs ipos iptr).Reg (LV).queries (oqSA CC l) Rg := by
    refine ⟨fun off ho => ?_, fun hf off ho => ?_, fun k hk off ho => ?_, fun k hk => ⟨?_, ?_⟩⟩
    · change Rg (B osIxCoefsA + 2 * (LV).foldsOff + off)
      rw [Nat.add_assoc]
      exact hRb _ hcfl _ (by omega)
    · have hy := (hR.final_iff hl).1 hf
      change Rg (ihs + off)
      rw [hihs]
      simp only [hy, ↓reduceIte]
      exact hRb _ hlane _ (by have := hnh hf; omega)
    · change Rg (lqWp (LV).depth (LV).capDepth F k + off)
      unfold lqWp
      have hk1 : k / (128 / (LV).depth) < (LV).squeezes := (Nat.div_lt_iff_lt_mul hP).mpr (lt_of_lt_of_le hk hqS)
      have hm1 : k % (128 / (LV).depth) + 1 ≤ 128 / (LV).depth := Nat.mod_lt _ hP
      have hlt : k % (128 / (LV).depth) * qwN (LV).depth (LV).capDepth + off < 128 / (LV).depth * qwN (LV).depth (LV).capDepth :=
        calc k % (128 / (LV).depth) * qwN (LV).depth (LV).capDepth + off
            < (k % (128 / (LV).depth) + 1) * qwN (LV).depth (LV).capDepth := by rw [Nat.add_one_mul]; omega
          _ ≤ 128 / (LV).depth * qwN (LV).depth (LV).capDepth := Nat.mul_le_mul_right _ hm1
      rw [Nat.add_assoc]
      exact hRw _ hk1 _ hlt
    · change Rg (B osIxQposA + (LV).posOff + k)
      rw [Nat.add_assoc]
      exact hRb _ hqpl _ (by rw [hqpos]; omega)
    · change Rg (B osIxQbpA + (LV).posOff + k)
      rw [Nat.add_assoc]
      exact hRb _ hqbpl _ (by rw [hqbp]; omega)
  obtain ⟨e, hbe, he⟩ := hR.lqAt_os (cur := cur) (tabs := tabs) (fs := fs) (al := al) (cert := cert) kd hl lam' li' wp
    icf ihs ipos iptr Rg hreg fp cc hfc
  have hmret := hR.lqMret_os (cur := cur) (tabs := tabs) hl lam' li' wp icf ihs ipos iptr
    (fun hne => by rw [hli']; simp only [hne, ↓reduceIte])
  rw [hmret, ← (hR.lqCapOk_os (cur := cur) (tabs := tabs) hl).2] at he
  rw [← e1, ← e2, ← e3, ← e4] at he
  refine ⟨e, hbe, he.mono (fun _ h => h) (fun _ h => h) (fun _ h => h) (fun rd hp => ?_) (fun _ _ _ h => h)⟩
  obtain ⟨hmem, hptr, hwin⟩ := hp
  have hq := (HH).qMem b rd hmem l hl
  rw [e1, e2] at hq
  have hpos := hR.lqPos_os (cur := cur) (tabs := tabs) hl hmem
  rw [e3] at hpos
  rw [e4] at hptr
  refine ⟨hq.1, hq.2, fun k hk => ⟨hpos k hk, hptr k hk, ?_⟩⟩
  · intro i hi
    rw [hpd'] at hi ⊢
    have hk' : k < oqQA CC l := by rw [hqq]; exact hk
    have hk1 : k / (128 / (LV).depth) < (LV).squeezes := (Nat.div_lt_iff_lt_mul hP).mpr (lt_of_lt_of_le hk hqS)
    have h := lqWin_of_runs hwin hk1 hP i hi
    have hws : (lqWs (oqSA CC l).pd (os.getD l []) k).1 =
        qwPosOf (LV).depth (sqSample ((HH).D l).w0 ((HH).D l).capL (k / (128 / (LV).depth))) (k % (128 / (LV).depth)) := by
      change (opAt (os.getD l []) k).leafIndex = _
      rw [opAt, ← hqo k hk', (HH).qs_eq l hl k hk']
    change LoadHolds rd (ptrAt (wp k)) i (gen ^ qwVal (LV).depth (LV).capDepth (lqWs (oqSA CC l).pd (os.getD l []) k).1 i)
    rw [hws]
    exact h

end
end LeanVM.Guest.B1.Whir.HonRun
