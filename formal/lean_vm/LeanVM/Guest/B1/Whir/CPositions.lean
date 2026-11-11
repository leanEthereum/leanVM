/-
  LeanVM.Guest.B1.Whir.CPositions

  A level's query positions, honestly: the dispatch into `level_positions`, then the batching
  challenge.
-/

module

public import LeanVM.Guest.B1.Whir.CFold
public import LeanVM.Guest.B1.Whir.Squeezes

/-!
# A level's positions, honestly

`osPositions_complete`: the level's slots of `query_positions` and `query_win_ptrs` materialized,
the dispatch on the rate into `level_positions` holding of the carried capacity and returning the
capacity `last` its squeezes leave (`DispC`), the capacity copied, the zero run allocated at its
first use, and the batching challenge squeezed from `last` with nothing waiting (`SqzOut`).
-/

namespace LeanVM.Guest.B1.Whir

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest LeanVM.Guest.B1
open LeanVM.Guest.Value LeanVM.Protocol LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

variable {C : CallRel} {rd : Reader}

/-- What a level's positions leave: the challenge's capacity carried, the challenge, the zero
run allocated, the materializations. -/
structure SqzOut (σ : Val) (st st' : OsSt) (F : Fs) : Prop where
  fsv : st'.fsv σ = F.squeeze.2.cap
  lam : σ (.n (st'.k - 1)) = F.squeeze.1
  pad : PadOk σ st'.pad
  padSome : ∃ p, st'.pad = some p ∧ p + 4 < st'.k
  fs : st'.fs.length = 5
  can : AllCanonical (st'.fsv σ)
  below : st'.Below
  cb : st'.cb = st.cb
  co : st'.co = st.co
  w0 : st'.w0 = st.w0
  w1 : st'.w1 = st.w1
  k : st.k ≤ st'.k
  mats : MatsOk σ st'.mats
  matsB : MatsBelow st'.k st'.mats

/-- The zero run's values a level allocates: five at the first use, none after. -/
def padLenOf (st : OsSt) : ℕ := if st.pad = none then 5 else 0

/-- The values a materialization at the offset `off` writes. -/
def matLen (off : ℕ) : ℕ := if off = 0 then 0 else 2

/-- The positions' values, by segments. -/
def posSegs (c : OsCfg) (lv : OsLv) (st : OsSt) (σ : Val) (last : List E) : List (ℕ × (ℕ → E)) :=
  let m1 := osMatsAfter c.plan st.mats osQpos lv.posOff st.k
  let S := (⟨last, []⟩ : Fs).perm
  [(matLen lv.posOff, fun i ↦ [gw (osMatSD c.plan st.mats osQpos lv.posOff).2,
      σ (.n osQpos) * gw lv.posOff].getD i 0),
    (matLen lv.posOff, fun i ↦ [gw (osMatSD c.plan m1 osQbp lv.posOff).2,
      σ (.n osQbp) * gw lv.posOff].getD i 0),
    (5, fun i ↦ last.getD i 0), (5, fun i ↦ last.getD i 0),
    (padLenOf st, fun i ↦ [word 1 0 0, word 0 0 0, word 0 0 0, word 0 0 0, word 0 0 0].getD i 0),
    (13, cells13F S), (7, challengeVals (cells13F S 0) (cells13F S 1))]

theorem osMatP_k' (plan : List (ℕ × ℕ × ℕ)) (mats : List OsMat) (base off k : ℕ) :
    (osMatP plan mats base off k).2.2 = k + matLen off := by
  rw [osMatP_k, matLen]; split_ifs <;> rfl

/-- **A level's positions, honestly.** -/
theorem osPositions_complete {c : OsCfg} {lvl : ℕ} {lv : OsLv} {st : OsSt} (σ : Val) {R : E}
    (hR : σ (.n osRate) = R) (hfs : st.fs.length = 5) (hb : st.Below) (hk : 161 ≤ st.k)
    (hpad : PadOk σ st.pad)
    (hpk : ∀ p, st.pad = some p → p + 4 < st.k) (hmo : MatsOk σ st.mats)
    (hmob : MatsBelow st.k st.mats) (hpo : lv.posOff < u128Bound)
    {last : List E} (hll : last.length = 5) (hlc : AllCanonical last)
    (hD : DispC C rd R ((c.lvAt lvl).map osPositionsName)
      (st.fsv σ ++ [σ (.n osQpos) * gen ^ lv.posOff, σ (.n osQbp) * gen ^ lv.posOff, σ (.n osWin)])
      last) :
    BlkF C rd σ st.k (osPositions c lvl lv st).2.k
      (fun i ↦ segLookup (posSegs c lv st σ last) (i - st.k)) (osPositions c lvl lv st).1
      (fun σ' ↦ SqzOut σ' st (osPositions c lvl lv st).2 ⟨last, []⟩ ∧ AgreeBelow st.k σ σ') := by
  obtain ⟨f0, f1, f2, f3, f4, hf⟩ := fold_args st hfs
  set k := st.k with hkdef
  set P := c.plan
  set ml := matLen lv.posOff with hml
  set m1 := osMatsAfter P st.mats osQpos lv.posOff k with hm1
  set m2 := osMatsAfter P m1 osQbp lv.posOff (osMatP P st.mats osQpos lv.posOff k).2.2 with hm2
  set qp := osMatP P st.mats osQpos lv.posOff k with hqp
  set wq := osMatP P m1 osQbp lv.posOff qp.2.2 with hwq
  have hqk : qp.2.2 = k + ml := osMatP_k' _ _ _ _ _
  have hwk : wq.2.2 = k + ml + ml := by rw [hwq, osMatP_k', hqk]
  set S := (⟨last, []⟩ : Fs).perm with hS
  set segs := posSegs c lv st σ last with hsegs
  set padLen := padLenOf st with hpl
  set pd := osPad st.pad (wq.2.2 + 10) with hpdd
  have hpd : pd.2.2 = wq.2.2 + 10 + padLen := by rw [hpdd, hpl, padLenOf]; cases st.pad <;> rfl
  have hk' : (osPositions c lvl lv st).2.k = wq.2.2 + 10 + padLen + 20 := by
    show pd.2.2 + 20 = _; rw [hpd]
  have hlen : segLen segs = 2 * ml + 30 + padLen := by
    simp only [hsegs, posSegs, segLen, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      ← hpl, ← hml]
    omega
  intro σ' ha hv
  have HV : ∀ i < segLen segs, σ' (.n (k + i)) = segLookup segs i := fun i hi ↦ by
    rw [hv _ (by omega) (by rw [hk', hwk]; omega)]
    show segLookup segs (k + i - k) = _
    rw [Nat.add_sub_cancel_left]
  have sv := seg_val HV
  have hagree : ∀ i < k, σ' (.n i) = σ (.n i) := ha
  have hfl : ∀ f ∈ st.fs, f < k := hb.fs
  rw [hf] at hfl
  simp only [List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp, forall_eq] at hfl
  have hfsv : st.fsv σ = [σ (.n f0), σ (.n f1), σ (.n f2), σ (.n f3), σ (.n f4)] := by
    simp [OsSt.fsv, hf]
  have hL7 : segs.length = 7 := by simp [hsegs, posSegs]
  -- the materializations
  have hmo' : MatsOk σ' st.mats := matsOk_agree hmo hmob hagree
  have hq := osMatP_complete (C := C) (rd := rd) (plan := P) (mats := st.mats) (base := osQpos)
    (off := lv.posOff) (k := k) hpo hmo' (hagree _ (by unfold osQpos; omega)) (fun i h1 h2 ↦ by
      rw [← hqp, hqk] at h2
      have := sv 0 (by omega) 0 (by simp [segLen]) (i - k)
        (by simp only [hsegs, posSegs, List.getElem_cons_zero]; omega)
      rw [show k + 0 + (i - k) = i by omega] at this
      rw [this]
      simp only [hsegs, posSegs, List.getElem_cons_zero, matPVal]
      have hml2 : ml ≤ 2 := by rw [hml, matLen]; split_ifs <;> omega
      split_ifs with hik
      · rw [hik, Nat.sub_self]; rfl
      · rw [show i - k = 1 by omega]; rfl)
  have hmo1 : MatsOk σ' m1 := osMatsAfter_ok hmo' hpo hq.1
  have hml2 : ml ≤ 2 := by rw [hml, matLen]; split_ifs <;> omega
  have hmob1 : MatsBelow (k + 2) m1 :=
    matsBelow_after hmob (by unfold osQpos; omega) (by omega) (by omega)
  have hw := osMatP_complete (C := C) (rd := rd) (plan := P) (mats := m1) (base := osQbp)
    (off := lv.posOff) (k := qp.2.2) hpo hmo1 (hagree _ (by unfold osQbp; omega)) (fun i h1 h2 ↦ by
      rw [← hwq, hwk] at h2
      rw [hqk] at h1
      have := sv 1 (by omega) ml (by simp [hsegs, posSegs, segLen, ← hml]) (i - (k + ml))
        (by simp only [hsegs, posSegs, List.getElem_cons_succ, List.getElem_cons_zero]; omega)
      rw [show k + ml + (i - (k + ml)) = i by omega] at this
      rw [this, hqk]
      simp only [hsegs, posSegs, List.getElem_cons_succ, List.getElem_cons_zero, matPVal]
      split_ifs with hik
      · rw [hik, Nat.sub_self]; rfl
      · rw [show i - (k + ml) = 1 by omega]; rfl)
  have hmo2 : MatsOk σ' m2 := osMatsAfter_ok hmo1 hpo hw.1
  have hmob2 : MatsBelow (k + 4) m2 :=
    matsBelow_after hmob1 (by unfold osQbp; omega) (by omega) (by rw [hqk]; omega)
  -- the dispatch's returns and their copies
  have vr : ∀ i < 5, σ' (.n (wq.2.2 + i)) = last.getD i 0 := fun i hi ↦ by
    have := sv 2 (by omega) (2 * ml) (by simp [hsegs, posSegs, segLen, ← hml]; omega) i
      (by simp [hsegs, posSegs]; omega)
    rw [hwk, show k + ml + ml + i = k + 2 * ml + i by ring, this]
    simp [hsegs, posSegs]
  have vc : ∀ i < 5, σ' (.n (wq.2.2 + 5 + i)) = last.getD i 0 := fun i hi ↦ by
    have := sv 3 (by omega) (2 * ml + 5) (by simp [hsegs, posSegs, segLen, ← hml]; omega) i
      (by simp [hsegs, posSegs]; omega)
    rw [hwk, show k + ml + ml + 5 + i = k + (2 * ml + 5) + i by ring, this]
    simp [hsegs, posSegs]
  have vp : ∀ i < padLen, σ' (.n (wq.2.2 + 10 + i)) = [word 1 0 0, word 0 0 0, word 0 0 0, word 0 0 0,
      word 0 0 0].getD i 0 := fun i hi ↦ by
    have := sv 4 (by omega) (2 * ml + 10) (by simp [hsegs, posSegs, segLen, ← hml]; omega) i
      (by simp [hsegs, posSegs, ← hpl]; omega)
    rw [hwk, show k + ml + ml + 10 + i = k + (2 * ml + 10) + i by ring, this]
    simp [hsegs, posSegs]
  have vk : ∀ c < 13, σ' (.n (pd.2.2 + c)) = cells13F S c := fun c hc ↦ by
    have := sv 5 (by omega) (2 * ml + 10 + padLen)
      (by simp [hsegs, posSegs, segLen, ← hml, ← hpl]; omega) c (by simp [hsegs, posSegs]; omega)
    rw [hpd, hwk, show k + ml + ml + 10 + padLen + c = k + (2 * ml + 10 + padLen) + c by ring,
      this]
    simp [hsegs, posSegs, hS]
  have vch : ∀ i < 7, σ' (.n (pd.2.2 + 13 + i)) = challengeVals (cells13F S 0) (cells13F S 1) i :=
    fun i hi ↦ by
      have := sv 6 (by omega) (2 * ml + 23 + padLen)
        (by simp [hsegs, posSegs, segLen, ← hml, ← hpl]; omega) i (by simp [hsegs, posSegs]; omega)
      rw [hpd, hwk, show k + ml + ml + 10 + padLen + 13 + i = k + (2 * ml + 23 + padLen) + i by
        ring, this]
      simp [hsegs, posSegs, hS]
  -- the zero run
  have hpz : PadOk σ' (some pd.2.1) ∧ AllOk C rd σ' pd.1 ∧ pd.2.1 + 4 < pd.2.2 + 20 := by
    rw [hpdd]
    cases hp : st.pad with
    | none =>
      have hpl5 : padLen = 5 := by rw [hpl, padLenOf, hp]; rfl
      have p0 := vp 0 (by omega); have p1 := vp 1 (by omega); have p2 := vp 2 (by omega)
      have p3 := vp 3 (by omega); have p4 := vp 4 (by omega)
      simp only [List.getD_cons_zero, List.getD_cons_succ, Nat.add_zero] at p0 p1 p2 p3 p4
      refine ⟨⟨by simpa [osPad, word_zero] using p1, by simpa [osPad, word_zero] using p2,
        by simpa [osPad, word_zero] using p3, by simpa [osPad, word_zero] using p4⟩, ?_, by simp [osPad]⟩
      simp only [osPad, allOk_cons, allOk_nil, and_true, StmtOk, Atom.Holds]
      exact ⟨p0, by simpa using p1, by simpa using p2, by simpa using p3, by simpa using p4⟩
    | some p =>
      rw [hp] at hpad
      have hpk' := hpk p hp
      obtain ⟨z1, z2, z3, z4⟩ := hpad
      refine ⟨⟨show σ' (.n (p + 1)) = 0 by rw [hagree (p + 1) (by omega)]; exact z1,
        show σ' (.n (p + 2)) = 0 by rw [hagree (p + 2) (by omega)]; exact z2,
        show σ' (.n (p + 3)) = 0 by rw [hagree (p + 3) (by omega)]; exact z3,
        show σ' (.n (p + 4)) = 0 by rw [hagree (p + 4) (by omega)]; exact z4⟩, allOk_nil, ?_⟩
      simp [osPad]; omega
  -- the squeeze
  obtain ⟨l0, l1, l2, l3, l4, hl5⟩ : ∃ l0 l1 l2 l3 l4, last = [l0, l1, l2, l3, l4] := by
    match last, hll with
    | [l0, l1, l2, l3, l4], _ => exact ⟨l0, l1, l2, l3, l4, rfl⟩
  have hcm : last = [wq.2.2 + 5, wq.2.2 + 6, wq.2.2 + 7, wq.2.2 + 8, wq.2.2 + 9].map fun i ↦ σ' (.n i) := by
    have e0 := vc 0 (by omega); have e1 := vc 1 (by omega); have e2 := vc 2 (by omega)
    have e3 := vc 3 (by omega); have e4 := vc 4 (by omega)
    rw [hl5] at e0 e1 e2 e3 e4 ⊢
    simp only [List.getD_cons_zero, List.getD_cons_succ, Nat.add_zero, Nat.add_assoc,
      Nat.reduceAdd] at e0 e1 e2 e3 e4
    simp only [List.map_cons, List.map_nil, e0, e1, e2, e3, e4]
  have hSF : (⟨[wq.2.2 + 5, wq.2.2 + 6, wq.2.2 + 7, wq.2.2 + 8, wq.2.2 + 9].map fun i ↦ σ' (.n i), []⟩ : Fs).perm = S := by
    rw [← hcm]
  have hsq := osSqueeze0_complete (C := C) (rd := rd) (σ := σ') (p := pd.2.1)
    (cap := [wq.2.2 + 5, wq.2.2 + 6, wq.2.2 + 7, wq.2.2 + 8, wq.2.2 + 9]) (j := pd.2.2) rfl hpz.1
    (by rw [← hcm]; exact hlc) (fun c hc ↦ by rw [hSF]; exact vk c hc)
    (fun i hi ↦ by
      rw [vch i hi]
      have e0 := vk 0 (by omega)
      rw [Nat.add_zero] at e0
      rw [e0, vk 1 (by omega)])
  rw [hSF] at hsq
  have hfsT : ([pd.2.2 + 8, pd.2.2 + 9, pd.2.2 + 10, pd.2.2 + 11, pd.2.2 + 12].map
      fun i ↦ σ' (.n i)) = (⟨last, []⟩ : Fs).squeeze.2.cap := by
    simp only [List.map_cons, List.map_nil, Fs.squeeze, capOf]
    rw [vk 8 (by omega), vk 9 (by omega), vk 10 (by omega), vk 11 (by omega), vk 12 (by omega)]
    simp [cells13F, hS]
  have hcan' : AllCanonical ((osPositions c lvl lv st).2.fsv σ') := by
    show AllCanonical ([pd.2.2 + 8, pd.2.2 + 9, pd.2.2 + 10, pd.2.2 + 11, pd.2.2 + 12].map
      fun i ↦ σ' (.n i))
    rw [hfsT]; exact capOf_canonical _
  have hkk : k ≤ (osPositions c lvl lv st).2.k := by rw [hk']; omega
  have hR' : σ' (.n osRate) = R := by rw [hagree _ (by unfold osRate; omega), hR]
  refine ⟨?_, ⟨hfsT, ?_, hpz.1, ⟨pd.2.1, rfl, hpz.2.2⟩, rfl, hcan', ?_, rfl, rfl, rfl, rfl, hkk,
    hmo2, matsBelow_mono hmob2 (by rw [hk']; omega)⟩, ha⟩
  · simp only [osPositions, allOk_append]
    refine ⟨⟨⟨⟨⟨hq.1, hw.1⟩, ?_⟩, ?_⟩, hpz.2.1⟩, hsq.1⟩
    · rw [allOk_cons]
      refine ⟨hD σ' hR' _ _ ?_ ?_, allOk_nil⟩
      · rw [hf]
        simp only [List.cons_append, List.nil_append, List.map_cons, List.map_nil]
        rw [hagree _ hfl.1, hagree _ hfl.2.1, hagree _ hfl.2.2.1, hagree _ hfl.2.2.2.1,
          hagree _ hfl.2.2.2.2, hq.2, hw.2, hagree _ (by unfold osWin; omega), hfsv]
        rfl
      · have hrv : (osRun wq.2.2 5).map σ' = last := by
          refine List.ext_getElem (by simp [osRun, hll]) fun i h1 h2 ↦ ?_
          simp only [osRun, List.getElem_map, List.getElem_range]
          rw [vr i (by simpa [osRun] using h1), List.getD_eq_getElem _ _ h2]
        exact hrv
    · intro s hs
      simp only [List.mem_map, List.mem_range] at hs
      obtain ⟨i, hi, rfl⟩ := hs
      simp only [StmtOk, Atom.Holds]
      rw [vc i hi, vr i hi]
  · show σ' (.n (pd.2.2 + 20 - 1)) = _
    rw [show pd.2.2 + 20 - 1 = pd.2.2 + 19 by omega, hsq.2]
    rfl
  · have := hb.w0; have := hb.w1; have := hb.c; have := hb.b; have := hb.a; have := hb.t
    have := hb.cb
    refine ⟨fun f hf ↦ ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals simp only [osPositions, List.mem_cons, List.mem_nil_iff, or_false] at *
    all_goals omega

end
end LeanVM.Guest.B1.Whir
