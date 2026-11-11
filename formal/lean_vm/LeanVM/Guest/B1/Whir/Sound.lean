/-
  LeanVM.Guest.B1.Whir.Sound

  `open_stacked` is sound at every stack size and rate.
-/

module

public import LeanVM.Guest.B1.Whir.FactsAll
public import LeanVM.Guest.B1.Whir.DataAll
public import LeanVM.Guest.B1.Whir.Names
public import LeanVM.Guest.B1.Bits.AssertCanonical
public import LeanVM.Guest.B1.Bits.Grind
public import LeanVM.Guest.B1.Bits.QueryWindowsAll
public import LeanVM.Guest.B1.Merkle.CapAll
public import LeanVM.Guest.B1.Opening.Fold
public import LeanVM.Guest.B1.Opening.OodPoint
public import LeanVM.Guest.B1.Opening.FinalMessage
public import LeanVM.Guest.B1.Opening.RowWeights
public import LeanVM.Guest.B1.Opening.QueriesAll
public import LeanVM.Guest.B1.Opening.QueriesAllW
public import LeanVM.Guest.B1.Opening.LoopsTable
public import LeanVM.Guest.B1.Eq.FoldFinal

/-!
# `open_stacked`, soundly (TRIAGE G #42)

`open_stacked_sound_w : open_stacked_sound_w_Spec open_stacked_osW` and
`open_stacked_sound_holds : open_stacked_sound_Spec`: for every stack log `minOpenLog ≤ μ ≤ 30` and rate
`1 ≤ r ≤ 4`, a call of `open_stacked__L{μ - minOpenLog}` on the rate's selector establishes `OpenOut`: the
words it reads and the openings run the Spec's `whirOpen μ r target` (the stacked WHIR opening up
to its terminal check, `verifyWhir_split`), and it returns the terminal's claim, point, glued
weight and residual. From the size's core IR (`osData_all`) at the rate's levels
(`osBody_rate`), its facts at the rate (`candB_all`), B1-a's callees and the helpers'
specializations (`*_holds`, `*Table_ok`) and `open_generic`.
-/

namespace LeanVM.Guest.B1.Whir

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest LeanVM.Guest.B1
open LeanVM.Guest.Value LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Verifier

@[expose] public section

theorem lp_callee {κ : ℕ} (hκ : κ ≤ 32) (L : MemoryImage κ) {lv : OsLv}
    (hlp : (osPositionsName lv, lv.squeezes, lpLoopOf (osPositionsName lv), lv.depth, lv.capDepth) ∈
      lpTable)
    (hdec : ("decode_query_windows__L" ++ natStr lv.depth ++ "_L" ++ natStr lv.capDepth, lv.depth,
      lv.capDepth) ∈ queryWindowsShapes)
    (hpw : digitsVal (osPowDigits (192 / lv.depth)) 1 = 192 / lv.depth) (hn0 : 0 < lv.squeezes)
    (hn : lv.squeezes < ordG) (hn5 : lv.squeezes * 5 < u128Bound) (args rets : List E)
    (h : coreProgram.Rel L.read (osPositionsName lv) args rets) (hw : WinTabs L.read (args.getD 7 0)) :
    MeaningLevelPositions lv.depth lv.capDepth lv.squeezes L.read args rets := by
  have h12 := lpTable_ok _ hlp
  exact level_positions_sound h12.1 h12.2 hpw
    (fun a r hw h ↦ decode_query_windows_all_holds _ hdec hκ L a r hw h) hn0 hn hn5 args rets h hw

theorem lr_callee {rd : Reader} {lv : OsLv}
    (hlr : (osResidualName lv, lv.queries, lv.logCols, (lrLoopsOf (osResidualName lv)).1,
      (lrLoopsOf (osResidualName lv)).2) ∈ lrTable)
    (hrb : (rbName lv.logCols, lv.logCols) ∈ rbTable) (hc : 1 ≤ lv.logCols)
    (hq1 : lv.queries / resBatch < ordG) (hq1' : lv.queries / resBatch < u128Bound)
    (hq8 : resBatch * (lv.queries / resBatch) < u128Bound) (args rets : List E)
    (h : coreProgram.Rel rd (osResidualName lv) args rets) :
    MeaningLevelResidual lv.queries lv.logCols rd args rets := by
  have h123 := lrTable_ok _ hlr
  have hrbf := rbTable_ok _ hrb
  exact level_residual_sound h123.1 h123.2.1 h123.2.2 hrbf hc hq1 hq1' hq8 args rets h

theorem rw_callee {rd : Reader} {lvl : ℕ} {lv : OsLv}
    (hrw : "opening_row_weights__L" ++ natStr lv.folds ++ "_L" ++ natStr (if lvl = 0 then 1 else 0) =
      if lvl = 0 then "opening_row_weights__L6_L1" else "opening_row_weights__L4_L0")
    (hfo : lv.folds = if lvl = 0 then 6 else 4) (args rets : List E)
    (h : coreProgram.Rel rd ("opening_row_weights__L" ++ natStr lv.folds ++ "_L" ++
      natStr (if lvl = 0 then 1 else 0)) args rets) :
    MeaningOpeningRowWeights lv.folds (if lvl = 0 then 1 else 0) rd args rets := by
  rw [hrw] at h
  by_cases h0 : lvl = 0
  · simp only [h0, ↓reduceIte] at h hfo ⊢
    rw [hfo]; exact opening_row_weights_holds.1 rd args rets |>.mp h
  · simp only [h0, ↓reduceIte] at h hfo ⊢
    rw [hfo]; exact opening_row_weights_holds.2 rd args rets |>.mp h

/-- **A level's callees**, from B1-a's theorems, the helpers' tables and the names' facts. -/
theorem lvCallees_of {κ : ℕ} (hκ : κ ≤ 32) (L : MemoryImage κ) {c : OsCfg} {lvl : ℕ} {lv : OsLv}
    (hs : LvStatic c lvl lv) (hn : NamesOk c lvl lv) : LvCallees L.read c lvl lv := by
  obtain ⟨⟨hood, hfm, hgr, hdec, hcap, -, hrw, hfo⟩, hlp, hlq, hlr, hrb, hpw, hn0, hn,
    hn5, hq8⟩ := hn
  have hlq' := lqTable_ok _ hlq
  exact ⟨fun a r h ↦ (assert_canonical_holds L.read a r).mp h,
    fun hnf a r h ↦ (opening_ood_point_all_holds _ (hood hnf) L.read a r).mp h,
    fun a r h ↦ (opening_final_message_holds _ hfm L.read a r).mp h,
    fun a r h ↦ by rw [hgr] at h; exact (grind_check_holds L.read a r).mp h,
    ⟨lp_callee hκ L hlp hdec hpw hn0 hn hn5, hlq', rw_callee hrw hfo,
      fun a r h ↦ (verify_merkle_cap_holds _ hcap L.read a r).mp h⟩,
    lr_callee hlr hrb hs.ml1 hs.qo hs.qu hq8⟩

theorem calleesOk_of {rd : Reader} {c : OsCfg} : ∀ (lvs : List OsLv) (lvl : ℕ),
    (∀ i (hi : i < lvs.length), LvCallees rd c (lvl + i) lvs[i]) → CalleesOk rd c lvl lvs
  | [], _, _ => trivial
  | lv :: rest, lvl, h => ⟨h 0 (by simp), calleesOk_of rest (lvl + 1) fun i hi ↦ by
      have := h (i + 1) (by simp; omega)
      rwa [show lvl + (i + 1) = lvl + 1 + i by ring] at this⟩

theorem ratesOk_of {σ : Val} {c : OsCfg} : ∀ (lvs : List OsLv) (lvl : ℕ),
    (∀ i (hi : i < lvs.length), LvRate σ c (lvl + i) lvs[i]) → RatesOk σ c lvl lvs
  | [], _, _ => trivial
  | lv :: rest, lvl, h => ⟨h 0 (by simp), ratesOk_of rest (lvl + 1) fun i hi ↦ by
      have := h (i + 1) (by simp; omega)
      rwa [show lvl + (i + 1) = lvl + 1 + i by ring] at this⟩

theorem openName_eq (μ : ℕ) (h : μ - minOpenLog < ligNSizes) :
    openName μ = "open_stacked__L" ++ natStr (μ - minOpenLog) := by
  rw [openName, openNames, natStr_eq, List.getD_eq_getElem _ _ (by simpa using h)]
  simp

theorem osCfgR_levels_getElem (m ri i : ℕ) (h : i < (osCfgR m ri).levels.length) :
    (osCfgR m ri).levels[i] = osLvR m ri i := by
  simp [osCfgR, osLevelsR]

/-- **A level's `opening_queries` calls are sound with their queries named**: through the frame
map, at the deployed shape the names' facts give. -/
theorem lvQW_of {rd : Reader} {C : CallRel} {V : FrameMap} (hU : UnfoldsV rd C V)
    (hle : CallRel.Le C (coreProgram.Rel rd)) {c : OsCfg} {lvl : ℕ} {lv : OsLv}
    (hn : NamesOk c lvl lv) : LvQW rd C lvl lv (lvW rd V lvl lv (oqNameOf lvl lv)) := by
  intro args rets hC hN hNo hcdd hbits
  have hq := hn.1.2.2.2.2.2.1
  have hp := opening_queries_all_sound_w _ (shapes_loops hq)
  obtain ⟨fm, hf, hpm, hh⟩ := hU _ _ _ hC
  have hdep : lv.depth - lv.capDepth + lv.capDepth = lv.depth := Nat.sub_add_cancel hcdd
  have := hp rd C V hU hle fm (V (oqNameOf lvl lv) args rets) args rets
    (lv.queries / (1 + if lvl = 0 then 1 else 0)) hf hpm hh hN hNo
    (by simp only; rw [hdep]; exact hbits _ hN hNo)
  simp only at this
  rw [hdep] at this
  exact this

theorem qwOk_of {rd : Reader} {C : CallRel} {Wf : ℕ → OsLv → List E → List E → List QW} :
    ∀ (lvs : List OsLv) (lvl : ℕ),
    (∀ i (hi : i < lvs.length), LvQW rd C (lvl + i) lvs[i] (Wf (lvl + i) lvs[i])) →
      QWOk rd C Wf lvl lvs
  | [], _, _ => trivial
  | lv :: rest, lvl, h => ⟨h 0 (by simp), qwOk_of rest (lvl + 1) fun i hi ↦ by
      have := h (i + 1) (by simp; omega)
      rwa [show lvl + (i + 1) = lvl + 1 + i by ring] at this⟩

theorem osQCalls_name (c : OsCfg) : ∀ (lvl : ℕ) (lvs : List OsLv) (st : OsSt),
    ∀ e ∈ osQCalls c lvl lvs st, e.2.2.1 = osQueriesName e.1 e.2.1
  | _, [], _, e, he => by simp [osQCalls] at he
  | lvl, lv :: rest, st, e, he => by
    simp only [osQCalls, List.mem_cons] at he
    rcases he with rfl | he
    · rfl
    · exact osQCalls_name c (lvl + 1) rest _ e he

/-- **`open_stacked` is sound with its witness named**, at every size and rate. -/
theorem open_stacked_sound_w : open_stacked_sound_w_Spec open_stacked_osW := by
  intro κ hκ L C V hU hle μ r h1 h2 h3 h4 root fs target root0 root1 cur rets fn σ hfs hroot hfind
    hp hh
  set rd := L.read
  set m := μ - minOpenLog with hmdef
  set ri := r - 1 with hridef
  have h20 : minOpenLog + ligNSizes = 31 := rfl
  have hm : m < ligNSizes := by omega
  have hri : ri < 4 := by omega
  have hμ : μ = m + minOpenLog := by omega
  have hr : r = ri + 1 := by omega
  obtain ⟨cfg, hF, hnames, hffm⟩ := candB_sound (candB_all m ri hm hri)
  rw [← hμ, ← hr] at hF
  have hdata : FnIs ("open_stacked__L" ++ natStr m) (osParams 10) (osBody (osCfgR m ri)) := by
    have := osData_all m hm
    unfold OsData at this
    rwa [osBody_rate m ri] at this
  rw [openName_eq μ hm] at hfind
  have hσ : σ (.n osRate) = ofK (addressOfIndex ri) ∧ σ (.n 9) = cur := by
    obtain ⟨fn0, hf0, hps, -⟩ := hdata
    rw [hf0] at hfind
    cases hfind
    rw [hps] at hp
    obtain ⟨f0, f1, f2, f3, f4, rfl⟩ : ∃ f0 f1 f2 f3 f4, fs = [f0, f1, f2, f3, f4] := by
      match fs, hfs with
      | [f0, f1, f2, f3, f4], _ => exact ⟨f0, f1, f2, f3, f4, rfl⟩
    refine ⟨?_, ?_⟩
    · have := congrArg (·.getD 0 0) hp
      simpa [osParams, rateSel] using this
    · have := congrArg (·.getD 9 0) hp
      simpa [osParams] using this
  set c := osCfgR m ri
  have hW := open_generic (Wf := fun lvl lv ↦ lvW rd V lvl lv (oqNameOf lvl lv)) hdata hF
    (calleesOk_of _ 0 fun i hi ↦ by
      rw [Nat.zero_add]
      have hn := hnames i hi
      have hs := hF.lv i hi
      rw [lv_getD hi] at hn hs
      exact lvCallees_of hκ L hs hn)
    (fun a r h ↦ (opening_fold_holds rd a r).mp h)
    (fun a r h ↦ (fold_final_msg_holds _ hffm rd a r).mp h) hfs hroot hle hU
    (qwOk_of _ 0 fun i hi ↦ by
      rw [Nat.zero_add]
      have hn := hnames i hi
      rw [lv_getD hi] at hn
      exact lvQW_of hU hle hn)
    (ratesOk_of _ 0 fun i hi ↦ by
      rw [Nat.zero_add]
      refine ⟨ri, hri, hσ.1, osCfgR_lvAt_length m ri i, ?_⟩
      rw [osCfgR_lvAt_getD i hri, lv_getD hi])
    hfind hp hh
  unfold open_stacked_osW
  rw [hσ.2, ← hridef]
  have heq : (osQCalls c 0 c.levels (osHead c).2).map (osLevelOs rd σ V) =
      (osQCalls c 0 c.levels (osHead c).2).map
        (fun e ↦ lvOs rd σ V (lvW rd V e.1 e.2.1 (oqNameOf e.1 e.2.1)) e.1 e.2.1 e.2.2) := by
    refine List.map_congr_left fun e he ↦ ?_
    obtain ⟨lvl, lv, name, args, rets'⟩ := e
    have := osQCalls_name _ _ _ _ _ he
    simp only at this
    subst this
    rfl
  rw [heq]
  exact hW

/-- **`open_stacked` is sound**, at every stack log and rate. -/
theorem open_stacked_sound_holds : open_stacked_sound_Spec := by
  intro κ hκ L μ r h1 h2 h3 h4 root fs target root0 root1 cur rets hfs hroot hrel
  obtain ⟨fn, hfind, hpar, hbody⟩ := unfoldsV_rel L.read _ _ _ hrel
  exact (open_stacked_sound_w hκ L _ _ (unfoldsV_rel L.read) (fun _ _ _ h ↦ h) μ r h1 h2 h3 h4
    root fs target root0 root1 cur rets fn _ hfs hroot hfind hpar hbody).openOut

end
end LeanVM.Guest.B1.Whir
