/-
  LeanVM.Guest.B1.Whir.Sound

  `open_stacked` is sound at every candidate.
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

`open_stacked_sound_holds : open_stacked_sound_Spec`: for every stack log `22 ≤ μ ≤ 28` and rate
`1 ≤ r ≤ 4`, a call of `open_stacked__L{candidate μ r}` establishes `OpenOut`: the words it reads
and the openings run the Spec's `whirOpen μ r target` (the stacked WHIR opening up to its
terminal check, `verifyWhir_split`), and it returns the terminal's claim, point, glued weight
and residual. From the candidate's core IR (`osData_all`), its facts (`candB_all`), B1-a's
callees (`*_holds`) and `open_generic`.
-/

namespace LeanVM.Guest.B1.Whir

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Verifier

@[expose] public section

/-- **A level's callees**, from B1-a's theorems and the names' facts. -/
theorem lvCallees_of {κ : ℕ} (hκ : κ ≤ 32) (L : MemoryImage κ) {c : OsCfg} {lvl : ℕ} {lv : OsLv}
    (hsq : FnIs (c.sqLoop lvl) (osParams 6) (sqLoopBody lv (c.sqLoop lvl)))
    (hn : NamesOk c lvl lv) : LvCallees L.read c lvl lv := by
  let rd := L.read
  obtain ⟨hood, hfm, hgr, hdec, hcap, -, hrw, hfo⟩ := hn
  refine ⟨fun a r h ↦ (opening_fold_holds rd a r).mp h,
    fun a r h ↦ (assert_canonical_holds rd a r).mp h,
    fun hnf a r h ↦ (opening_ood_point_holds _ (hood hnf) rd a r).mp h,
    fun a r h ↦ (opening_final_message_holds _ hfm rd a r).mp h,
    fun a r h ↦ by rw [hgr] at h; exact (grind_check_holds rd a r).mp h, hsq,
    fun a r hw h ↦ decode_query_windows_all_holds _ hdec hκ L a r hw h, fun a r h ↦ ?_,
    fun a r h ↦ (verify_merkle_cap_holds _ hcap rd a r).mp h⟩
  rw [hrw] at h
  by_cases h0 : lvl = 0
  · simp only [h0, ↓reduceIte] at h hfo ⊢
    rw [hfo]; exact opening_row_weights_holds.1 rd a r |>.mp h
  · simp only [h0, ↓reduceIte] at h hfo ⊢
    rw [hfo]; exact opening_row_weights_holds.2 rd a r |>.mp h

theorem calleesOk_of {rd : Reader} {c : OsCfg} : ∀ (lvs : List OsLv) (lvl : ℕ),
    (∀ i (hi : i < lvs.length), LvCallees rd c (lvl + i) lvs[i]) → CalleesOk rd c lvl lvs
  | [], _, _ => trivial
  | lv :: rest, lvl, h => ⟨h 0 (by simp), calleesOk_of rest (lvl + 1) fun i hi ↦ by
      have := h (i + 1) (by simp; omega)
      rwa [show lvl + (i + 1) = lvl + 1 + i by ring] at this⟩

theorem openName_eq (μ r : ℕ) (h : candidate μ r < 28) :
    openName μ r = "open_stacked__L" ++ natStr (candidate μ r) := by
  rw [openName, openNames, natStr_eq, List.getD_eq_getElem _ _ (by simpa using h)]
  simp

theorem osCfg_levels_getElem (m i : ℕ) (h : i < (osCfg m).levels.length) :
    (osCfg m).levels[i] = osLv m i := by
  simp [osCfg]

/-- **A level's `opening_queries` calls are sound with their queries named**: through the frame
map, at the deployed shape the names' facts give. -/
theorem lvQW_of {rd : Reader} {C : CallRel} {V : FrameMap} (hU : UnfoldsV rd C V)
    (hle : CallRel.Le C (coreProgram.Rel rd)) {c : OsCfg} {lvl : ℕ} {lv : OsLv}
    (hn : NamesOk c lvl lv) : LvQW rd C lvl lv (lvW rd V lvl lv (osQueriesName lvl lv)) := by
  intro args rets hC hN hNo hcdd hbits
  have hq := hn.2.2.2.2.2.1
  have hp := opening_queries_all_sound_w _ (shapes_loops hq)
  obtain ⟨fm, hf, hpm, hh⟩ := hU _ _ _ hC
  have hdep : lv.depth - lv.capDepth + lv.capDepth = lv.depth := Nat.sub_add_cancel hcdd
  have := hp rd C V hU hle fm (V (osQueriesName lvl lv) args rets) args rets
    (lv.queries / (1 + if lvl = 0 then 1 else 0)) hf hpm hh hN hNo
    (by simp only; rw [hdep]; exact hbits _ hN hNo)
  simp only at this
  rw [hdep] at this
  exact this

theorem qwOk_of {rd : Reader} {C : CallRel} {Wf : ℕ → OsLv → List E → List E → List QW} {c : OsCfg} :
    ∀ (lvs : List OsLv) (lvl : ℕ),
    (∀ i (hi : i < lvs.length), LvQW rd C (lvl + i) lvs[i] (Wf (lvl + i) lvs[i])) →
      QWOk rd C Wf lvl lvs
  | [], _, _ => trivial
  | lv :: rest, lvl, h => ⟨h 0 (by simp), qwOk_of (c := c) rest (lvl + 1) fun i hi ↦ by
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

/-- **`open_stacked` is sound with its witness named**, at every candidate. -/
theorem open_stacked_sound_w : open_stacked_sound_w_Spec open_stacked_osW := by
  intro κ hκ L C V hU hle μ r h1 h2 h3 h4 root fs target root0 root1 cur rets fn σ hfs hroot hfind
    hp hh
  set rd := L.read
  have hm : candidate μ r < 28 := by unfold candidate; omega
  obtain ⟨cfg, hF, hnames, hffm⟩ := candB_sound (candB_all μ r h1 h2 h3 h4)
  have hdata := osData_all _ hm
  rw [openName_eq μ r hm] at hfind
  have hcur : σ (.n 8) = cur := by
    obtain ⟨fn0, hf0, hps, -⟩ := hdata.1
    rw [hf0] at hfind
    cases hfind
    rw [hps] at hp
    obtain ⟨f0, f1, f2, f3, f4, rfl⟩ : ∃ f0 f1 f2 f3 f4, fs = [f0, f1, f2, f3, f4] := by
      match fs, hfs with
      | [f0, f1, f2, f3, f4], _ => exact ⟨f0, f1, f2, f3, f4, rfl⟩
    have := congrArg (·.getD 8 0) hp
    simpa [osParams] using this
  have hW := open_generic (Wf := fun lvl lv ↦ lvW rd V lvl lv (osQueriesName lvl lv)) hdata.1
    (fun lvl h ↦ ?_) hF ?_ (fun a r h ↦ (opening_fold_holds rd a r).mp h)
    (fun a r h ↦ (fold_final_msg_holds _ hffm rd a r).mp h) hfs hroot hle ?_ hfind hp hh
  · unfold open_stacked_osW
    rw [hcur]
    have heq : (osQCalls (osCfg (candidate μ r)) 0 (osCfg (candidate μ r)).levels
        (osHead (osCfg (candidate μ r))).2).map (osLevelOs rd σ V) =
        (osQCalls (osCfg (candidate μ r)) 0 (osCfg (candidate μ r)).levels
        (osHead (osCfg (candidate μ r))).2).map
          (fun e ↦ lvOpenings rd σ e.2.1 (lvW rd V e.1 e.2.1 (osQueriesName e.1 e.2.1)) e.2.2) := by
      refine List.map_congr_left fun e he ↦ ?_
      obtain ⟨lvl, lv, name, args, rets'⟩ := e
      have := osQCalls_name _ _ _ _ _ he
      simp only at this
      subst this
      rfl
    rw [heq]
    exact hW
  · rw [osCfg_levels_getElem _ _ h]; exact (hdata.2 lvl h).2
  · refine calleesOk_of _ 0 fun i hi ↦ ?_
    rw [Nat.zero_add, osCfg_levels_getElem _ _ hi]
    have hn := hnames i hi
    rw [lv_getD hi, osCfg_levels_getElem _ _ hi] at hn
    exact lvCallees_of hκ L (hdata.2 i hi).1 hn
  · refine qwOk_of (c := osCfg (candidate μ r)) _ 0 fun i hi ↦ ?_
    rw [Nat.zero_add]
    have hn := hnames i hi
    rw [lv_getD hi] at hn
    exact lvQW_of hU hle hn

end
end LeanVM.Guest.B1.Whir
