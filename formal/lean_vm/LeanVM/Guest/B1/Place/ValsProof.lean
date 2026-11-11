/-
  LeanVM.Guest.B1.Place.ValsProof

  The honest valuation of open_stacked's body at the values its placed lift reads: the proof.
-/

module

public import LeanVM.Guest.B1.Place.ValsBody
public import LeanVM.Guest.B1.Whir.FactsAll
public import LeanVM.Guest.B1.Place.ValsSizes

/-!
# The body's values the lift reads, proved

The honest valuation `osSigma` is the body's values `osBodyF` on `[10, osFinEnd)`: the head's
(`osSigma_headV`), level `i`'s (`osSigma_lvV`, by `lvsF_atV`), the tail's and the finish's.

* `bufs`: the hints are `osAllocsV` (`osBodyAc_allocsV`); their pointers' values are the head's
  ten fixed buffers, each level's row weights (`lvs_alloc_valsV`), the tail's challenges and the
  finish's five, which `osAtOf` takes from `bases` in that order.
* `lp`: level `i`'s `level_positions` frame is `lpCallS` at the state after its grinding check
  (`osLvKOf_getV`); its argument `5` is `query_positions` itself at offset `0`, else the
  positions' first materialization (`lvF_posV`), `query_positions·g^posOff`.
* `lq`: the calls after the positions are the row weights' (a named callee, `NamesOk`) and the
  dispatch into `level_queries` (`lvB_callsV`), whose argument `2` is the row weights' pointer
  (`lvF_wpV`).

The arms' facts used (`posOff < 2^128`, the row weights' names) come from `candB_all`.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Guest.B1.Whir
open LeanVM.Protocol.Verifier hiding Layout

@[expose] public section

/-! ## The body's values by part -/

theorem logG_gwV {e : ℕ} (he : e < 2 ^ 64 - 1) : logG (gw e) = e := by
  rw [Whir.gw_eq (by unfold u128Bound; omega), logG_gen_pow he]

theorem osHead_kV (c : OsCfg) : (osHead c).2.k = 161 := rfl

theorem osLvSt_kV (c : OsCfg) : 161 ≤ (osLvSt c).k :=
  osHead_kV c ▸ osLevels_kV c 0 c.levels (osHead c).2

theorem osTlSt_kV (c : OsCfg) : (osLvSt c).k + 2 ≤ (osTlSt c).2.1.k := by
  have hb : (osTail c (osLvSt c)).2.2 < (osTail c (osLvSt c)).2.1.k :=
    (osTail_bounds c (osLvSt c) (osLvSt_kV c)).2.2.1
  have e : (osTail c (osLvSt c)).2.2 = (osLvSt c).k + 1 := rfl
  show (osLvSt c).k + 2 ≤ (osTail c (osLvSt c)).2.1.k
  omega

theorem osFinEnd_kV (c : OsCfg) : (osTlSt c).2.1.k + 6 ≤ osFinEnd c (osTlSt c).2.1 (osTlSt c).2.2 :=
  osFinEnd_ge _ _ _


section Body

variable {c : OsCfg} {tr : OsTr} {σ : Val} {c0 c2 : E} {A : OsAt}

theorem osBodyF_headV {i : ℕ} (h : i < 161) :
    osBodyF c tr σ c0 c2 A i = headF c σ A.P c0 c2 i := by
  unfold osBodyF bodyF; exact seqF_ltV h

theorem osBodyF_lvsV {i : ℕ} (h1 : 161 ≤ i) (h2 : i < (osLvSt c).k) :
    osBodyF c tr σ c0 c2 A i =
      lvsF c 0 c.levels (tr.Ds A) (osHead c).2 (fill σ 10 161 (headF c σ A.P c0 c2)) i := by
  unfold osBodyF bodyF; rw [seqF_geV h1, seqF_ltV h2]

theorem osBodyF_tailV (h0 : 161 ≤ (osLvSt c).k) :
    osBodyF c tr σ c0 c2 A ((osLvSt c).k + 1) = A.T := by
  have hb := osTlSt_kV c
  unfold osBodyF bodyF
  rw [seqF_geV (show 161 ≤ (osLvSt c).k + 1 by omega),
    seqF_geV (show (osLvSt c).k ≤ (osLvSt c).k + 1 by omega),
    seqF_ltV (show (osLvSt c).k + 1 < (osTlSt c).2.1.k by omega)]
  unfold tailF
  rw [seqF_ltV (show (osLvSt c).k + 1 < (osLvSt c).k + 2 by omega)]
  simp

theorem osBodyF_tailSzV (h0 : 161 ≤ (osLvSt c).k) :
    osBodyF c tr σ c0 c2 A (osLvSt c).k = gw yrLogCap := by
  have hb := osTlSt_kV c
  unfold osBodyF bodyF
  rw [seqF_geV (show 161 ≤ (osLvSt c).k by omega),
    seqF_geV (show (osLvSt c).k ≤ (osLvSt c).k by omega),
    seqF_ltV (show (osLvSt c).k < (osTlSt c).2.1.k by omega)]
  unfold tailF
  rw [seqF_ltV (show (osLvSt c).k < (osLvSt c).k + 2 by omega)]
  simp

theorem osBodyF_finV {i : ℕ} (h0 : 161 ≤ (osLvSt c).k) (h : (osTlSt c).2.1.k ≤ i) :
    osBodyF c tr σ c0 c2 A i =
      finishF c (osTlSt c).2.1 (osTlSt c).2.2 (multilinearEval tr.Lf.ms tr.Tc) A.PT A.PT1 A.BD A.LS
        A.ICH (finI c tr c.levels.length) (fun j ↦ (ptC tr (c.levels.headD default).folds).getD j 0)
        (finB c tr) (Xof tr.rs tr.Fall tr.Tc) (finM tr) (finH c tr) (finI c tr) (finL c tr)
        (Λof tr.rs) (Zof tr.rs) (Yof tr.rs tr.Fall tr.Tc)
        (fill (fill (fill σ 10 161 (headF c σ A.P c0 c2)) 161 (osLvSt c).k
          (lvsF c 0 c.levels (tr.Ds A) (osHead c).2 (fill σ 10 161 (headF c σ A.P c0 c2))))
          (osLvSt c).k (osTlSt c).2.1.k
          (tailF c (osLvSt c) (fill (fill σ 10 161 (headF c σ A.P c0 c2)) 161 (osLvSt c).k
            (lvsF c 0 c.levels (tr.Ds A) (osHead c).2 (fill σ 10 161 (headF c σ A.P c0 c2))))
            A.T (tr.tailWords c))) i := by
  have hb := osTlSt_kV c
  unfold osBodyF bodyF
  rw [seqF_geV (show 161 ≤ i by omega), seqF_geV (show (osLvSt c).k ≤ i by omega),
    seqF_geV (show (osTlSt c).2.1.k ≤ i by omega)]

end Body

/-! ## The finish's values -/

section Finish

variable {c : OsCfg} {st : OsSt} {tch : ℕ} {Y PT PT1 BD LS ICH In : E} {Pp β : ℕ → E}
  {X : ℕ → ℕ → E} {M h I L : ℕ → E} {Λ : ℕ → E} {Z Yo : ℕ → ℕ → E} {σ : Val}

theorem finPtsV_k (c : OsCfg) (st : OsSt) (tch : ℕ) : st.k + 1 + 2 ≤ (finPtsV c st tch).2 :=
  osPtBlks_k c _ _ _ _ _ _

theorem finBsV_k (c : OsCfg) (st : OsSt) (tch : ℕ) :
    (finPtsV c st tch).2 + 4 ≤ (finBsV c st tch).2 :=
  osBases_k c _ _ _ _ _ _

theorem finEndV_k (c : OsCfg) (st : OsSt) (tch : ℕ) :
    (finBsV c st tch).2 + 3 ≤ osFinEnd c st tch := by
  have h1 := osResiduals_k c ((finBsV c st tch).2 + 1) ((finPtsV c st tch).2 + 1)
    ((finPtsV c st tch).2 + 3) 0 c.levels st.mats ((finBsV c st tch).2 + 3)
  have h2 := osOodWeights_k c tch c.levels.tail ((c.levels.headD default).logCols) 1 none
    (osResiduals c ((finBsV c st tch).2 + 1) ((finPtsV c st tch).2 + 1)
      ((finPtsV c st tch).2 + 3) 0 c.levels st.mats ((finBsV c st tch).2 + 3)).2
  show _ ≤ (osOodWeights c tch ((c.levels.headD default).logCols) 1 c.levels.tail none
    (osResiduals c ((finBsV c st tch).2 + 1) ((finPtsV c st tch).2 + 1)
      ((finPtsV c st tch).2 + 3) 0 c.levels st.mats ((finBsV c st tch).2 + 3)).2).2.2 + 6
  omega

/-- **The finish's buffers' pointers** in its values. -/
theorem finishF_bufsV :
    finishF c st tch Y PT PT1 BD LS ICH In Pp β X M h I L Λ Z Yo σ (st.k + 1) = PT ∧
      finishF c st tch Y PT PT1 BD LS ICH In Pp β X M h I L Λ Z Yo σ (st.k + 1 + 1) = PT1 ∧
      finishF c st tch Y PT PT1 BD LS ICH In Pp β X M h I L Λ Z Yo σ
        ((finPtsV c st tch).2 + 1) = BD ∧
      finishF c st tch Y PT PT1 BD LS ICH In Pp β X M h I L Λ Z Yo σ
        ((finPtsV c st tch).2 + 2 + 1) = LS ∧
      finishF c st tch Y PT PT1 BD LS ICH In Pp β X M h I L Λ Z Yo σ
        ((finBsV c st tch).2 + 1) = ICH := by
  have o1 := finPtsV_k c st tch
  have o2 := finBsV_k c st tch
  unfold finBsV finPtsV at o2
  unfold finPtsV at o1
  unfold finishF finBsV finPtsV
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [seqF_ltV (by omega)]; simp
  · rw [seqF_ltV (by omega)]; simp [show st.k + 1 + 1 - st.k = 2 by omega]
  · rw [seqF_geV (by omega), seqF_geV (by omega), seqF_ltV (by omega)]; simp
  · rw [seqF_geV (by omega), seqF_geV (by omega), seqF_geV (by omega), seqF_ltV (by omega)]
    simp [show (osPtBlks c (st.k + 1) (st.k + 1 + 1) tch 0 pointCap (st.k + 1 + 2)).2 + 2 + 1 -
      ((osPtBlks c (st.k + 1) (st.k + 1 + 1) tch 0 pointCap (st.k + 1 + 2)).2 + 2) = 1 by omega]
  · rw [seqF_geV (by omega), seqF_geV (by omega), seqF_geV (by omega), seqF_geV (by omega),
      seqF_geV (by omega), seqF_ltV (by omega)]
    simp

/-- **The finish's buffers' sizes** in its values. -/
theorem finishF_szsV :
    finishF c st tch Y PT PT1 BD LS ICH In Pp β X M h I L Λ Z Yo σ (finPtsV c st tch).2 =
        gw (c.levels.length * ligColsCap) ∧
      finishF c st tch Y PT PT1 BD LS ICH In Pp β X M h I L Λ Z Yo σ
        ((finPtsV c st tch).2 + 2) = gw c.levels.length ∧
      finishF c st tch Y PT PT1 BD LS ICH In Pp β X M h I L Λ Z Yo σ (finBsV c st tch).2 =
        gw (c.levels.length + 1) := by
  have o1 := finPtsV_k c st tch
  have o2 := finBsV_k c st tch
  unfold finBsV finPtsV at o2
  unfold finPtsV at o1
  unfold finishF finBsV finPtsV
  refine ⟨?_, ?_, ?_⟩
  · rw [seqF_geV (by omega), seqF_geV (by omega), seqF_ltV (by omega)]; simp
  · rw [seqF_geV (by omega), seqF_geV (by omega), seqF_geV (by omega), seqF_ltV (by omega)]
    simp
  · rw [seqF_geV (by omega), seqF_geV (by omega), seqF_geV (by omega), seqF_geV (by omega),
      seqF_geV (by omega), seqF_ltV (by omega)]
    simp

end Finish

/-! ## The honest valuation -/

/-- Level `i`'s start. -/
abbrev sAtV (c : OsCfg) (i : ℕ) : OsSt := (osLevels c 0 (c.levels.take i) (osHead c).2).2

theorem spDats_lengthV : ∀ (Ls : List SpLv) (i : ℕ) (wp : ℕ → E), (spDats Ls i wp).length = Ls.length
  | [], _, _ => rfl
  | _ :: Ls, i, wp => by simp [spDats, spDats_lengthV Ls (i + 1) wp]

theorem spDats_wpV : ∀ (Ls : List SpLv) (i : ℕ) (wp : ℕ → E) (j : ℕ)
    (h : j < (spDats Ls i wp).length), (spDats Ls i wp)[j].wp = wp (i + j)
  | [], _, _, _, h => absurd h (by simp [spDats])
  | L :: Ls, i, wp, 0, _ => rfl
  | L :: Ls, i, wp, j + 1, h => by
    have := spDats_wpV Ls (i + 1) wp j (by simpa [spDats] using h)
    rw [show i + (j + 1) = i + 1 + j by omega, ← this]
    rfl

theorem spDats_mapV : ∀ (Ls : List SpLv) (i : ℕ) (wp : ℕ → E),
    (spDats Ls i wp).map LvDat.wp = (List.range Ls.length).map fun j ↦ wp (i + j)
  | [], _, _ => rfl
  | L :: Ls, i, wp => by
    rw [List.length_cons, List.range_succ_eq_map]
    simp only [spDats, List.map_cons, List.map_map, spDats_mapV Ls (i + 1) wp, Nat.add_zero]
    refine congrArg _ (List.map_congr_left fun j _ ↦ ?_)
    simp only [Function.comp, show i + 1 + j = i + (j + 1) by omega]

section Sigma

variable {c : OsCfg} {tr : OsTr} {σ0 : Val} {c0 c2 : E} {b0 : ℕ}

theorem osSigma_bodyV {i : ℕ} (h1 : 10 ≤ i) (h2 : i < osFinEnd c (osTlSt c).2.1 (osTlSt c).2.2) :
    osSigma c tr σ0 c0 c2 b0 (.n i) = osBodyF c tr σ0 c0 c2 (osAtOf c b0) i :=
  fill_in h1 h2

theorem osSigma_headV {i : ℕ} (h1 : 10 ≤ i) (h2 : i < 161) :
    osSigma c tr σ0 c0 c2 b0 (.n i) =
      (headVals c (σ0 (.n 6)) (osAtOf c b0).P c0 c2).getD (i - 10) 0 := by
  have := osTlSt_kV c
  have := osFinEnd_kV c
  have := osLvSt_kV c
  rw [osSigma_bodyV h1 (by omega), osBodyF_headV h2]
  rfl

/-- **Level `i`'s values in the honest valuation.** -/
theorem osSigma_lvV (hlen : tr.Ls.length = c.levels.length) {i : ℕ} (hi : i < c.levels.length)
    {x : ℕ} (h1 : (sAtV c i).k ≤ x) (h2 : x < (osLevel c i c.levels[i] (sAtV c i)).2.k) :
    ∃ σ', AgreeBelow 161 (fill σ0 10 161 (headF c σ0 (osAtOf c b0).P c0 c2)) σ' ∧
      osSigma c tr σ0 c0 c2 b0 (.n x) = Whir.lvF c i c.levels[i] (sAtV c i) σ'
        ((spDats tr.Ls 0 (osAtOf c b0).wp)[i]'(by rw [spDats_lengthV, hlen]; exact hi)) x := by
  have hk0 : 161 ≤ (sAtV c i).k := osHead_kV c ▸ osLevels_kV c 0 _ (osHead c).2
  have hle : (osLevel c i c.levels[i] (sAtV c i)).2.k ≤ (osLvSt c).k := by
    have := osLevels_k_getV c c.levels 0 (osHead c).2 i hi
    rwa [Nat.zero_add] at this
  have := osTlSt_kV c
  have := osFinEnd_kV c
  rw [osSigma_bodyV (i := x) (by omega) (by omega), osBodyF_lvsV (i := x) (by omega) (by omega)]
  obtain ⟨σ', ha, he⟩ := lvsF_atV c c.levels (tr.Ds (osAtOf c b0)) 0 (osHead c).2
    (fill σ0 10 161 (headF c σ0 (osAtOf c b0).P c0 c2)) i hi
    (by unfold OsTr.Ds; rw [spDats_lengthV, hlen]; exact hi) x h1 (by rw [Nat.zero_add]; exact h2)
  rw [Nat.zero_add] at he
  exact ⟨σ', ha, he⟩

/-- **A level's row weights' pointer** in the honest valuation. -/
theorem osSigma_wpV (hlen : tr.Ls.length = c.levels.length) {i : ℕ} (hi : i < c.levels.length) :
    osSigma c tr σ0 c0 c2 b0 (.n (wpVarV c i c.levels[i] (sAtV c i))) = (osAtOf c b0).wp i := by
  have hw := osLevel_wpV c i c.levels[i] (sAtV c i)
  have hA := osLvA_kV c i c.levels[i] (sAtV c i)
  obtain ⟨σ', -, he⟩ := osSigma_lvV (σ0 := σ0) (c0 := c0) (c2 := c2) (b0 := b0) hlen hi
    (x := wpVarV c i c.levels[i] (sAtV c i)) (by unfold wpVarV; omega) (by omega)
  rw [he, lvF_wpV, spDats_wpV, Nat.zero_add]

/-- **A level's positions pointer** in the honest valuation. -/
theorem osSigma_qposV (hlen : tr.Ls.length = c.levels.length) {i : ℕ} (hi : i < c.levels.length)
    (hpo : (lvAt c i).posOff < u128Bound) :
    osSigma c tr σ0 c0 c2 b0 (.n (osMatP c.plan (lvM c i c.levels[i] (sAtV c i)).2.1.mats osQpos
      (lvAt c i).posOff (lvM c i c.levels[i] (sAtV c i)).2.1.k).2.1) =
      (osAtOf c b0).P.qpos * gen ^ (lvAt c i).posOff := by
  have hl : lvAt c i = c.levels[i] := List.getD_eq_getElem _ _ hi
  by_cases h0 : (lvAt c i).posOff = 0
  · rw [h0, pow_zero, mul_one]
    simp only [osMatP, ↓reduceIte]
    rw [osSigma_headV (by decide) (by decide)]
    rfl
  · have e : (osMatP c.plan (lvM c i c.levels[i] (sAtV c i)).2.1.mats osQpos (lvAt c i).posOff
        (lvM c i c.levels[i] (sAtV c i)).2.1.k).2.1 = (osLvA c i c.levels[i] (sAtV c i)).2.1.k + 1 := by
      unfold osMatP; simp only [h0, ↓reduceIte]; rfl
    rw [e]
    have hw := osLevel_wpV c i c.levels[i] (sAtV c i)
    have hA := osLvA_kV c i c.levels[i] (sAtV c i)
    have hk0 : 161 ≤ (sAtV c i).k := osHead_kV c ▸ osLevels_kV c 0 _ (osHead c).2
    obtain ⟨σ', ha, he⟩ := osSigma_lvV (σ0 := σ0) (c0 := c0) (c2 := c2) (b0 := b0) hlen hi
      (x := (osLvA c i c.levels[i] (sAtV c i)).2.1.k + 1) (by omega) (by unfold wpVarV at hw; omega)
    rw [hl] at h0 hpo ⊢
    obtain ⟨σ'', ha', he'⟩ := lvF_posV c i c.levels[i] (sAtV c i) σ'
      ((spDats tr.Ls 0 (osAtOf c b0).wp)[i]'(by rw [spDats_lengthV, hlen]; exact hi)) h0
    rw [he, he', ha' _ (by unfold osQpos; omega), ha _ (by unfold osQpos; omega),
      fill_in (by unfold osQpos; omega) (by unfold osQpos; omega), Whir.gw_eq hpo]
    rfl

/-! ## The levels' frames -/

theorem osMatP_callSFV (σ : Val) (P : List (ℕ × ℕ × ℕ)) (m : List OsMat) (b o k : ℕ) :
    (osMatP P m b o k).1.filterMap (Stmt.callSF σ) = [] :=
  callSF_atoms σ _ (osMatP_atoms _ _ _ _ _)

theorem mkCall_fV (σ : Val) (x : Option V × String × List V × List V) :
    (Main.mkCall σ x).f = x.2.1 ∧ (Main.mkCall σ x).args = x.2.2.1 := by
  rcases x with ⟨_ | _, f, a, r⟩ <;> exact ⟨rfl, rfl⟩

theorem lvM_fsV (c : OsCfg) (lvl : ℕ) (lv : OsLv) (s : OsSt) :
    ∃ a b d e f, (lvM c lvl lv s).2.1.fs = [a, b, d, e, f] := by
  unfold lvM osFinal osCommit
  split_ifs <;> exact ⟨_, _, _, _, _, rfl⟩

/-- **The calls after a level's positions**: the one without a named kind is the dispatch into
`level_queries`, its argument `2` the row weights' pointer. -/
theorem lvB_callsV (σ : Val) (c : OsCfg) (lvl : ℕ) (lv : OsLv) (s : OsSt)
    (hrw : osKindOf ("opening_row_weights__L" ++ natStr lv.folds ++ "_L" ++
      natStr (if lvl = 0 then 1 else 0)) ≠ none) :
    ∀ x ∈ (lvB c lvl lv s).filterMap (Stmt.callSF σ), osKindOf x.2.1 = none →
      (x.2.2.1.map σ).getD 2 0 = σ (.n (wpVarV c lvl lv s)) := by
  intro x hx hk
  unfold lvB osQueries at hx
  dsimp only at hx
  have hy : (lvl = c.yrLevel) = True ∨ (lvl = c.yrLevel) = False := by
    by_cases h : lvl = c.yrLevel
    · exact .inl (eq_true h)
    · exact .inr (eq_false h)
  rcases hy with hy | hy <;>
    simp only [hy, ↓reduceIte, List.filterMap_append, List.filterMap_cons, List.filterMap_nil,
      osMatP_callSFV, osMu, osHeap, osOodGlue, osGlue, Stmt.callSF, Main.Stmt.callS,
      List.nil_append, List.append_nil, List.mem_cons, List.mem_append, List.not_mem_nil,
      or_false] at hx <;>
    rcases hx with rfl | rfl <;>
    first | exact absurd hk hrw | rfl

/-- **Level `j`'s frames**: its `level_positions` frame and its calls after it. -/
theorem osLvKOf_getV (σ : Val) (c : OsCfg) : ∀ (lvl : ℕ) (lvs : List OsLv) (st : OsSt) (j : ℕ)
    (hj : j < lvs.length),
    ((osLvKOf σ c lvl lvs st)[j]'(by rw [osLvKOf_length]; exact hj)).sq =
        Main.mkCall σ (lpCallS σ c (lvl + j)
          (lvM c (lvl + j) lvs[j] (osLevels c lvl (lvs.take j) st).2).2.1) ∧
      ((osLvKOf σ c lvl lvs st)[j]'(by rw [osLvKOf_length]; exact hj)).B =
        ((lvB c (lvl + j) lvs[j] (osLevels c lvl (lvs.take j) st).2).filterMap
          (Stmt.callSF σ)).map (Main.mkCall σ)
  | _, [], _, _, hj => absurd hj (by simp)
  | lvl, lv :: rest, st, 0, _ => ⟨rfl, rfl⟩
  | lvl, lv :: rest, st, j + 1, hj => by
    have ih := osLvKOf_getV σ c (lvl + 1) rest (osLevel c lvl lv st).2 j (by simpa using hj)
    rw [show lvl + (j + 1) = lvl + 1 + j by omega]
    exact ih

/-! ## The values -/

/-- **The values the lift reads**, at a configuration with its sizes bounded, its positions'
offsets below `2^128` and its row weights named. -/
theorem osCallVals_of {c : OsCfg} {tr : OsTr} {σ0 : Val} {c0 c2 : E} {b0 : ℕ}
    (hlen : tr.Ls.length = c.levels.length) (hn : 0 < c.levels.length)
    (hsz : ∀ e ∈ osSizesL c, e < 2 ^ 64 - 1)
    (hpo : ∀ i < c.levels.length, (lvAt c i).posOff < u128Bound)
    (hrw : ∀ i (hi : i < c.levels.length), osKindOf ("opening_row_weights__L" ++
      natStr c.levels[i].folds ++ "_L" ++ natStr (if i = 0 then 1 else 0)) ≠ none) :
    OsCallVals c tr σ0 c0 c2 b0 := by
  have hL := osLvSt_kV c
  have hT := osTlSt_kV c
  have hE := osFinEnd_kV c
  have hpk := finPtsV_k c (osTlSt c).2.1 (osTlSt c).2.2
  have hbk := finBsV_k c (osTlSt c).2.1 (osTlSt c).2.2
  have hek := finEndV_k c (osTlSt c).2.1 (osTlSt c).2.2
  have hg : ∀ e ∈ osSizesL c, logG (gw e) = e := fun e he ↦ logG_gwV (hsz e he)
  -- the finish's values
  have fin : ∀ x, (osTlSt c).2.1.k ≤ x → x < osFinEnd c (osTlSt c).2.1 (osTlSt c).2.2 →
      (osSigma c tr σ0 c0 c2 b0) (.n x) = osBodyF c tr σ0 c0 c2 (osAtOf c b0) x := fun x h1 h2 ↦ osSigma_bodyV (by omega) h2
  have fPT : (osSigma c tr σ0 c0 c2 b0) (.n ((osTlSt c).2.1.k + 1)) = (osAtOf c b0).PT := by
    rw [fin _ (by omega) (by omega), osBodyF_finV hL (by omega)]; exact finishF_bufsV.1
  have fPT1 : (osSigma c tr σ0 c0 c2 b0) (.n ((osTlSt c).2.1.k + 1 + 1)) = (osAtOf c b0).PT1 := by
    rw [fin _ (by omega) (by omega), osBodyF_finV hL (by omega)]; exact finishF_bufsV.2.1
  have fBD : (osSigma c tr σ0 c0 c2 b0) (.n ((finPtsV c (osTlSt c).2.1 (osTlSt c).2.2).2 + 1)) = (osAtOf c b0).BD := by
    rw [fin _ (by omega) (by omega), osBodyF_finV hL (by omega)]; exact finishF_bufsV.2.2.1
  have fLS : (osSigma c tr σ0 c0 c2 b0) (.n ((finPtsV c (osTlSt c).2.1 (osTlSt c).2.2).2 + 2 + 1)) = (osAtOf c b0).LS := by
    rw [fin _ (by omega) (by omega), osBodyF_finV hL (by omega)]; exact finishF_bufsV.2.2.2.1
  have fICH : (osSigma c tr σ0 c0 c2 b0) (.n ((finBsV c (osTlSt c).2.1 (osTlSt c).2.2).2 + 1)) = (osAtOf c b0).ICH := by
    rw [fin _ (by omega) (by omega), osBodyF_finV hL (by omega)]; exact finishF_bufsV.2.2.2.2
  have sBD : (osSigma c tr σ0 c0 c2 b0) (.n (finPtsV c (osTlSt c).2.1 (osTlSt c).2.2).2) =
      gw (c.levels.length * ligColsCap) := by
    rw [fin _ (by omega) (by omega), osBodyF_finV hL (by omega)]; exact finishF_szsV.1
  have sLS : (osSigma c tr σ0 c0 c2 b0) (.n ((finPtsV c (osTlSt c).2.1 (osTlSt c).2.2).2 + 2)) = gw c.levels.length := by
    rw [fin _ (by omega) (by omega), osBodyF_finV hL (by omega)]; exact finishF_szsV.2.1
  have sICH : (osSigma c tr σ0 c0 c2 b0) (.n (finBsV c (osTlSt c).2.1 (osTlSt c).2.2).2) = gw (c.levels.length + 1) := by
    rw [fin _ (by omega) (by omega), osBodyF_finV hL (by omega)]; exact finishF_szsV.2.2
  -- the tail's
  have tT : (osSigma c tr σ0 c0 c2 b0) (.n ((osLvSt c).k + 1)) = (osAtOf c b0).T := by
    rw [osSigma_bodyV (i := (osLvSt c).k + 1) (by omega) (by omega)]; exact osBodyF_tailV hL
  have sT : (osSigma c tr σ0 c0 c2 b0) (.n (osLvSt c).k) = gw yrLogCap := by
    rw [osSigma_bodyV (i := (osLvSt c).k) (by omega) (by omega)]; exact osBodyF_tailSzV hL
  -- the levels'
  have hD : (tr.Ds (osAtOf c b0)).length = c.levels.length := by
    unfold OsTr.Ds; rw [spDats_lengthV, hlen]
  have hlv := lvs_alloc_valsV c (osSigma c tr σ0 c0 c2 b0) c.levels (tr.Ds (osAtOf c b0)) 0 (osHead c).2
    (fill σ0 10 161 (headF c σ0 (osAtOf c b0).P c0 c2)) hD (fun i h1 h2 ↦ by
      have h1' : 161 ≤ i := by rw [osHead_kV] at h1; exact h1
      have h2' : i < (osLvSt c).k := h2
      rw [osSigma_bodyV (i := i) (by omega) (by omega), osBodyF_lvsV h1' h2'])
  have hwps : (tr.Ds (osAtOf c b0)).map LvDat.wp = (List.range c.levels.length).map fun j ↦ (osAtOf c b0).wp j := by
    unfold OsTr.Ds; rw [spDats_mapV, hlen]; simp only [Nat.zero_add]
  have hn0 : c.maxIl ∈ osSizesL c := by
    unfold osSizesL
    exact List.mem_append_left _ (List.mem_append_right _ (List.mem_replicate.mpr ⟨by omega, rfl⟩))
  have hm : ∀ e, e ∈ [c.yrLen, 2 * c.levels.length, c.nFolds, c.levels.length, c.levels.length,
      c.levels.length * ligPosCap, c.levels.length * ligPosCap, 128, c.levels.length * ligColsCap,
      c.levels.length * oodSlots] ++ [yrLogCap, pointCap, pointCap, c.levels.length * ligColsCap,
      c.levels.length, c.levels.length + 1] → e ∈ osSizesL c := by
    intro e he
    unfold osSizesL
    rcases List.mem_append.mp he with h | h
    · exact List.mem_append_left _ (List.mem_append_left _ h)
    · exact List.mem_append_right _ h
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- sizes
    rw [osBodyAc_allocsV]
    unfold osAllocsV
    simp only [List.map_append, hlv.2, hg _ hn0, List.map_const']
    simp only [headAllocsV, finAllocsV, osHeapAV, List.map_cons, List.map_nil, Sum.elim_inr,
      Sum.elim_inl, id, sT, sBD, sLS, sICH]
    simp (disch := omega) only [osSigma_headV]
    show [logG (gw c.yrLen), logG (gw (2 * c.levels.length)), logG (gw c.nFolds),
      logG (gw c.levels.length), logG (gw c.levels.length), logG (gw (c.levels.length * ligPosCap)),
      logG (gw (c.levels.length * ligPosCap)), logG (gw 128), logG (gw (c.levels.length * ligColsCap)),
      logG (gw (c.levels.length * oodSlots))] ++ _ = _
    simp only [hg c.yrLen (hm _ (by simp)), hg (2 * c.levels.length) (hm _ (by simp)),
      hg c.nFolds (hm _ (by simp)), hg c.levels.length (hm _ (by simp)),
      hg (c.levels.length * ligPosCap) (hm _ (by simp)), hg 128 (hm _ (by simp)),
      hg (c.levels.length * ligColsCap) (hm _ (by simp)),
      hg (c.levels.length * oodSlots) (hm _ (by simp)), hg yrLogCap (hm _ (by simp)),
      hg (c.levels.length + 1) (hm _ (by simp))]
    unfold osSizesL
    simp only [List.append_eq, List.nil_append, List.append_assoc, List.singleton_append]
  · -- bufs
    have hRHS : (bases b0 (osSizesL c)).map (fun b ↦ ofK (addressOfIndex b)) =
        (List.range (osSizesL c).length).map (osPtrAt c b0) := by
      refine List.ext_getElem (by simp [length_bases]) fun j h1 h2 ↦ ?_
      simp only [List.getElem_map, List.getElem_range, osPtrAt, osBase]
      rw [List.getD_eq_getElem _ _ (by simpa using h1)]
    have hlen16 : (osSizesL c).length = 10 + c.levels.length + 6 := by simp [osSizesL]; omega
    rw [osBodyAc_allocsV]
    unfold osAllocsV
    simp only [List.map_append]
    rw [hlv.1, hwps, hRHS, hlen16, List.range_add, List.range_add]
    simp only [List.map_append, headAllocsV, finAllocsV, osHeapAV, List.map_cons, List.map_nil, tT,
      fPT, fPT1, fBD, fLS, fICH]
    simp (disch := omega) only [osSigma_headV]
    have eT : osIxT c = 10 + c.levels.length + 0 := by unfold osIxT; omega
    have ePT : osIxPT c = 10 + c.levels.length + 1 := by unfold osIxPT; omega
    have ePT1 : osIxPT1 c = 10 + c.levels.length + 2 := by unfold osIxPT1; omega
    have eBD : osIxBD c = 10 + c.levels.length + 3 := by unfold osIxBD; omega
    have eLS : osIxLS c = 10 + c.levels.length + 4 := by unfold osIxLS; omega
    have eICH : osIxICH c = 10 + c.levels.length + 5 := by unfold osIxICH; omega
    rw [List.append_assoc _ [(osAtOf c b0).T]]
    refine congrArg₂ (· ++ ·) (congrArg₂ (· ++ ·) rfl ?_) ?_
    · rw [List.map_map]; rfl
    · rw [List.map_map]
      show [osPtrAt c b0 (osIxT c), osPtrAt c b0 (osIxPT c), osPtrAt c b0 (osIxPT1 c),
        osPtrAt c b0 (osIxBD c), osPtrAt c b0 (osIxLS c), osPtrAt c b0 (osIxICH c)] = _
      rw [eT, ePT, ePT1, eBD, eLS, eICH]
      rfl
  · -- lp
    intro i h
    have hi : i < c.levels.length := by rwa [osLvKOf_length] at h
    rw [(osLvKOf_getV (osSigma c tr σ0 c0 c2 b0) c 0 c.levels (osHead c).2 i hi).1, (mkCall_fV _ _).2]
    simp only [Nat.zero_add]
    obtain ⟨a, b, d, e, f, hfs⟩ := lvM_fsV c i c.levels[i] (sAtV c i)
    unfold lpCallS
    dsimp only
    rw [hfs]
    simp only [List.cons_append, List.nil_append, List.map_cons, List.map_nil, List.getD_cons_succ,
      List.getD_cons_zero]
    exact osSigma_qposV hlen hi (hpo i hi)
  · -- lq
    intro i h c' hc' hk
    have hi : i < c.levels.length := by rwa [osLvKOf_length] at h
    rw [(osLvKOf_getV (osSigma c tr σ0 c0 c2 b0) c 0 c.levels (osHead c).2 i hi).2] at hc'
    simp only [Nat.zero_add] at hc'
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hc'
    rw [(mkCall_fV (osSigma c tr σ0 c0 c2 b0) x).1] at hk
    rw [(mkCall_fV (osSigma c tr σ0 c0 c2 b0) x).2, lvB_callsV (osSigma c tr σ0 c0 c2 b0) c i c.levels[i] (sAtV c i) (hrw i hi) x hx hk]
    exact osSigma_wpV hlen hi

end Sigma

/-- **The values hold at every arm and rate.** -/
theorem os_call_vals : os_call_vals_Spec := by
  intro m hm ri hri tr σ0 c0 c2 b0 hlen
  obtain ⟨cfg, hF, hN, -⟩ := candB_sound (candB_all m ri hm hri)
  refine osCallVals_of hlen (by have := hF.n2; omega)
    (by rw [osSizesL_rateV]; exact osSizesL_boundV m hm) (fun i hi ↦ (hF.lv i hi).posOff)
    (fun i hi ↦ ?_)
  obtain ⟨⟨-, -, -, -, -, -, h7, -⟩, -⟩ := hN i hi
  rw [← List.getD_eq_getElem _ default hi, h7]
  split_ifs <;> simp [osKindOf, osKindTable, List.lookup]
end
end LeanVM.Guest.B1
