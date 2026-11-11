/-
  LeanVM.Guest.B1.Whir.Open

  `open_stacked__L{m}` computes `whirOpen`, from its candidate's facts.
-/

module

public import LeanVM.Protocol.Verifier.WhirTarget
public import LeanVM.Guest.B1.Whir.OpenAux
public import LeanVM.Guest.B1.Whir.InterfaceW
public import LeanVM.Guest.B1.Opening.QueriesW
public import LeanVM.Guest.B1.Whir.Head
public import LeanVM.Guest.B1.Whir.Tail
public import LeanVM.Guest.B1.Whir.InnerEq
public import LeanVM.Guest.B1.Whir.Flatness
public import LeanVM.Guest.B1.Whir.Roots
public import LeanVM.Guest.B1.Whir.DataSpec

/-!
# A candidate, soundly

`open_generic`: a candidate `m` whose core IR is its template (`OsData m`) and whose
configuration has the facts `CandFacts m μ r cfg` (the configuration `Whir.ladder μ r = cfg`,
level by level; the `LIG_*` rows; the vanishing tables), its callees by their meanings: a call
establishes `OpenOut`. The head, the levels, the tail and the finish compose
(`osHead_sound`, `osLevels_sound`, `osTail_sound`, `osFinish_sound`), the glued weight by
`inner_eq`.
-/

namespace LeanVM.Guest.B1.Whir

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest LeanVM.Guest.B1
open LeanVM.Guest.Value LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile
open LeanVM.Protocol.Verifier

@[expose] public section

/-- A level's row facts. -/
structure LvStatic (c : OsCfg) (i : ℕ) (lv : OsLv) : Prop where
  ml1 : 1 ≤ lv.logCols
  posOff : lv.posOff < u128Bound
  q2 : 2 ≤ lv.queries
  qo : lv.queries / resBatch < ordG
  qu : lv.queries / resBatch < u128Bound
  pre : lv.prefixLen + c.yrLog = lv.logCols
  rfo : lv.resFoldOff = lv.foldsOff + lv.folds
  le : lv.foldsOff + lv.folds ≤ c.nFolds
  cols : c.nFolds - (lv.foldsOff + lv.folds) + c.yrLog = lv.logCols
  vanish : vanishOk lv.vanish lv.logCols = true
  lc : i * ligColsCap < u128Bound
  van : lv.vanish = vanishOff lv.logCols

/-- **A candidate's facts**: its configuration against the Spec's, its rows. -/
structure CandFacts (c : OsCfg) (μ r : ℕ) (cfg : List Whir.Level) : Prop where
  dc : Whir.ladder μ r = some cfg
  lok : LevelsOk c μ 0 c.levels cfg
  shape : stackShape μ r = ((c.levels.headD default).depth,
    lvWidth 0 (c.levels.headD default))
  off0 : (c.levels.headD default).foldsOff = 0
  n2 : 2 ≤ c.levels.length
  yr : c.yrLevel = c.levels.length - 1
  ylog : 1 ≤ c.yrLog
  last : (c.levels.getLastD default).logCols = c.yrLog
  lastF : (c.levels.getLastD default).foldsOff +
    (c.levels.getLastD default).folds = c.nFolds
  ylen : 2 ^ c.yrLog = c.yrLen
  mu : c.nFolds + c.yrLog = μ
  mu40 : μ ≤ pointCap
  lane : (c.levels.headD default).folds ≤ c.nFolds
  next : ∀ i, i + 1 < c.levels.length →
    (c.levels.getD (i + 1) default).foldsOff =
      (c.levels.getD i default).foldsOff + (c.levels.getD i default).folds
  lv : ∀ i < c.levels.length, LvStatic c i (c.levels.getD i default)

variable {rd : Reader} {σ : Val}

/-- A coordinate after `Fo` fold challenges: a fold challenge, then a tail challenge. -/
theorem load_xof {F T : List E} {Fo t tch : ℕ} (hFo : Fo ≤ F.length)
    (hfch : ∀ j (h : j < F.length), LoadHolds rd (σ (.n osFch)) j F[j])
    (hT : ReadsAt rd (σ (.n tch)) T) (ht : t < F.length - Fo + T.length) :
    LoadHolds rd (σ (.n (if t < F.length - Fo then ((osFch, Fo + t) : ℕ × ℕ)
        else (tch, t - (F.length - Fo))).1))
      (if t < F.length - Fo then ((osFch, Fo + t) : ℕ × ℕ) else (tch, t - (F.length - Fo))).2
      ((F.drop Fo ++ T).getD t 0) := by
  by_cases h : t < F.length - Fo
  · simp only [h, ↓reduceIte]
    rw [List.getD_eq_getElem _ _ (by simp; omega), List.getElem_append_left (by simp; omega),
      List.getElem_drop]
    exact hfch _ _
  · simp only [h, ↓reduceIte]
    rw [List.getD_eq_getElem _ _ (by simp; omega), List.getElem_append_right (by simp; omega)]
    simp only [List.length_drop]
    exact hT _ _

theorem rs_getD {rs : List OsRec} {i : ℕ} (h : i < rs.length) : rs.getD i default = rs[i] :=
  List.getD_eq_getElem _ _ h

theorem lv_getD {c : OsCfg} {i : ℕ} (h : i < c.levels.length) :
    c.levels.getD i default = c.levels[i] := List.getD_eq_getElem _ _ h

/-- `levelTail` with its tail rounds as the guest runs them. -/
theorem levelTail_eq (lane ml : ℕ) (ms : List E) (s : WhirStateT) :
    levelTail lane ml ms s =
      ((tailRoundsT ml s.target s.quad).bind fun r ↦ VerifierProgram.ret ([] ++ r.1, r.2)).bind
          fun r ↦
        VerifierProgram.ret (⟨(s.folds ++ r.1).drop lane ++ (s.folds ++ r.1).take lane,
          s.glued.foldl (fun weight claim ↦
            weight + claim.scalar * claim.weightAt (s.folds.drop claim.foldStart ++ r.1)) 0,
          multilinearEval ms r.1, r.2⟩ : WhirEnd) := by
  simp only [levelTail, VerifierProgram.bind_eq, VerifierProgram.pure_eq,
      VerifierProgram.bind_assoc, VerifierProgram.ret_bind,
    List.nil_append]

/-- **`whirOpen`, as the guest runs it**: the first round polynomial, the levels' heads, the
tail. -/
theorem whirOpen_eq {μ r : ℕ} {cfg : List Whir.Level} (hdc : Whir.ladder μ r = some cfg)
    (hne : cfg ≠ []) (target : E) :
    whirOpen μ r target = (sumcheckRoundPoly 3 target none).bind fun quad ↦
      (whirLevelsHead μ 0 cfg ⟨target, quad, [], []⟩).bind fun res ↦
        levelTail ((cfg.head?.map (·.fold)).getD 0) res.2.1 res.1 res.2.2 := by
  rw [whirOpen, hdc]
  simp only [Verifier.liftOption, VerifierProgram.bind_eq, VerifierProgram.ret_bind]
  exact prog_bind_congr fun quad ↦ whirLevelsOpen_eq _ _ 0 cfg _ hne

/-- A padded buffer's words. -/
theorem readsAt_padded {rd : Reader} {p : E} {P : List E} {n : ℕ} (f : E → E)
    (h : ∀ i < P.length + n, LoadHolds rd p i (f (P.getD i 0))) :
    ReadsAt rd p (P.map f ++ List.replicate n (f 0)) := by
  intro k hk
  simp only [List.length_append, List.length_map, List.length_replicate] at hk
  by_cases h1 : k < P.length
  · rw [List.getElem_append_left (by simpa using h1), List.getElem_map]
    have := h k hk
    rwa [List.getD_eq_getElem _ _ h1] at this
  · rw [List.getElem_append_right (by simpa using h1), List.getElem_replicate]
    have := h k hk
    rwa [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega), Option.getD_none] at this

/-- **A configuration, soundly**: from its body, its facts, its callees' meanings and the rate's
selector naming its levels' rows, a call establishes `OpenOut`. -/
theorem open_generic {name : String} {μ r : ℕ} {c : OsCfg} {cfg : List Whir.Level}
    (hfnc : FnIs name (osParams 10) (osBody c))
    (hF : CandFacts c μ r cfg) (hcal : CalleesOk rd c 0 c.levels)
    (hfold : ∀ args rets, coreProgram.Rel rd "opening_fold" args rets →
      MeaningOpeningFold rd args rets)
    (hfm : ∀ args rets, coreProgram.Rel rd ("fold_final_msg__L" ++ natStr c.yrLog)
      args rets → MeaningFoldFinalMsg c.yrLog rd args rets)
    {root : Digest} {fs : List E} {sel target root0 root1 cur : E} {rets : List E}
    (hfs : fs.length = 5) (hroot : (root0, root1) = digestHalves root)
    {C : CallRel} (hle : CallRel.Le C (coreProgram.Rel rd)) {V : FrameMap} (hU : UnfoldsV rd C V)
    {Wf : ℕ → OsLv → List E → List E → List QW} (hqw : QWOk rd C Wf 0 c.levels)
    {σ : Val} (hrat : RatesOk σ c 0 c.levels) {fn' : Fn} (hfind' : coreProgram.find? name = some fn')
    (hp' : fn'.params.map σ = sel :: fs ++ [target, root0, root1, cur])
    (hh : Stmt.HoldsList C rd σ fn'.body False (fun rs ↦ rs = rets)) :
    OpenOutW rd μ r root fs target cur rets (readN rd cur (osWordsLen c))
      ((osQCalls c 0 c.levels (osHead c).2).map
        (fun e ↦ lvOs rd σ V (Wf e.1 e.2.1) e.1 e.2.1 e.2.2)) := by
  have hn := hF.n2
  obtain ⟨fn, hfind, hps, hbody⟩ := hfnc
  rw [hfind] at hfind'
  cases hfind'
  have hp := hp'
  rw [hbody, osBody_split, holdsList_flat_ret _ (osBodyA_flat c)] at hh
  obtain ⟨hok, hret⟩ := hh
  rw [hps] at hp
  simp only [osBodyA, allOk_append] at hok
  obtain ⟨⟨⟨hH, hL⟩, hT⟩, hFin⟩ := hok
  -- the head
  obtain ⟨c0, c2, hrd0, hrun0, hin0, hcur0, hwt⟩ :=
    osHead_sound (c := c) hfs hp hroot hF.shape hF.off0 (allOk_mono hle hH)
  -- the levels
  obtain ⟨xs1, os1, R', ms, ws', rs, hrd1, hrun1, hmsl, hfmr, hgl, hrsl, hrec, hfl, hfch, hq, ht,
    hfs1, hpad1, hco1, hcur1, hos1, hxl1, hmt1⟩ :=
    osLevels_sound hle hU c.levels cfg 0 (osHead c).2 _ _ root hF.lok hcal hqw hrat hin0 hwt hL
  obtain ⟨p, hpp⟩ := osLevels_pad c c.levels 0 (osHead c).2 (by
    intro h; rw [h] at hn; simp at hn)
  set stL := (osLevels c 0 c.levels (osHead c).2).2 with hstL
  -- the tail
  obtain ⟨xs2, T, F', hxl2, hTl, hrd2, hrun2, hTr, -⟩ := osTail_sound hfold hF.ylog hfs1
    (by have := hco1; unfold u128Bound; omega) (by rw [hpp] at hpad1 ⊢; exact hpad1) ws' hq ht
    (allOk_mono hle hT)
  set stT := (osTail c stL).2 with hstT
  have hmtT : MatsOk σ stT.1.mats := by
    have e : stT.1.mats = stL.mats := by simp [stT, osTail, osFolds_mats]
    rw [e]; exact hmt1
  set F := ws'.folds with hFdef
  have hFl : F.length = c.nFolds := by
    rw [hfl, ← hF.lastF]
  set lane := (c.levels.headD default).folds with hlane
  obtain ⟨hlane', hcne⟩ := levelsOk_lane hF.lok
  -- the records
  have hrec' : ∀ i (hi : i < c.levels.length), RecStored rd σ c i c.levels[i] (rs.getD i default) :=
    fun i hi ↦ by
      have := hrec i (by rw [hrsl]; exact hi) hi
      rw [rs_getD (by rw [hrsl]; exact hi)]
      simpa using this
  have hsta : ∀ i (hi : i < c.levels.length), LvStatic c i c.levels[i] := fun i hi ↦ by
    have := hF.lv i hi; rwa [lv_getD hi] at this
  have hcal' : ∀ i (hi : i < c.levels.length), LvCallees rd c i c.levels[i] := fun i hi ↦ by
    simpa using calleesOk_at hcal i hi
  have hrat' : ∀ i (hi : i < c.levels.length), LvRate σ c i c.levels[i] := fun i hi ↦ by
    simpa using ratesOk_at hrat i hi
  -- the levels' inputs to the finish
  have hTr' : ∀ j (h : j < T.length), LoadHolds rd (σ (.n stT.2)) j T[j] := hTr
  have hbasis : ∀ i (hi : i < c.levels.length), BasisIn rd σ c stT.2 i c.levels[i]
      (βof c rs i * (rs.getD i default).lam ^ c.levels[i].queries) (Xof rs F T i) := fun i hi ↦ by
    have hr := hrec' i hi
    have hs := hsta i hi
    refine ⟨by unfold βof; exact hr.rq.beta, fun t ht ↦ ⟨(vanish_inv hs.vanish t (by
      rw [← hs.pre]; exact ht)).2, ?_⟩⟩
    have hpl : c.levels[i].prefixLen = F.length - (rs.getD i default).F := by
      have := hs.pre; have := hs.cols; rw [hFl, hr.F]; omega
    have hrf : c.levels[i].resFoldOff = (rs.getD i default).F := by rw [hs.rfo, hr.F]
    unfold coordSrc
    rw [hpl, hrf]
    exact load_xof (by rw [hr.F, hFl]; exact hs.le) hfch hTr (by
      rw [hTl, hr.F, hFl]; have := hs.cols; have := hs.pre; omega)
  have hres : ∀ i (hi : i < c.levels.length), ResIn rd σ c i c.levels[i] (Pof rs i)
      ((rs.getD i default).lam) :=
    fun i hi ↦ by
      have hr := hrec' i hi
      have hs := hsta i hi
      exact ⟨(hcal' i hi).res, hrat' i hi, hs.van, hs.posOff, hs.lc, hs.pre,
        fun j hj ↦ hr.rq.pos j hj, hr.rq.lam0, hr.rq.mu⟩
  have hood : OodAll rd σ c stT.2 (Λof rs) (Zof rs) (Yof rs F T) (c.levels.headD default).logCols
      1 c.levels.tail := by
    refine oodAll_of _ _ _ fun i hi ↦ ?_
    have hi' : i + 1 < c.levels.length := by simp at hi; omega
    have hr := hrec' i (by omega)
    have hs := hsta i (by omega)
    have hnf : i ≠ c.yrLevel := by rw [hF.yr]; omega
    have hprev : (if i = 0 then (c.levels.headD default).logCols
        else (c.levels.tail.getD (i - 1) default).logCols) = (c.levels[i]'(by omega)).logCols := by
      rcases i with _ | i
      · simp only [↓reduceIte, List.headD_eq_head?_getD, List.head?_eq_getElem?,
          List.getElem?_eq_getElem (show 0 < c.levels.length by omega), Option.getD_some]
      · simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (show i + 1 < c.levels.length
          by omega)]
    obtain ⟨z, hz⟩ : ∃ z, (rs.getD i default).z = some z := Option.ne_none_iff_exists'.mp
      (hr.z.2.1 hnf)
    obtain ⟨hzl, hzat⟩ := hr.z.2.2 z hz
    have hfo : (c.levels.tail.getD i default).foldsOff = (rs.getD i default).F := by
      have := hF.next i hi'
      rw [List.getD_eq_getElem?_getD, List.getElem?_tail, ← List.getD_eq_getElem?_getD, this,
        lv_getD (by omega), hr.F]
    have hzf : (c.levels[i]'(by omega)).logCols - c.yrLog = F.length - (rs.getD i default).F := by
      have := hs.cols; rw [hFl, hr.F]; omega
    rw [hprev]
    refine ⟨?_, fun t ht ↦ ⟨?_, ?_⟩⟩
    · have := hr.rq.ood hnf
      simp only [Λof, Nat.add_sub_cancel_left]
      rwa [add_comm 1 i]
    · simp only [Zof, Nat.add_sub_cancel_left, hz, Option.getD_some]
      have ht' : t < z.length := by rw [hzl]; have := hs.cols; omega
      rw [List.getD_eq_getElem _ _ ht', add_comm 1 i]
      exact hzat t ht'
    · simp only [Yof, Nat.add_sub_cancel_left, Xof, oodSrc, hzf, hfo]
      exact load_xof (by rw [hr.F, hFl]; exact hs.le) hfch hTr (by
        rw [hTl, hr.F, hFl]; have := hs.cols; omega)
  -- the finish
  obtain ⟨hfin, hpt, hne⟩ := osFinish_sound (rd := rd) (σ := σ) (c := c) (st := stT.1) (tch := stT.2)
    (ms := ms) (T := T) (Pt := (F ++ T).drop lane ++ (F ++ T).take lane)
    (β := βof c rs) (X := Xof rs F T) (P := Pof rs) (W := Wof rs) (Λ := Λof rs) (Z := Zof rs)
    (Y := Yof rs F T) (Lam := fun i ↦ (rs.getD i default).lam) (fun _ _ ↦ rfl) hfm (by rw [hmsl, hF.ylen]) hfmr hTl hTr
    (ptSrc_ok hFl hTl hF.lane hfch hTr') hbasis hres hood hn hmtT (allOk_mono hle hFin)
  -- the glued weight
  have hlvfin : ∀ i < c.levels.length, LvFin c rs F T i := fun i hi ↦ by
    have hr := hrec' i hi
    have hs := hsta i hi
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hr.z.1, fun h ↦ ?_⟩
    · rw [hr.F, hFl]; exact hs.le
    · rw [lv_getD hi, hFl, hr.F, hTl]; exact hs.cols
    · rw [lv_getD hi]; exact hr.ml
    · rw [lv_getD hi]; exact hr.rq.qlen
    · rw [lv_getD hi]; exact hs.pre
    · rw [lv_getD hi]; exact vanish_val hs.vanish
    · rw [lv_getD hi]; exact fun t ht ↦ (vanish_inv hs.vanish t ht).1
    · rw [lv_getD hi]; exact fun t ht ↦ hne i hi t (by rw [hs.pre]; exact ht)
    · obtain ⟨z, hz⟩ := Option.ne_none_iff_exists'.mp (hr.z.2.1 h)
      exact ⟨z, hz, by rw [lv_getD hi]; exact (hr.z.2.2 z hz).1⟩
  have hinner := inner_eq (rs := rs) (F := F) (T := T) (by rw [hrsl]) (by omega) hF.yr hTl hlvfin
  have hrets := hret.symm.trans hfin
  have hreads : ReadsAt rd cur ([c0, c2] ++ (xs1 ++ (xs2 ++ []))) := by
    refine readsAt_append hrd0 (readsAt_append ?_ (readsAt_append ?_ (readsAt_nil _ _)))
    · rw [show [c0, c2].length = 2 from rfl, ← hcur0]; exact hrd1
    · rw [show [c0, c2].length = 2 from rfl, ← hcur0, ← hcur1]; exact hrd2
  have hxlen : ([c0, c2] ++ (xs1 ++ (xs2 ++ []))).length = osWordsLen c := by
    simp only [List.length_append, List.length_cons, List.length_nil, hxl1, hxl2, osWordsLen]
    omega
  rw [← hxlen, readN_of_readsAt hreads, ← hos1,
    show os1 = [] ++ (os1 ++ ([] ++ [])) by simp]
  refine ⟨⟨(F ++ T).drop lane ++ (F ++ T).take lane, ws'.glued.foldl (fun weight claim ↦
      weight + claim.scalar * claim.weightAt (F.drop claim.foldStart ++ T)) 0,
      multilinearEval ms T, σ (.n stT.1.t)⟩, F', R', ?_, ?_, ?_, σ (.n (stT.1.k + 1)),
    σ (.n (stT.1.k + 1 + 1)), ?_, ?_, ?_⟩
  · exact hreads
  · rw [whirOpen_eq hF.dc hcne target]
    refine RunsWith.bind' (RunsTo.withRoots hrun0 _) (RunsWith.bind' hrun1 ?_)
    rw [levelTail_eq, hF.last, hlane']
    exact RunsWith.bind' (RunsTo.withRoots hrun2 R') (runsWith_ret _ _ _)
  · have := hF.lane; have := hF.mu
    simp [hFl, hTl, hF.mu]; omega
  · rw [hrets]
    simp only [hgl, List.nil_append, hinner]
  · have := readsAt_padded (rd := rd) (P := (F ++ T).drop lane ++ (F ++ T).take lane)
      (n := pointCap - μ) id (fun i hi ↦ (hpt i (by
        have := hF.lane; have := hF.mu; have := hF.mu40
        simp [hFl, hTl, hF.mu] at hi; omega)).1)
    simpa using this
  · have := readsAt_padded (rd := rd) (P := (F ++ T).drop lane ++ (F ++ T).take lane)
      (n := pointCap - μ) (fun x ↦ 1 + x) (fun i hi ↦ (hpt i (by
        have := hF.lane; have := hF.mu; have := hF.mu40
        simp [hFl, hTl, hF.mu] at hi; omega)).2)
    rwa [add_zero] at this

end
end LeanVM.Guest.B1.Whir
