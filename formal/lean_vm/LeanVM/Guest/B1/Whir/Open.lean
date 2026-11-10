/-
  LeanVM.Guest.B1.Whir.Open

  `open_stacked__L{m}` computes `whirOpen`, from its configuration's facts and its callees'
  meanings.
-/

module

public import LeanVM.Guest.B1.Whir.Levels
public import LeanVM.Guest.B1.Whir.FinishSound
public import LeanVM.Guest.B1.Whir.Flatness
public import LeanVM.Guest.B1.Whir.Witness

/-!
# A candidate, soundly

`open_generic`: a specialization whose body is the template at `c` (`osBody c`), whose levels
have their facts and callees (`LevelsOk`), whose finish has its static facts (`FinStatic`) and
whose `opening_queries` calls are the levels' (`osQCalls c = osQCallsL …`): a call establishes
`OpenOutW` at the witness's words and openings. The head stores the root's halves and starts
level `0` (`osHead_lvIn`); the levels and the closing rounds run `whirLevelsOpen`
(`osLevels_sound`); the finish returns the terminal (`osFinish_sound`).
-/

namespace LeanVM.Guest.B1.Whir

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest LeanVM.Guest.B1
open LeanVM.Guest.Value LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile
open LeanVM.Protocol.Verifier

@[expose] public section

variable {C : CallRel} {rd : Reader} {σ : Val}

/-! ## The pieces of the witness -/

theorem whirOpen_eq {μ r : ℕ} {cfg : List Whir.Level} (hdc : Whir.ladder μ r = some cfg)
    (target : E) :
    whirOpen μ r target = whirLevelsOpen μ ((cfg.head?.map (·.fold)).getD 0) 0 cfg ⟨target, [], []⟩ := by
  simp only [whirOpen, hdc, Verifier.liftOption, VerifierProgram.bind_eq, VerifierProgram.ret_bind]

theorem zipIdx_words (c : OsCfg) : ∀ (lvs : List OsLv) (k : ℕ),
    ((lvs.zipIdx k).map fun (p : OsLv × ℕ) ↦ lvWords c p.2 p.1).sum = lvsWords c k lvs
  | [], _ => rfl
  | lv :: rest, k => by
    rw [List.zipIdx_cons, List.map_cons, List.sum_cons, zipIdx_words c rest (k + 1), lvsWords]

theorem osWordsLen_eq (c : OsCfg) : osWordsLen c = lvsWords c 0 c.levels + 2 * c.yrLog := by
  rw [osWordsLen, ← zipIdx_words c c.levels 0]

theorem osReadN_of_readsAt {p : E} {xs : List E} (h : ReadsAt rd p xs) :
    osReadN rd p xs.length = xs := by
  refine List.ext_getElem (by simp [osReadN]) fun i h1 h2 ↦ ?_
  simp only [osReadN, List.getElem_map, List.getElem_range, osMemRead]
  rw [(h i h2).2]
  rfl

theorem osQCallsL_openings (Vm : FrameMap) (c : OsCfg) (L : ℕ → OsLv) :
    ∀ (lvs : List OsLv) (k : ℕ) (st : OsSt), (∀ i < lvs.length, L (k + i) = lvs.getD i default) →
      ((osQCallsL c k lvs st).zipIdx k).map (fun (p : (String × List V × List V) × ℕ) ↦
        osLevelW rd Vm p.2 (L p.2) p.1.1 (p.1.2.1.map σ) (p.1.2.2.map σ)) =
        osLevelsW rd Vm σ c k lvs st
  | [], _, _, _ => rfl
  | lv :: rest, k, st, h => by
    simp only [osQCallsL, List.zipIdx_cons, List.map_cons, osLevelsW]
    rw [osQCallsL_openings Vm c L rest (k + 1) _ fun i hi ↦ by
        have := h (i + 1) (by simp; omega)
        rwa [show k + (i + 1) = k + 1 + i by ring] at this]
    have h0 := h 0 (by simp)
    simp only [Nat.add_zero, List.getD_cons_zero] at h0
    simp only [h0]

/-! ## The head -/

theorem osHead_roots {c : OsCfg} (h : AllOk C rd σ (osHead c).1) :
    LoadHolds rd (σ (.n osRoots)) 0 (σ (.n 6)) ∧ LoadHolds rd (σ (.n osRoots)) 1 (σ (.n 7)) := by
  have m1 : osLd 6 osRoots 0 ∈ (osHead c).1 := by simp [osHead]
  have m2 : osLd 7 osRoots 1 ∈ (osHead c).1 := by simp [osHead]
  exact ⟨(holds_load _ _ _).mp (h _ m1), (holds_load _ _ _).mp (h _ m2)⟩

theorem osHead_st (c : OsCfg) : (osHead c).2 =
    { k := 36, fs := [0, 1, 2, 3, 4], cb := 8, co := 0, claim := 5, pad := none, mats := [] } := rfl

/-! ## A candidate -/

/-- The finish's static facts and `fold_final_msg`'s meaning. -/
structure FinStatic (rd : Reader) (C : CallRel) (c : OsCfg) : Prop where
  n2 : 2 ≤ c.levels.length
  yr : c.yrLevel = c.levels.length - 1
  ylog : 1 ≤ c.yrLog
  ylen : 2 ^ c.yrLog = c.yrLen
  lv : ∀ i < c.yrLevel, LvFin c (c.levels.getD i default) (c.levels.getD (i + 1) default)
  loops : ∀ i < c.yrLevel,
    FnIs (c.resLoop i) (osParams 7) (resLoopBody i (c.levels.getD i default) (c.resLoop i))
  nF : lvsFolds c.levels = c.nFolds
  lane : (c.levels.headD default).folds ≤ c.nFolds
  mu40 : c.nFolds + c.yrLog ≤ pointCap
  ffm : ∀ a r, C ("fold_final_msg__L" ++ natStr c.yrLog) a r → MeaningFoldFinalMsg c.yrLog rd a r

/-- **A candidate, soundly**: from its body, its levels' facts and callees, its finish's facts
and its `opening_queries` calls, a call establishes `OpenOutW` at the witness's words and
openings. -/
theorem open_generic {V : FrameMap} (hU : UnfoldsV rd C V) (hle : CallRel.Le C (coreProgram.Rel rd))
    {c : OsCfg} {μ r : ℕ} {cfg : List Whir.Level} (hdc : Whir.ladder μ r = some cfg)
    (hmu : c.nFolds + c.yrLog = μ)
    (hshape : stackShape μ r = ((c.levels.headD default).depth, lvWidth 0 (c.levels.headD default)))
    (hoff0 : (c.levels.headD default).foldsOff = 0)
    (hlane : (cfg.head?.map (·.fold)).getD 0 = (c.levels.headD default).folds)
    (hq : osQCalls c = osQCallsL c 0 c.levels (osHead c).2)
    (hLOk : LevelsOk rd C σ c μ 0 c.levels cfg) (hFS : FinStatic rd C c)
    {fn : Fn} (hfp : fn.params = osParams 10) (hfb : fn.body = osBody c)
    {root : Digest} {fs : List E} {target root0 root1 cur tabs : E} {rets : List E}
    (hfs : fs.length = 5) (hroot : (root0, root1) = digestHalves root) (hwt : WinTabs rd tabs)
    (hp : fn.params.map σ = fs ++ [target, root0, root1, cur, tabs])
    (hh : Stmt.HoldsList C rd σ fn.body False (fun rs ↦ rs = rets)) :
    OpenOutW rd μ r root fs target cur rets (osReadN rd (σ (.n 8)) (osWordsLen c))
      ((osQCalls c).zipIdx.map fun ((name, args, rets), l) ↦
        osLevelW rd V l (c.levels.getD l default) name (args.map σ) (rets.map σ)) := by
  -- the parameters
  obtain ⟨f0, f1, f2, f3, f4, rfl⟩ : ∃ f0 f1 f2 f3 f4, fs = [f0, f1, f2, f3, f4] := by
    match fs, hfs with
    | [f0, f1, f2, f3, f4], _ => exact ⟨f0, f1, f2, f3, f4, rfl⟩
  rw [hfp] at hp
  simp only [osParams, List.range_succ, List.range_zero, List.map_cons, List.map_nil,
    List.nil_append, List.cons_append, List.cons.injEq, and_true] at hp
  obtain ⟨p0, p1, p2, p3, p4, p5, p6, p7, p8, p9⟩ := hp
  -- the body
  rw [hfb, osBody_eq, holdsList_flat_ret _ (osBodyA_flat c)] at hh
  obtain ⟨hA, hret⟩ := hh
  simp only [osBodyA, allOk_append] at hA
  obtain ⟨⟨⟨hH, hL⟩, hT⟩, hFin⟩ := hA
  obtain ⟨lv0, rest, hlv⟩ : ∃ lv0 rest, c.levels = lv0 :: rest := by
    rcases h : c.levels with _ | ⟨lv0, rest⟩
    · have := hFS.n2; rw [h] at this; simp at this
    · exact ⟨lv0, rest, rfl⟩
  have hhead : c.levels.headD default = lv0 := by rw [hlv]; rfl
  rw [hhead] at hshape hoff0 hlane
  -- level 0's start
  obtain ⟨hr0, hr1⟩ := osHead_roots hH
  have hwt' : WinTabs rd (σ (.n osTabs)) := by rw [show osTabs = 9 from rfl, p9]; exact hwt
  have hin : LvIn rd σ 0 lv0 (osHead c).2 ⟨target, [], []⟩ [] [(root, stackShape μ r)] root := by
    rw [osHead_st]
    refine ⟨rfl, by unfold u128Bound; positivity, fun p hp ↦ by simp at hp, matsOk_nil σ, ?_, ?_,
      fun j h ↦ absurd h (by simp), rfl, ?_, ?_, ?_, rfl, fun r hr ↦ absurd hr (by simp)⟩
    · simp [recsDeficit, p5]
    · simp [hoff0]
    · simp [hshape]
    · rw [p6] at hr0; rw [← hroot]; exact hr0
    · rw [p7] at hr1; rw [← hroot]; exact hr1
  rw [hlv] at hL hT hLOk
  obtain ⟨xs, recs', gs, fold, T, R', hxl, hrd, hrun, hrl, hrecs, -, hgl, hfch, hfm, hfl, hTr, hTl⟩ :=
    osLevels_sound hU hle hwt' lv0.folds 0 lv0 rest cfg _ _ [] _ root hLOk hin hL hT
  simp only [List.nil_append] at hrun hfch hfch
  -- the finish
  have hy : c.yrLevel = rest.length := by rw [hFS.yr, hlv]; simp
  have hFI : FinishIn rd C σ c (osTail c (osLevels c 0 (lv0 :: rest) (osHead c).2).2).2.2 gs T fold
      recs' := by
    refine ⟨hFS.n2, hFS.yr, hFS.ylog, hFS.ylen, by rw [hrl, hy], fun i hi ↦ ?_, hFS.lv, hFS.loops,
      by rw [hgl, ← hFS.nF, hlv], hfch, hTl, hTr, hfm, by rw [hfl]; omega, hFS.lane,
      hFS.mu40, hFS.ffm⟩
    have hi' : i < recs'.length := by rw [hrl, ← hy]; exact hi
    have := hrecs i hi'
    rw [Nat.zero_add, ← hlv] at this
    rw [List.getD_eq_getElem recs' default hi']
    exact this
  rw [hlv] at hFin
  obtain ⟨pt, pt1, hrv, hpt, hpt1⟩ := osFinish_sound hle hFI hFin
  rw [hhead, hmu] at hpt hpt1
  -- the words and the openings
  have hcur : (osHead c).2.cur σ = cur := by
    rw [osHead_st]; simp [OsSt.cur, p8]
  rw [hcur] at hrd
  have hwords : osReadN rd (σ (.n 8)) (osWordsLen c) = xs := by
    rw [p8, osWordsLen_eq, hlv, ← hxl]
    exact osReadN_of_readsAt hrd
  have hops : ((osQCalls c).zipIdx.map fun ((name, args, rets), l) ↦
      osLevelW rd V l (c.levels.getD l default) name (args.map σ) (rets.map σ)) =
      osLevelsW rd V σ c 0 (lv0 :: rest) (osHead c).2 := by
    rw [hq, ← hlv]
    exact osQCallsL_openings V c (fun l ↦ c.levels.getD l default) c.levels 0 (osHead c).2
      fun i _ ↦ by rw [Nat.zero_add]
  rw [hwords, hops]
  -- the run and the returns
  have hF0 : (osHead c).2.F σ = ⟨[f0, f1, f2, f3, f4], []⟩ := by
    rw [osHead_st]; simp [OsSt.F, p0, p1, p2, p3, p4]
  rw [hF0] at hrun
  have hrun2 : RunsWith (whirOpen μ r target) ⟨[f0, f1, f2, f3, f4], []⟩ xs
      (osLevelsW rd V σ c 0 (lv0 :: rest) (osHead c).2) [(root, stackShape μ r)]
      ⟨rotPt gs T lv0.folds,
        (recs'.flatMap recGlued).foldl (fun w g ↦ w + g.scalar * g.weightAt ((gs ++ T).drop g.foldStart)) 0,
        multilinearEval (fold.take c.yrLen) T,
        σ (.n (osTail c (osLevels c 0 (lv0 :: rest) (osHead c).2).2).2.1.claim) +
          T.prod * recsDeficit recs' gs⟩
      ((osTail c (osLevels c 0 (lv0 :: rest) (osHead c).2).2).2.1.F σ) R' := by
    rw [whirOpen_eq hdc, hlane]; exact hrun
  refine ⟨_, _, R', hrd, hrun2, ?_, pt, pt1, ?_, hpt, hpt1⟩
  · simp [hgl, hTl, ← hFS.nF, hlv, ← hmu]; have := hFS.lane; rw [hhead, ← hFS.nF, hlv] at this
    omega
  · rw [← hret, ← hrv]
    simp only [osBodyRet, hlv]

end
end LeanVM.Guest.B1.Whir
