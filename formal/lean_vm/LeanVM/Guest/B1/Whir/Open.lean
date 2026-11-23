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
import LeanVM.Guest.ValRef
import LeanVM.Guest.Data.ValNames.«open_stacked__L»

/-!
# A candidate, soundly

`open_generic`: a specialization whose body is the template at `c` (`osBody c`), whose levels
have their facts and callees (`LevelsOk`) and their rows at the rate's selector (`LvRate`), and
whose finish has its static facts (`FinStaticS`): a call establishes `OpenOutW` at the
witness's words and openings. The head stores the root's halves and starts
level `0` (`osHead_roots`, `LvIn`); the levels and the closing rounds run `whirLevelsOpen`
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

/-! ## The head -/

theorem osHead_roots {c : OsCfg} (h : AllOk C rd σ (osHead c).1) :
    LoadHolds rd (σ (.n osRoots)) 0 (σ (.n (valf% «open_stacked» "commit_root_0"))) ∧ LoadHolds rd (σ (.n osRoots)) 1 (σ (.n (valf% «open_stacked» "commit_root_1"))) := by
  have m1 : osLd 7 osRoots 0 ∈ (osHead c).1 := by simp [osHead]
  have m2 : osLd 8 osRoots 1 ∈ (osHead c).1 := by simp [osHead]
  exact ⟨(holds_load _ _ _).mp (h _ m1), (holds_load _ _ _).mp (h _ m2)⟩

theorem osHead_st (c : OsCfg) : (osHead c).2 =
    { k := osPadV + 5, fs := [1, 2, 3, 4, 5], cb := 9, co := 0, claim := 6, pad := some osPadV,
      mats := [] } := rfl

theorem osHead_pad {c : OsCfg} (h : AllOk C rd σ (osHead c).1) : PadOk σ (some osPadV) := by
  have hp : AllOk C rd σ (osPad none osPadV).1 := fun s hs ↦ h s (by
    unfold osHead; simp only [List.mem_append]; exact Or.inr hs)
  exact osPad_ok (fun p hp ↦ by simp at hp) hp

/-! ## A candidate -/

/-- The finish's static facts and the meanings of `fold_final_msg`, `is_zero` and
`level_residual_slow`. -/
structure FinStaticS (rd : Reader) (C : CallRel) (c : OsCfg) : Prop where
  n2 : 2 ≤ c.levels.length
  yr : c.yrLevel = c.levels.length - 1
  ylog : 1 ≤ c.yrLog
  ylen : 2 ^ c.yrLog = c.yrLen
  lv : ∀ i < c.yrLevel, LvFin c (c.levels.getD i default) (c.levels.getD (i + 1) default)
  res : ∀ i < c.yrLevel, ∀ a r,
    a.getD 4 0 = gen ^ ((c.levels.getD i default).queries / resBatch) →
    a.getD 5 0 = gen ^ ((c.levels.getD i default).queries % resBatch) →
    C (osResidualName (c.levels.getD i default)) a r →
    MeaningLevelResidual (c.levels.getD i default).queries (c.levels.getD i default).logCols
      (c.levels.getD i default).folds (c.levels.getD i default).highBits rd a r
  nlen : c.levels.length ≤ 64
  nF : lvsFolds c.levels = c.nFolds
  lane : (c.levels.headD default).folds ≤ c.nFolds
  mu40 : c.nFolds + c.yrLog ≤ pointCap
  ffm : ∀ a r, C ("fold_final_msg__L" ++ natStr c.yrLog) a r → MeaningFoldFinalMsg c.yrLog rd a r
  iz : ∀ a r, C "is_zero" a r → MeaningIsZero a r
  slow : ∀ i < c.yrLevel, ∀ a r, C (osSlowName c (c.levels.getD i default)) a r →
    SlowRet (c.levels.getD i default).queries (c.levels.getD i default).prefixLen c.yrLog
      (c.levels.getD i default).vanish rd a r

/-- **A candidate, soundly**: from its body, its levels' facts, callees and rows at the rate's
selector, and its finish's facts, a call establishes `OpenOutW` at the witness's words and
openings. -/
theorem open_generic {V : FrameMap} (hU : UnfoldsV rd C V) (hle : CallRel.Le C (coreProgram.Rel rd))
    {c : OsCfg} {μ r : ℕ} {cfg : List Whir.Level} (hdc : Whir.ladder μ r = some cfg)
    (hmu : c.nFolds + c.yrLog = μ)
    (hshape : stackShape μ r = ((c.levels.headD default).depth, lvWidth 0 (c.levels.headD default)))
    (hoff0 : (c.levels.headD default).foldsOff = 0)
    (hlane : (cfg.head?.map (·.fold)).getD 0 = (c.levels.headD default).folds)
    (hLOk : LevelsOk rd C σ c μ 0 c.levels cfg) (hFS : FinStaticS rd C c)
    (hrate : ∀ i < c.levels.length, LvRate σ c i (c.levels.getD i default))
    {fn : Fn} (hfp : fn.params = osParams 11) (hfb : fn.body = osBody c)
    {root : Digest} {sel : E} {fs : List E} {target root0 root1 cur tabs : E} {rets : List E}
    (hfs : fs.length = 5) (hroot : (root0, root1) = digestHalves root) (hwt : WinTabs rd tabs)
    (hp : fn.params.map σ = sel :: fs ++ [target, root0, root1, cur, tabs])
    (hh : Stmt.HoldsList C rd σ fn.body False (fun rs ↦ rs = rets)) :
    OpenOutW rd μ r root fs target cur rets (osReadN rd (σ (.n (valf% «open_stacked» "cursor@1"))) (osWordsLen c))
      (osLevelsW rd V σ c 0 c.levels (osHead c).2) := by
  -- the parameters
  obtain ⟨f0, f1, f2, f3, f4, rfl⟩ : ∃ f0 f1 f2 f3 f4, fs = [f0, f1, f2, f3, f4] := by
    match fs, hfs with
    | [f0, f1, f2, f3, f4], _ => exact ⟨f0, f1, f2, f3, f4, rfl⟩
  rw [hfp] at hp
  simp only [osParams, List.range_succ, List.range_zero, List.map_cons, List.map_nil,
    List.nil_append, List.cons_append, List.cons.injEq, and_true] at hp
  obtain ⟨-, p0, p1, p2, p3, p4, p5, p6, p7, p8, p9⟩ := hp
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
  have hwt' : WinTabs rd (σ (.n osTabs)) := by rw [show osTabs = 10 from rfl, p9]; exact hwt
  have hin : LvIn rd σ 0 lv0 (osHead c).2 ⟨target, [], []⟩ [] [(root, stackShape μ r)] root := by
    have hpd := osHead_pad hH
    rw [osHead_st]
    refine ⟨rfl, Nat.zero_le _, hpd, ⟨_, rfl⟩, matsOk_nil σ, ?_, ?_,
      fun j h ↦ absurd h (by simp), rfl, ?_, ?_, ?_, rfl, fun r hr ↦ absurd hr (by simp), rfl⟩
    · simp [recsDeficit, p5]
    · simp [hoff0]
    · simp [hshape]
    · rw [p6] at hr0; rw [← hroot]; exact hr0
    · rw [p7] at hr1; rw [← hroot]; exact hr1
  rw [hlv] at hL hT hLOk
  obtain ⟨xs, recs', gs, fold, T, R', hxl, hrd, hrun, hrl, hrecs, -, hgl, hfch, hfm, hfl, hTr, hTl,
    hmT, es, hes, hesl, hesr⟩ :=
    osLevels_sound hU hle hwt' lv0.folds 0 lv0 rest cfg _ _ [] _ root hLOk hin hL hT
  simp only [List.nil_append] at hrun hfch hfch
  -- the finish
  have hy : c.yrLevel = rest.length := by rw [hFS.yr, hlv]; simp
  have hFI : FinishIn rd C σ c (osTail c (osLevels c 0 (lv0 :: rest) (osHead c).2).2).2.2 gs T fold
      recs' := by
    refine ⟨hFS.n2, hFS.yr, hFS.ylog, hFS.ylen, by rw [hrl, hy], fun i hi ↦ ?_, hFS.lv,
      fun i hi ↦ hrate i (by have := hFS.yr; omega), hFS.res, hFS.nlen,
      by rw [hgl, ← hFS.nF, hlv], hfch, hTl, hTr, hfm, by rw [hfl]; omega, hFS.lane,
      hFS.mu40, hFS.ffm, hFS.iz, hFS.slow⟩
    have hi' : i < recs'.length := by rw [hrl, ← hy]; exact hi
    have := hrecs i hi'
    rw [Nat.zero_add, ← hlv] at this
    rw [List.getD_eq_getElem recs' default hi']
    exact this
  rw [hlv] at hFin
  have hrts : ∀ i < c.yrLevel, RtOk σ
      ((osTail c (osLevels c 0 (lv0 :: rest) (osHead c).2).2).2.1.rts.getD i []) (c.levels.getD i default) := by
    intro i hi
    rw [hes, osHead_st]
    simp only [List.nil_append]
    rw [hlv]
    exact hesr i (by rw [hesl, ← hy]; omega)
  obtain ⟨pt, pt1, hrv, hpt, hpt1⟩ := osFinish_sound hFI hrts hmT hFin
  rw [hhead, hmu] at hpt hpt1
  -- the words and the openings
  have hcur : (osHead c).2.cur σ = cur := by
    rw [osHead_st]; simp [OsSt.cur, p8]
  rw [hcur] at hrd
  have hwords : osReadN rd (σ (.n (valf% «open_stacked» "cursor@1"))) (osWordsLen c) = xs := by
    rw [p8, osWordsLen_eq, hlv, ← hxl]
    exact osReadN_of_readsAt hrd
  rw [hwords, hlv]
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
