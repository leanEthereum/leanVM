/-
  LeanVM.Guest.B1.Whir.FactsSound

  From a candidate's checked facts, its callees' meanings and its semantic facts (the vanishing
  tables, the high parts' normalizers, the loop helpers): `LevelsOk` and `FinStaticS`.
-/

module

public import LeanVM.Guest.B1.Whir.Facts
public import LeanVM.Guest.B1.Whir.Open

/-!
# The checked facts, used

* `Callees rd C σ`: the meanings of every deployed callee `open_stacked` calls, under a call
  relation `C`;
* `SemOk c`: the semantic facts of candidate `c`'s levels (`vanishOk`, `hsScale`'s values, the
  loop helpers' bodies);
* `levelsOk_of`: `levelsB` and the two give `LevelsOk`; `finStatic_of`: `CandOk` and them give
  `FinStaticS`.
-/

namespace LeanVM.Guest.B1.Whir

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.Verifier

@[expose] public section

/-- The deployed callees' meanings under `C`. -/
structure Callees (rd : Reader) (C : CallRel) (σ : Val) : Prop where
  round : ∀ a r, WinTabs rd (a.getD 7 0) → C "opening_round" a r → MeaningOpeningRound rd a r
  msg : ∀ p ∈ omDeployed, ∀ a r, C (omName p) a r → MeaningOpeningMessage p.1 p.2 rd a r
  sp : ∀ n ∈ spDeployed, ∀ a r, C (spName n) a r → MeaningSqueezePoint n rd a r
  spf : ∀ n ∈ spfDeployed, ∀ a r, C (spfName n) a r → MeaningSqueezePointFrom n rd a r
  g17 : ∀ w, C ("grind_check__L" ++ natStr queryGrind) [w, σ (.n osTabs)] [] →
    (w.limb 0).lane.toNat % 2 ^ queryGrind = 0
  g14 : ∀ w, C ("grind_check__L" ++ natStr batchGrind) [w, σ (.n osTabs)] [] →
    (w.limb 0).lane.toNat % 2 ^ batchGrind = 0
  dec : ∀ p ∈ queryWindowsShapes, ∀ a r, WinTabs rd (a.getD 3 0) → coreProgram.Rel rd p.1 a r →
    MeaningDecodeQueryWindows p.2.1 p.2.2 rd a r
  cap : ∀ p ∈ merkleCapNames, ∀ a r, C p.1 a r → MeaningVerifyMerkleCap p.2 rd a r
  tail : ∀ a r, C "opening_tail_round" a r → MeaningOpeningTailRound rd a r
  ffm : ∀ p ∈ foldFinalMsgNames, ∀ a r, C p.1 a r → MeaningFoldFinalMsg p.2 rd a r

/-- A candidate's semantic facts. -/
structure SemOk (c : OsCfg) : Prop where
  van : ∀ l < c.levels.length,
    vanishOk (c.levels.getD l default).vanish ((c.levels.getD l default).logCols + 1) = true
  hsm : ∀ l < c.yrLevel, ∀ c' < (c.levels.getD l default).folds,
    K.ofBits (hsScale (c.levels.getD l default).vanish (c.levels.getD l default).highBits c'
      (vanishInv ((c.levels.getD l default).vanish + (c.levels.getD l default).logCols))) =
      ((subspaceRoots (c.levels.getD l default).logCols).getD (c.levels.getD l default).logCols 0)⁻¹ *
        hsNorm (c.levels.getD l default).logCols (c.levels.getD l default).highBits c'
  hsn : ∀ i < c.yrLen + (c.levels.getD c.yrLevel default).folds,
    K.ofBits (hsScale (c.levels.getD c.yrLevel default).vanish (c.yrLog + 1) i 1) =
      hsNorm c.yrLog (c.yrLog + 1) i
  sq : ∀ l < c.levels.length,
    FnIs (c.sqLoop l) (osParams 6) (sqLoopBody (c.levels.getD l default) (c.sqLoop l))
  res : ∀ l < c.yrLevel,
    FnIs (c.resLoop l) (osParams 7) (resLoopBody l (c.levels.getD l default) (c.resLoop l))

theorem drop_cons_getD {l : List OsLv} {k : ℕ} {lv : OsLv} {rest : List OsLv}
    (h : l.drop k = lv :: rest) : l.getD k default = lv ∧ k < l.length ∧ l.drop (k + 1) = rest := by
  have hk : k < l.length := by
    by_contra hc
    rw [List.drop_eq_nil_of_le (by omega)] at h
    simp at h
  refine ⟨?_, hk, ?_⟩
  · rw [List.getD_eq_getElem _ _ hk]
    have := congrArg List.head? h
    rw [List.head?_drop, List.getElem?_eq_getElem hk] at this
    simpa using this
  · rw [← List.drop_drop, h]; rfl

theorem lvFin_of {c : OsCfg} {logN lvl : ℕ} {lv lv' : OsLv} {level next : Whir.Level}
    (h : MidOk c logN lvl lv level next lv') (hv : vanishOk lv.vanish (lv.logCols + 1) = true)
    (hs : ∀ c' < lv.folds, K.ofBits (hsScale lv.vanish lv.highBits c' (vanishInv (lv.vanish + lv.logCols))) =
      ((subspaceRoots lv.logCols).getD lv.logCols 0)⁻¹ * hsNorm lv.logCols lv.highBits c') :
    LvFin c lv lv' := by
  obtain ⟨-, -, -, h1, -, -, -, -, -, -, -, -, h2, -, -, -, -, -, -, -, -, h3, -, -, -, -, -, -, -,
    -, -, -, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14⟩ := h
  exact ⟨h4, h5, h6, h7, h3, h1, h8, h9, h10, h11, h12, h2, h13, h14, vanish_val hv,
    vanish_inv hv, hs⟩

/-- **The levels' facts and callees** from the checked facts. -/
theorem levelsOk_of {rd : Reader} {C : CallRel} {σ : Val} {c : OsCfg} {logN : ℕ}
    (hcal : Callees rd C σ) (hsem : SemOk c) (hle : CallRel.Le C (coreProgram.Rel rd)) :
    ∀ (lvl : ℕ) (lvs : List OsLv) (cfg : List Whir.Level), c.levels.drop lvl = lvs →
      levelsB c logN lvl lvs cfg = true → LevelsOk rd C σ c logN lvl lvs cfg
  | lvl, [lv], [level], hd, hb => by
    simp only [levelsB, decide_eq_true_eq] at hb
    obtain ⟨hlv, hk, -⟩ := drop_cons_getD hd
    obtain ⟨hfin, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18,
      hq, hnhs, hhsb, hvs, h64, hn2, hlc, hom, homn, hdec, hcap⟩ := hb
    have hvan := hsem.van lvl hk
    rw [hlv] at hvan
    refine ⟨⟨hfin, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18,
      ⟨_, _, qshOk_sound hq, hnhs, hhsb, fun i hi ↦ ?_⟩, h64, hn2, fun i hi ↦ ?_⟩, ?_⟩
    · rw [hvs, List.map_map, List.getD_eq_getElem _ _ (by simpa using hi), List.getElem_map,
        List.getElem_range, Function.comp_apply]
      rw [hlc] at hvan
      exact vanish_val hvan i (by omega)
    · have := hsem.hsn i (by rw [← hfin, hlv]; exact hi)
      rwa [← hfin, hlv] at this
    · refine ⟨fun a r ha hc ↦ hcal.round a r ha hc, fun a r hc ↦ ?_, hcal.g17, fun a r ha hc ↦ ?_,
        fun a r hc ↦ hcal.cap _ hcap a r hc, ?_, hcal.tail⟩
      · rw [← homn] at hc; exact hcal.msg _ hom a r hc
      · exact hcal.dec _ hdec a r ha hc
      · have := hsem.sq lvl hk; rwa [hlv] at this
  | lvl, lv :: lv' :: lvs, level :: next :: cfg, hd, hb => by
    simp only [levelsB, Bool.and_eq_true, decide_eq_true_eq] at hb
    obtain ⟨hm, hrest⟩ := hb
    obtain ⟨hlv, hk, hd'⟩ := drop_cons_getD hd
    refine ⟨?_, ?_, levelsOk_of hcal hsem hle (lvl + 1) (lv' :: lvs) (next :: cfg) hd' hrest⟩
    · obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19,
        h20, h21, h22, hq, h23, -⟩ := hm
      exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19,
        h20, h21, h22, ⟨_, _, qshOk_sound hq⟩, h23⟩
    · obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hom, homn, hsp,
        hspn, hspf, hspfn, hdec, hcap, -⟩ := hm
      refine ⟨fun a r ha hc ↦ hcal.round a r ha hc, fun a r hc ↦ ?_, fun a r hc ↦ ?_, fun a r hc ↦ ?_,
        hcal.g17, hcal.g14, fun a r ha hc ↦ hcal.dec _ hdec a r ha hc,
        fun a r hc ↦ hcal.cap _ hcap a r hc, ?_⟩
      · rw [← homn] at hc; exact hcal.msg _ hom a r hc
      · rw [← hspfn] at hc; exact hcal.spf _ hspf a r hc
      · rw [← hspn] at hc; exact hcal.sp _ hsp a r hc
      · have := hsem.sq lvl hk; rwa [hlv] at this
  | _, [], _, _, hb => by simp [levelsB] at hb
  | _, [_], [], _, hb => by simp [levelsB] at hb
  | _, [_], _ :: _ :: _, _, hb => by simp [levelsB] at hb
  | _, _ :: _ :: _, [], _, hb => by simp [levelsB] at hb
  | _, _ :: _ :: _, [_], _, hb => by simp [levelsB] at hb

/-- `levelsB` gives every non-final level's `MidOk`. -/
theorem midOk_of {c : OsCfg} {logN : ℕ} :
    ∀ (lvl : ℕ) (lvs : List OsLv) (cfg : List Whir.Level), levelsB c logN lvl lvs cfg = true →
      ∀ i, i + 1 < lvs.length → ∃ level next, MidOk c logN (lvl + i) (lvs.getD i default) level next
        (lvs.getD (i + 1) default)
  | lvl, [lv], [level], _, i, hi => by simp at hi
  | lvl, lv :: lv' :: lvs, level :: next :: cfg, hb, i, hi => by
    simp only [levelsB, Bool.and_eq_true, decide_eq_true_eq] at hb
    rcases i with _ | i
    · exact ⟨level, next, by simpa using hb.1⟩
    · obtain ⟨l, n, h⟩ := midOk_of (lvl + 1) (lv' :: lvs) (next :: cfg) hb.2 i (by simp at hi ⊢; omega)
      refine ⟨l, n, ?_⟩
      rw [show lvl + (i + 1) = lvl + 1 + i by ring]
      simpa using h
  | _, [], _, hb, _, _ => by simp [levelsB] at hb
  | _, [_], [], hb, _, _ => by simp [levelsB] at hb
  | _, [_], _ :: _ :: _, hb, _, _ => by simp [levelsB] at hb
  | _, _ :: _ :: _, [], hb, _, _ => by simp [levelsB] at hb
  | _, _ :: _ :: _, [_], hb, _, _ => by simp [levelsB] at hb

/-- **The finish's static facts** from the checked facts. -/
theorem finStatic_of {rd : Reader} {C : CallRel} {σ : Val} {m μ r : ℕ} {cfg : List Whir.Level}
    (hcal : Callees rd C σ) (hsem : SemOk (osCfg m)) (h : CandOk m μ r cfg) :
    FinStaticS rd C (osCfg m) := by
  obtain ⟨-, -, -, -, hn2, hyr, hyl, hyn, hnF, hla, h40, hffm, hlv⟩ := h
  refine ⟨hn2, hyr, hyl, hyn, fun i hi ↦ ?_, hsem.res, hnF, hla, h40,
    fun a r hc ↦ hcal.ffm _ hffm a r hc⟩
  obtain ⟨level, next, hm⟩ := midOk_of 0 _ cfg hlv i (by omega)
  rw [Nat.zero_add] at hm
  exact lvFin_of hm (hsem.van i (by omega)) (hsem.hsm i hi)

end
end LeanVM.Guest.B1.Whir
