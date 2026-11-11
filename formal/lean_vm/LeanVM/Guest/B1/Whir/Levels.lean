/-
  LeanVM.Guest.B1.Whir.Levels

  The template's levels run the Spec's levels up to the tail.
-/

module

public import LeanVM.Protocol.Verifier.WhirTarget
public import LeanVM.Guest.B1.Whir.Level
public import LeanVM.Guest.B1.Whir.LevelSpec

/-!
# The levels (G:1488-1646)

`whirLevelsHead`: `whirLevelsOpen` without its tail (`whirLevelsOpen_eq`). `osLevels_sound`: the
template's levels, the configuration's facts holding level by level (`LevelsOk`) and the callees
by their meanings (`CalleesOk`), run `whirLevelsHead`; they leave the final message, every
level's record (`RecStored`), the fold challenges in `fold_challenges` and the guest's state for
the tail.
-/

namespace LeanVM.Guest.B1.Whir

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest LeanVM.Guest.B1
open LeanVM.Guest.Value LeanVM.Protocol LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

variable {rd : Reader} {σ : Val}

/-- `whirLevelsOpen` up to the tail: the levels' heads. -/
def whirLevelsHead (logN : ℕ) : ℕ → List Whir.Level → WhirStateT → VerifierProgram (List E × ℕ ×
    WhirStateT)
  | _, [], _ => VerifierProgram.fail
  | index, [level], s => levelHead logN index level [] s
  | index, level :: next :: rest, s =>
    (levelHead logN index level (next :: rest) s).bind fun r ↦
      whirLevelsHead logN (index + 1) (next :: rest) r.2.2

/-- **The levels, then the tail.** -/
theorem whirLevelsOpen_eq (logN laneFolds : ℕ) : ∀ (index : ℕ) (cfg : List Whir.Level)
    (s : WhirStateT), cfg ≠ [] →
    whirLevelsOpen logN laneFolds index cfg s =
      (whirLevelsHead logN index cfg s).bind fun r ↦ levelTail laneFolds r.2.1 r.1 r.2.2
  | _, [], _, h => absurd rfl h
  | index, [level], s, _ => by rw [whirLevelsOpen_head]; rfl
  | index, level :: next :: rest, s, _ => by
    rw [whirLevelsOpen_head, whirLevelsHead, VerifierProgram.bind_assoc]
    refine prog_bind_congr fun r ↦ ?_
    exact whirLevelsOpen_eq logN laneFolds (index + 1) (next :: rest) r.2.2 (by simp)

/-- The configuration's facts, level by level. -/
def LevelsOk (c : OsCfg) (logN : ℕ) : ℕ → List OsLv → List Whir.Level → Prop
  | lvl, [lv], [level] => LvB c lvl lv level lv.logCols ∧ level.fold = lv.folds ∧
      level.foldGrinding = lv.foldGrind ∧
      1 ≤ lv.folds ∧ logN - (lv.foldsOff + lv.folds) = lv.logCols ∧
      2 ^ lv.logCols = c.yrLen ∧ lvl = c.yrLevel
  | lvl, lv :: lv' :: lvs, level :: next :: cfg => LvB c lvl lv level lv.logCols ∧
      level.fold = lv.folds ∧ level.foldGrinding = lv.foldGrind ∧ 1 ≤ lv.folds ∧
      logN - (lv.foldsOff + lv.folds) = lv.logCols ∧
      1 ≤ lv.logCols ∧ (lvl + 1) * ligColsCap < u128Bound ∧ lvl ≠ c.yrLevel ∧
      lv'.foldsOff = lv.foldsOff + lv.folds ∧
      levelShape lv.logCols next (3 * 2 ^ next.fold) = (lv'.depth, lvWidth (lvl + 1) lv') ∧
      LevelsOk c logN (lvl + 1) (lv' :: lvs) (next :: cfg)
  | _, _, _ => False

/-- The callees, level by level. -/
def CalleesOk (rd : Reader) (c : OsCfg) : ℕ → List OsLv → Prop
  | _, [] => True
  | lvl, lv :: lvs => LvCallees rd c lvl lv ∧ CalleesOk rd c (lvl + 1) lvs

/-- The rate's selector names each level's row. -/
def RatesOk (σ : Val) (c : OsCfg) : ℕ → List OsLv → Prop
  | _, [] => True
  | lvl, lv :: lvs => LvRate σ c lvl lv ∧ RatesOk σ c (lvl + 1) lvs

theorem calleesOk_at {rd : Reader} {c : OsCfg} : ∀ {lvs : List OsLv} {lvl : ℕ},
    CalleesOk rd c lvl lvs → ∀ i (hi : i < lvs.length), LvCallees rd c (lvl + i) lvs[i]
  | [], _, _, i, hi => absurd hi (by simp)
  | _ :: _, _, h, 0, _ => by simpa using h.1
  | _ :: rest, lvl, h, i + 1, hi => by
    have := calleesOk_at h.2 i (by simpa using hi)
    rwa [show lvl + 1 + i = lvl + (i + 1) by ring] at this

theorem ratesOk_at {σ : Val} {c : OsCfg} : ∀ {lvs : List OsLv} {lvl : ℕ},
    RatesOk σ c lvl lvs → ∀ i (hi : i < lvs.length), LvRate σ c (lvl + i) lvs[i]
  | [], _, _, i, hi => absurd hi (by simp)
  | _ :: _, _, h, 0, _ => by simpa using h.1
  | _ :: rest, lvl, h, i + 1, hi => by
    have := ratesOk_at h.2 i (by simpa using hi)
    rwa [show lvl + 1 + i = lvl + (i + 1) by ring] at this

/-- The levels' `opening_queries` calls of `C`, sound with their queries `Wf lvl lv`. -/
def QWOk (rd : Reader) (C : CallRel) (Wf : ℕ → OsLv → List E → List E → List QW) :
    ℕ → List OsLv → Prop
  | _, [] => True
  | lvl, lv :: lvs => LvQW rd C lvl lv (Wf lvl lv) ∧ QWOk rd C Wf (lvl + 1) lvs

/-- **The levels** run `whirLevelsHead`, on the openings their queries' witnesses name. -/
theorem osLevels_sound {c : OsCfg} {logN : ℕ} {C : CallRel} (hle : CallRel.Le C (coreProgram.Rel rd))
    {V : FrameMap} (hU : UnfoldsV rd C V)
    {Wf : ℕ → OsLv → List E → List E → List QW} : ∀ (lvs : List OsLv) (cfg : List Whir.Level)
    (lvl : ℕ) (st : OsSt) (ws : WhirStateT) (R : List (Digest × ℕ × ℕ)) (root : Digest),
    LevelsOk c logN lvl lvs cfg → CalleesOk rd c lvl lvs → QWOk rd C Wf lvl lvs →
    RatesOk σ c lvl lvs →
    LvIn rd σ lvl (lvs.headD default) st ws R root → WinTabs rd (σ (.n osWin)) →
    AllOk C rd σ (osLevels c lvl lvs st).1 →
    ∃ (xs : List E) (os : List (List Opening)) (R' : List (Digest × ℕ × ℕ)) (ms : List E)
      (ws' : WhirStateT) (rs : List OsRec),
      ReadsAt rd (st.cur σ) xs ∧
      RunsWith (whirLevelsHead logN lvl cfg ws) (st.F σ) xs os R
        (ms, (lvs.getLastD default).logCols, ws') ((osLevels c lvl lvs st).2.F σ) R' ∧
      ms.length = c.yrLen ∧ ReadsAt rd (σ (.n osFmsg)) ms ∧
      ws'.glued = ws.glued ++ rs.flatMap recClaims ∧ rs.length = lvs.length ∧
      (∀ i (hi : i < rs.length) (hi' : i < lvs.length), RecStored rd σ c (lvl + i) lvs[i] rs[i]) ∧
      ws'.folds.length = (lvs.getLastD default).foldsOff + (lvs.getLastD default).folds ∧
      (∀ j (h : j < ws'.folds.length), LoadHolds rd (σ (.n osFch)) j ws'.folds[j]) ∧
      ws'.quad = (osLevels c lvl lvs st).2.quad σ ∧
      ws'.target = σ (.n (osLevels c lvl lvs st).2.t) ∧
      (osLevels c lvl lvs st).2.fs.length = 5 ∧ PadOk σ (osLevels c lvl lvs st).2.pad ∧
      (osLevels c lvl lvs st).2.co ≤ 8 ∧
      (osLevels c lvl lvs st).2.cur σ = st.cur σ * gen ^ xs.length ∧
      os = (osQCalls c lvl lvs st).map (fun e ↦ lvOs rd σ V (Wf e.1 e.2.1) e.1 e.2.1 e.2.2) ∧
      xs.length = lvsWords c lvl lvs ∧ MatsOk σ (osLevels c lvl lvs st).2.mats
  | [lv], [level], lvl, st, ws, R, root, hok, hcal, hqw, hrat, hin, hwt, hall => by
    obtain ⟨hcfg, hfold, hfg, h4, hml, hlen, hfin⟩ := hok
    have hall' : AllOk C rd σ (osLevel c lvl lv st).1 := by
      have := (allOk_append.mp hall).1
      exact this
    obtain ⟨xs, os, ws', ms, r, hrd, hrun, hmsl, hfm, hgl, hrec, hfl, hfch, hq, ht, hfs, hpad,
      hco, hcur, hos, hxl, hmt⟩ := osLevel_final_sound hle hU hqw.1 hcal.1 hrat.1 hcfg hfold hfg h4 hml hlen
        hfin hin hwt hall'
    exact ⟨xs, [os], R, ms, ws', [r], hrd, hrun, hmsl, hfm, by simpa using hgl, rfl,
      fun i hi _ ↦ by
        obtain rfl : i = 0 := by simpa using hi
        simpa using hrec, hfl, hfch, hq, ht, hfs, hpad, hco, hcur,
      by rw [hos]; simp [osQCalls], by rw [hxl]; simp [lvsWords, hfin], hmt⟩
  | lv :: lv' :: lvs, level :: next :: cfg, lvl, st, ws, R, root, hok, hcal, hqw, hrat, hin, hwt,
      hall => by
    obtain ⟨hcfg, hfold, hfg, h4, hml, hm, hlvl, hnf, hoff', hshape, hrest⟩ := hok
    have e1 : osLevels c lvl (lv :: lv' :: lvs) st =
        ((osLevel c lvl lv st).1 ++ (osLevels c (lvl + 1) (lv' :: lvs) (osLevel c lvl lv st).2).1,
          (osLevels c (lvl + 1) (lv' :: lvs) (osLevel c lvl lv st).2).2) := rfl
    rw [e1] at hall ⊢
    rw [allOk_append] at hall
    obtain ⟨xs1, os1, ws1, root', r, hrd1, hrun1, hin1, hgl1, hrec1, hcur1, hos1, hxl1⟩ :=
      osLevel_nonfinal_sound (rest := cfg) hle hU hqw.1 hcal.1 hrat.1 hcfg hfold hfg h4 hml hm hlvl
        hnf hoff' hshape hin hwt hall.1
    obtain ⟨xs2, os2, R', ms, ws', rs, hrd2, hrun2, hmsl, hfm, hgl2, hrl, hrec2, hfl, hfch, hq,
      ht, hfs, hpad, hco, hcur2, hos2, hxl2, hmt⟩ :=
      osLevels_sound hle hU (lv' :: lvs) (next :: cfg) (lvl + 1) _ ws1 _ root' hrest hcal.2 hqw.2
        hrat.2 hin1 hwt hall.2
    refine ⟨xs1 ++ xs2, [os1] ++ os2, R', ms, ws', r :: rs, readsAt_append hrd1 (by
        rw [← hcur1]; exact hrd2), ?_, hmsl, hfm, ?_, by simp [hrl], ?_, hfl, hfch, hq, ht, hfs,
      hpad, hco, ?_, ?_, ?_, hmt⟩
    · exact RunsWith.bind' hrun1 hrun2
    · rw [hgl2, hgl1]; simp
    · intro i hi hi'
      rcases i with _ | i
      · simpa using hrec1
      · have := hrec2 i (by simpa using hi) (by simpa using hi')
        rw [show lvl + 1 + i = lvl + (i + 1) by ring] at this
        simpa using this
    · rw [hcur2, hcur1, List.length_append, pow_add, mul_assoc]
    · rw [hos1, hos2]; simp [osQCalls]
    · rw [List.length_append, hxl1, hxl2]; simp [lvsWords, hnf]
  | [], _, _, _, _, _, _, hok, _, _, _, _, _, _ => by simp [LevelsOk] at hok
  | [_], [], _, _, _, _, _, hok, _, _, _, _, _, _ => by simp [LevelsOk] at hok
  | [_], _ :: _ :: _, _, _, _, _, _, hok, _, _, _, _, _, _ => by simp [LevelsOk] at hok
  | _ :: _ :: _, [], _, _, _, _, _, hok, _, _, _, _, _, _ => by simp [LevelsOk] at hok
  | _ :: _ :: _, [_], _, _, _, _, _, hok, _, _, _, _, _, _ => by simp [LevelsOk] at hok

end
end LeanVM.Guest.B1.Whir
