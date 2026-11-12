/-
  LeanVM.Guest.B1.Whir.Levels

  The levels of `open_stacked` and its closing rounds run the Spec's `whirLevelsOpen`.
-/

module

public import LeanVM.Guest.B1.Whir.LevelLast

/-!
# The levels (G:1560-1730)

`LevelsOk`: every non-final level's facts and callees (`MidFacts`, `MidCalls`), then the final
level's (`FinFacts`, `FinCalls`). `osLevels_sound`: from a level's `LvIn`, the template's levels
from it and the closing rounds run `whirLevelsOpen`, reading `lvsWords` words at the cursor and
the openings `osLevelsW` (one phase a level, the witness's); the returned terminal is the
guest's tail claim plus the deficit of every level's record times the closing challenges, and
the records' values are in memory (`RecStored`) for the finish.
-/

namespace LeanVM.Guest.B1.Whir

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest LeanVM.Guest.B1
open LeanVM.Guest.Value LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile
open LeanVM.Protocol.Verifier

@[expose] public section

variable {C : CallRel} {rd : Reader} {σ : Val}

/-- Every level's facts and callees, from level `lvl`. -/
def LevelsOk (rd : Reader) (C : CallRel) (σ : Val) (c : OsCfg) (logN : ℕ) :
    ℕ → List OsLv → List Whir.Level → Prop
  | lvl, [lv], [level] => FinFacts c logN lvl lv level ∧ FinCalls rd C σ c lvl lv
  | lvl, lv :: lv' :: lvs, level :: next :: cfg => MidFacts c logN lvl lv level next lv' ∧
      MidCalls rd C σ c lvl lv ∧ LevelsOk rd C σ c logN (lvl + 1) (lv' :: lvs) (next :: cfg)
  | _, _, _ => False

/-- The stream words of the levels from `lvl`. -/
def lvsWords (c : OsCfg) : ℕ → List OsLv → ℕ
  | _, [] => 0
  | lvl, lv :: rest => lvWords c lvl lv + lvsWords c (lvl + 1) rest

/-- The levels' folds. -/
def lvsFolds : List OsLv → ℕ
  | [] => 0
  | lv :: rest => lv.folds + lvsFolds rest

/-- The last level's row. -/
def lvsLast (lvs : List OsLv) : OsLv := lvs.getLastD default

theorem osLevels_cons (c : OsCfg) (lvl : ℕ) (lv : OsLv) (rest : List OsLv) (s : OsSt) :
    (osLevels c lvl (lv :: rest) s).1 =
      (osLevel c lvl lv s).1 ++ (osLevels c (lvl + 1) rest (osLevel c lvl lv s).2).1 := rfl

theorem osLevels_cons_snd (c : OsCfg) (lvl : ℕ) (lv : OsLv) (rest : List OsLv) (s : OsSt) :
    (osLevels c lvl (lv :: rest) s).2 = (osLevels c (lvl + 1) rest (osLevel c lvl lv s).2).2 := rfl

/-- **The levels from `lvl` and the closing rounds, soundly.** -/
theorem osLevels_sound {V : FrameMap} (hU : UnfoldsV rd C V)
    (hle : CallRel.Le C (coreProgram.Rel rd)) (hwt : WinTabs rd (σ (.n osTabs)))
    {c : OsCfg} {logN : ℕ} (lane : ℕ) :
    ∀ (lvl : ℕ) (lv : OsLv) (lvs : List OsLv) (cfg : List Whir.Level) (st : OsSt) (ws : WhirState)
      (recs : List OsRec) (R : List (Digest × ℕ × ℕ)) (root : Digest),
      LevelsOk rd C σ c logN lvl (lv :: lvs) cfg → LvIn rd σ lvl lv st ws recs R root →
      AllOk C rd σ (osLevels c lvl (lv :: lvs) st).1 →
      AllOk C rd σ (osTail c (osLevels c lvl (lv :: lvs) st).2).1 →
      ∃ (xs : List E) (recs' : List OsRec) (gs fold T : List E) (R' : List (Digest × ℕ × ℕ)),
        xs.length = lvsWords c lvl (lv :: lvs) + 2 * c.yrLog ∧ ReadsAt rd (st.cur σ) xs ∧
        RunsWith (whirLevelsOpen logN lane lvl cfg ws) (st.F σ) xs
          (osLevelsW rd V σ c lvl (lv :: lvs) st) R
          ⟨((ws.alphas ++ gs) ++ T).drop lane ++ ((ws.alphas ++ gs) ++ T).take lane,
            ((recs ++ recs').flatMap recGlued).foldl
              (fun w g ↦ w + g.scalar * g.weightAt (((ws.alphas ++ gs) ++ T).drop g.foldStart)) 0,
            multilinearEval (fold.take c.yrLen) T,
            σ (.n (osTail c (osLevels c lvl (lv :: lvs) st).2).2.1.claim) +
              T.prod * recsDeficit (recs ++ recs') (ws.alphas ++ gs)⟩
          ((osTail c (osLevels c lvl (lv :: lvs) st).2).2.1.F σ) R' ∧
        recs'.length = lvs.length ∧
        (∀ i (hi : i < recs'.length), RecStored rd σ (lvl + i) ((lv :: lvs).getD i default) recs'[i]) ∧
        (∀ r ∈ recs, r.F ≤ ws.alphas.length) ∧
        gs.length = lvsFolds (lv :: lvs) ∧
        (∀ j (h : j < (ws.alphas ++ gs).length), LoadHolds rd (σ (.n osFch)) j (ws.alphas ++ gs)[j]) ∧
        ReadsAt rd (σ (.n osFmsg)) fold ∧ fold.length = c.yrLen + (lvsLast (lv :: lvs)).folds ∧
        ReadsAt rd (σ (.n (osTail c (osLevels c lvl (lv :: lvs) st).2).2.2)) T ∧
        T.length = c.yrLog ∧ MatsOk σ (osTail c (osLevels c lvl (lv :: lvs) st).2).2.1.mats
  | lvl, lv, [], [level], st, ws, recs, R, root, hok, hin, hA, hT => by
    obtain ⟨hF, hcal⟩ := hok
    simp only [osLevels, List.append_nil] at hA hT
    obtain ⟨xs, gs, fold, T, hxl, hrd, hgl, hfl, hTl, hrun, hfm, hTr, lg, hmT⟩ :=
      osLevelLast_sound hU hle hwt hF hcal hin hA hT lane
    refine ⟨xs, [], gs, fold, T, R, by simp [hxl, lvsWords], hrd, ?_, rfl,
      fun i hi ↦ absurd hi (by simp), hin.recF, by simp [hgl, lvsFolds], ?_, hfm, hfl, hTr, hTl,
      by simpa [osLevels] using hmT⟩
    · rw [whirLevelsOpen_last]
      simp only [osLevelsW, List.append_nil, osLevels]
      refine RunsWith.of_eq hrun rfl rfl rfl rfl ?_ rfl rfl
      rw [hin.glued, recsDeficit_append_alphas _ _ _ hin.recF]
    · intro j hj
      by_cases h0 : j < ws.alphas.length
      · rw [List.getElem_append_left h0]; exact hin.fch j h0
      · rw [List.getElem_append_right (by omega)]
        have := lg (j - ws.alphas.length) (by simp at hj; omega)
        rw [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem (by simp at hj; omega),
          Option.getD_some, ← hin.glen, Nat.add_sub_cancel' (by omega)] at this
        exact this
  | lvl, lv, lv' :: lvs, level :: next :: cfg, st, ws, recs, R, root, hok, hin, hA, hT => by
    obtain ⟨hF, hcal, hrest⟩ := hok
    rw [osLevels_cons] at hA
    rw [osLevels_cons_snd] at hT ⊢
    rw [allOk_append] at hA
    obtain ⟨xs1, ws1, r, root', hxl1, hrd1, hrun1, hin1, hrec, hcur1, gs1, hgs1, hgl1⟩ :=
      osLevelMid_sound hU hle hwt hF hcal hin hA.1
    obtain ⟨xs2, recs', gs2, fold, T, R', hxl2, hrd2, hrun2, hrl, hrecs, -, hgl2, hfch, hfm,
      hfl, hTr, hTl, hmT⟩ :=
      osLevels_sound hU hle hwt lane (lvl + 1) lv' lvs (next :: cfg) (osLevel c lvl lv st).2 ws1
        (recs ++ [r]) _ root' hrest hin1 hA.2 hT
    have eG : ws1.alphas ++ gs2 = ws.alphas ++ (gs1 ++ gs2) := by rw [hgs1, List.append_assoc]
    rw [eG] at hrun2 hfch
    rw [List.append_assoc] at hrun2
    refine ⟨xs1 ++ xs2, r :: recs', gs1 ++ gs2, fold, T, R', ?_, ?_, ?_, by simp [hrl], ?_,
      hin.recF, by simp [hgl1, hgl2, lvsFolds], hfch, hfm, ?_, hTr, hTl, hmT⟩
    · simp only [List.length_append, hxl1, hxl2, lvsWords]; ring
    · exact readsAt_append hrd1 (by rw [← hcur1]; exact hrd2)
    · rw [whirLevelsOpen_next]
      have h := RunsWith.bind' hrun1 hrun2
      simp only [VerifierProgram.bind_assoc] at h
      exact RunsWith.of_eq h rfl rfl rfl rfl (by simp) rfl rfl
    · intro i hi
      rcases i with _ | i
      · simpa using hrec
      · have := hrecs i (by simp at hi; omega)
        rw [show lvl + 1 + i = lvl + (i + 1) by ring] at this
        simpa using this
    · rw [hfl]; rfl
  | _, _, [], [], _, _, _, _, _, hok, _, _, _ => absurd hok (by simp [LevelsOk])
  | _, _, [], _ :: _ :: _, _, _, _, _, _, hok, _, _, _ => absurd hok (by simp [LevelsOk])
  | _, _, _ :: _, [], _, _, _, _, _, hok, _, _, _ => absurd hok (by simp [LevelsOk])
  | _, _, _ :: _, [_], _, _, _, _, _, hok, _, _, _ => absurd hok (by simp [LevelsOk])

end
end LeanVM.Guest.B1.Whir
