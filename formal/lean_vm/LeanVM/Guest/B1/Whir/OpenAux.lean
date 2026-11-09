/-
  LeanVM.Guest.B1.Whir.OpenAux

  Glue for the assembly of `open_stacked`: the zero run after the levels, the rotated point's
  sources, the out-of-domain weights' inputs level by level, the lane folds.
-/

module

public import LeanVM.Guest.B1.Whir.Levels
public import LeanVM.Guest.B1.Whir.Finish

/-!
# Assembly glue

* `osLevels_pad`: after a level the sponge's zero run is allocated;
* `ptSrc_ok`: the rotated point `(F ++ T).drop lane ++ (F ++ T).take lane` is what `osPtSrc`
  names, the fold challenges `F` in `fold_challenges`, the tail's `T` in `tail_challenges`;
* `oodAll_of`: `OodAll` from its levels' inputs;
* `levelsOk_lane`: the lane folds are the first level's.
-/

namespace LeanVM.Guest.B1.Whir

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest LeanVM.Guest.B1
open LeanVM.Guest.Value LeanVM.Protocol LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

variable {rd : Reader} {σ : Val}

theorem osLevelB_pad (c : OsCfg) (lvl : ℕ) (lv : OsLv) (s : OsSt) :
    ∃ p, (osLevelB c lvl lv s).2.pad = some p := by
  refine ⟨(osPad s.pad (s.k + 14)).2.1, ?_⟩
  by_cases h : lvl = c.yrLevel
  · simp only [osLevelB, h, ↓reduceIte]; rfl
  · simp only [osLevelB, h, ↓reduceIte]; rfl

theorem osLevel_pad (c : OsCfg) (lvl : ℕ) (lv : OsLv) (s : OsSt) :
    ∃ p, (osLevel c lvl lv s).2.pad = some p := by
  have e : (osLevel c lvl lv s).2 = (osLevelB c lvl lv (osLevelA c lvl lv s).2.1).2 := by
    rw [osLevel_split]
  rw [e]
  exact osLevelB_pad c lvl lv (osLevelA c lvl lv s).2.1

theorem osLevels_pad (c : OsCfg) : ∀ (lvs : List OsLv) (lvl : ℕ) (s : OsSt), lvs ≠ [] →
    ∃ p, (osLevels c lvl lvs s).2.pad = some p
  | [], _, _, h => absurd rfl h
  | [lv], lvl, s, _ => by
    have e : osLevels c lvl [lv] s = ((osLevel c lvl lv s).1 ++ [], (osLevel c lvl lv s).2) := rfl
    rw [e]
    exact osLevel_pad c lvl lv s
  | lv :: lv' :: rest, lvl, s, _ => by
    have e : osLevels c lvl (lv :: lv' :: rest) s =
        ((osLevel c lvl lv s).1 ++ (osLevels c (lvl + 1) (lv' :: rest) (osLevel c lvl lv s).2).1,
          (osLevels c (lvl + 1) (lv' :: rest) (osLevel c lvl lv s).2).2) := rfl
    obtain ⟨p, hp⟩ := osLevels_pad c (lv' :: rest) (lvl + 1) (osLevel c lvl lv s).2
      (List.cons_ne_nil _ _)
    refine ⟨p, ?_⟩
    rw [e]
    exact hp

/-- **The rotated point's sources.** -/
theorem ptSrc_ok {c : OsCfg} {tch : ℕ} {F T : List E} (hF : F.length = c.nFolds)
    (hT : T.length = c.yrLog) (hlane : (c.levels.headD default).folds ≤ c.nFolds)
    (hFr : ∀ j (h : j < F.length), LoadHolds rd (σ (.n osFch)) j F[j])
    (hTr : ∀ j (h : j < T.length), LoadHolds rd (σ (.n tch)) j T[j]) (i : ℕ) :
    PtSrcOk rd σ (osPtSrc c tch i)
      (((F ++ T).drop (c.levels.headD default).folds ++
        (F ++ T).take (c.levels.headD default).folds).getD i 0) := by
  set lane := (c.levels.headD default).folds with hl
  have hlen : ((F ++ T).drop lane).length = c.nFolds + c.yrLog - lane := by simp [hF, hT]
  unfold osPtSrc
  rw [← hl]
  by_cases h1 : i < c.nFolds - lane
  · simp only [h1, ↓reduceIte, PtSrcOk]
    rw [List.getD_eq_getElem _ _ (by simp [hF, hT]; omega), List.getElem_append_left
      (by rw [hlen]; omega), List.getElem_drop, List.getElem_append_left (by rw [hF]; omega)]
    exact hFr _ _
  · by_cases h2 : i < c.nFolds - lane + c.yrLog
    · simp only [h1, h2, ↓reduceIte, PtSrcOk]
      rw [List.getD_eq_getElem _ _ (by simp [hF, hT]; omega), List.getElem_append_left
        (by rw [hlen]; omega), List.getElem_drop, List.getElem_append_right (by rw [hF]; omega)]
      simp only [show lane + i - F.length = i - (c.nFolds - lane) by rw [hF]; omega]
      exact hTr _ _
    · by_cases h3 : i < c.nFolds + c.yrLog
      · simp only [h1, h2, h3, ↓reduceIte, PtSrcOk]
        rw [List.getD_eq_getElem _ _ (by simp [hF, hT]; omega), List.getElem_append_right
          (by rw [hlen]; omega), List.getElem_take, List.getElem_append_left (by
            rw [hlen, hF]; omega)]
        simp only [hlen, show i - (c.nFolds + c.yrLog - lane) = i - (c.nFolds - lane) - c.yrLog by
          omega]
        exact hFr _ _
      · simp only [h1, h2, h3, ↓reduceIte, PtSrcOk]
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simp [hF, hT]; omega)]
        rfl

/-- **`OodAll`** from every level's inputs. -/
theorem oodAll_of {c : OsCfg} {tch : ℕ} {Λ : ℕ → E} {Z Y : ℕ → ℕ → E} :
    ∀ (L : List OsLv) (prev ol : ℕ),
      (∀ i < L.length, OodIn rd σ c tch (if i = 0 then prev else (L.getD (i - 1) default).logCols)
        (ol + i) (L.getD i default) (Λ (ol + i)) (Z (ol + i)) (Y (ol + i))) →
      OodAll rd σ c tch Λ Z Y prev ol L
  | [], _, _, _ => trivial
  | lv :: rest, prev, ol, h => by
    refine ⟨by simpa using h 0 (by simp), oodAll_of rest lv.logCols (ol + 1) fun i hi ↦ ?_⟩
    have := h (i + 1) (by simp; omega)
    simp only [Nat.add_one_ne_zero, ↓reduceIte, Nat.add_sub_cancel, List.getD_cons_succ,
      show ol + (i + 1) = ol + 1 + i by ring] at this
    rcases i with _ | i
    · simpa using this
    · simpa using this

/-- The lane folds are the first level's. -/
theorem levelsOk_lane {c : OsCfg} {logN : ℕ} : ∀ {lvl : ℕ} {lvs : List OsLv} {cfg : List Whir.Level},
    LevelsOk c logN lvl lvs cfg →
      (cfg.head?.map (·.fold)).getD 0 = (lvs.headD default).folds ∧ cfg ≠ []
  | _, [_], [_], h => ⟨by simpa using h.2.1, by simp⟩
  | _, _ :: _ :: _, _ :: _ :: _, h => ⟨by simpa using h.2.1, by simp⟩
  | _, [], _, h => by simp [LevelsOk] at h
  | _, [_], [], h => by simp [LevelsOk] at h
  | _, [_], _ :: _ :: _, h => by simp [LevelsOk] at h
  | _, _ :: _ :: _, [], h => by simp [LevelsOk] at h
  | _, _ :: _ :: _, [_], h => by simp [LevelsOk] at h

end
end LeanVM.Guest.B1.Whir
