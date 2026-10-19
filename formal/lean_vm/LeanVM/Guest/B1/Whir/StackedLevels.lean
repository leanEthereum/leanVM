/-
  LeanVM.Guest.B1.Whir.StackedLevels

  All the levels of `open_stacked` against `whirLevelsOpen`, up to the tail.
-/

module

public import LeanVM.Guest.B1.Whir.StackedLevel

/-!
# The levels of the stacked opening (TRIAGE #36)

`osLevels_sound`: by induction over the levels, `osLevel_sound` at each; the guest's levels read
words and openings over which `whirLevelsOpen` runs to its tail (`osTailOpen`), from the state the
guest leaves after its last level (`OsEndInv`), whatever the tail then reads.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.VerifySub

@[expose] public section

variable {rd : Reader} {σ : Val}

instance instInhabitedWhirLevelOs : Inhabited Whir.Level := ⟨⟨0, 0, 0⟩⟩

theorem osOods_noRet (lvl logCols oodz ood : ℕ) : ∀ (os n : ℕ) (st : OsSt),
    Stmt.noRetList (osOods lvl logCols oodz ood os n st).1 = true
  | _, 0, _ => rfl
  | os, n + 1, st => by
    simp only [osOods, noRetList_append, osOods_noRet lvl logCols oodz ood (os + 1) n, Bool.and_true]
    simp [osOodSample, osFsNext, fsNextT, fsCompressT, Stmt.noRetList, Stmt.noRet]

theorem osOodGlues_noRet' (lvl lam : ℕ) : ∀ (os n sc : ℕ) (st : OsSt),
    Stmt.noRetList (osOodGlues lvl lam os n sc st).1 = true
  | _, 0, _, _ => rfl
  | os, n + 1, sc, st => by
    simp only [osOodGlues, noRetList_append, osOodGlues_noRet' lvl lam (os + 1) n, Bool.and_true]
    simp [osOodGlue, Stmt.noRetList, Stmt.noRet]

theorem osLevels_cons (cfg : OsCfg) (lvl : ℕ) (lv : OsLvl) (rest : List OsLvl) (st : OsSt) :
    osLevels cfg lvl (lv :: rest) st =
      ((osLevel cfg lvl lv st).1 ++ (osLevels cfg (lvl + 1) rest (osLevel cfg lvl lv st).2).1,
        (osLevels cfg (lvl + 1) rest (osLevel cfg lvl lv st).2).2) := rfl

theorem osLevel_noRet (cfg : OsCfg) (lvl : ℕ) (lv : OsLvl) (st : OsSt) :
    Stmt.noRetList (osLevel cfg lvl lv st).1 = true := by
  unfold osLevel
  simp only [noRetList_append, osFolds_noRet, osGrind_noRet, osSqueezes_noRet, osLamPows_noRet,
    osQueries_noRet, Bool.true_and, Bool.and_true]
  split
  · simp [osFinal_noRet, osGlue, Stmt.noRetList, Stmt.noRet]
  · simp only [osCommit, noRetList_append, osOods_noRet, osOodGlues_noRet', Bool.and_true]
    simp [osFsNext, fsNextT, fsCompressT, osGlue, Stmt.noRetList, Stmt.noRet]

theorem osLevels_noRet (cfg : OsCfg) : ∀ (lvl : ℕ) (lvs : List OsLvl) (st : OsSt),
    Stmt.noRetList (osLevels cfg lvl lvs st).1 = true
  | _, [], _ => rfl
  | lvl, lv :: rest, st => by
    rw [osLevels_cons, noRetList_append, osLevels_noRet cfg (lvl + 1) rest, osLevel_noRet]; rfl

/-- **The levels** (G:1096-1213 at every level): from level `lvl` with `j` levels after it, the
guest's levels read words `ys` and openings `os`; from the state the guest leaves, any run of the
tail is a run of `whirLevelsOpen` from level `lvl`. -/
theorem osLevels_sound {cfg : OsCfg} {logN lane : ℕ} {Lall : List Whir.Level}
    (hlen : Lall.length = cfg.levels.length)
    (hspec : ∀ i < Lall.length, LvSpec cfg logN i (Lall.getD i default) (Lall.drop (i + 1)))
    (hcall : ∀ i < Lall.length, LvCallees rd cfg i)
    (hfin : ∀ a r, coreProgram.Rel rd cfg.finalMsg a r → MeaningOpeningFinalMessage cfg.yrLen rd a r)
    {cur : E} {kret : List E → Prop} :
    ∀ (j lvl : ℕ) (st : OsSt) (cv : Digest) (xs : List E) (w : WhirState)
      (roots : List (Digest × ℕ × ℕ)), lvl + j + 1 = Lall.length →
      OsLvInv rd σ cfg logN cur lvl st cv xs w roots →
      Stmt.HoldsList (coreProgram.Rel rd) rd σ (osLevels cfg lvl (cfg.levels.drop lvl) st).1 True kret →
      ∃ (ys : List E) (os : List Opening) (cvL : Digest) (wL : WhirState)
        (rootsL : List (Digest × ℕ × ℕ)) (residual : List E),
        OsEndInv rd σ cfg logN cur Lall.length (osLevels cfg lvl (cfg.levels.drop lvl) st).2 cvL
          (xs ++ ys) wL ∧
        residual.length = cfg.yrLen ∧ ReadsAt rd (σ (.n osFmsg)) residual ∧
        ∀ (r : List E) (o : List Opening) (we : WhirEnd) (st' : St),
          Runs (osTailOpen (logN - osLevelF cfg (Lall.length - 1)) lane wL residual) ⟨cvL, r, o, rootsL⟩ we st' →
          Runs (whirLevelsOpen logN lane lvl (Lall.drop lvl) w) ⟨cv, ys ++ r, os ++ o, roots⟩ we st' := by
  intro j
  induction j with
  | zero =>
    intro lvl st cv xs w roots hj hinv h
    have hl : lvl < Lall.length := by omega
    rw [List.drop_eq_getElem_cons (by omega), osLevels_cons, show cfg.levels[lvl] = cfg.lv lvl by
      simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (show lvl < cfg.levels.length by omega)]]
      at h ⊢
    have hrest : cfg.levels.drop (lvl + 1) = [] := List.drop_eq_nil_of_le (by omega)
    rw [hrest] at h ⊢
    simp only [osLevels, List.append_nil] at h ⊢
    have hLrest : Lall.drop (lvl + 1) = [] := List.drop_eq_nil_of_le (by omega)
    have hs := hspec lvl hl
    rw [hLrest] at hs
    obtain ⟨ys1, cv1, w1, chs, hrun1, hw1l, ysM, cv2, residual, pending, roots2, hrunM, ysQ, os, cv',
      w', hrunQ, hlast, -⟩ := osLevel_sound hs (hcall lvl hl) hfin hinv h
    obtain ⟨hresl, hres, hend⟩ := hlast rfl
    refine ⟨ys1 ++ ysM ++ ysQ, os, cv', w', roots2, residual, by simpa [hlen, show lvl + 1 = Lall.length by omega]
      using hend, hresl, hres, fun r o we st' htail => ?_⟩
    rw [List.drop_eq_getElem_cons hl, show Lall[lvl] = Lall.getD lvl default by
      simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hl], hLrest, os_whirLevelsOpen_cons]
    rw [show Lall.length - 1 = lvl by omega] at htail
    rw [← hw1l] at hrunM hrunQ htail
    simp only [List.append_assoc]
    refine Runs.bind (RunsTo.runs hrun1 _ _ _) ?_
    refine Runs.bind (hrunM _ _) ?_
    refine Runs.bind (hrunQ _ _) ?_
    exact htail
  | succ j ih =>
    intro lvl st cv xs w roots hj hinv h
    have hl : lvl < Lall.length := by omega
    rw [List.drop_eq_getElem_cons (by omega), osLevels_cons, show cfg.levels[lvl] = cfg.lv lvl by
      simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (show lvl < cfg.levels.length by omega)]]
      at h ⊢
    rw [holdsList_append] at h
    obtain ⟨h1, h2⟩ := holdsList_true_of (osLevel_noRet _ _ _ _) h
    have hs := hspec lvl hl
    have hne : Lall.drop (lvl + 1) ≠ [] := by
      intro he; have := congrArg List.length he; simp at this; omega
    obtain ⟨ys1, cv1, w1, chs, hrun1, hw1l, ysM, cv2, residual, pending, roots2, hrunM, ysQ, os, cv',
      w', hrunQ, -, hmid⟩ := osLevel_sound hs (hcall lvl hl) hfin hinv h1
    obtain ⟨ys, os', cvL, wL, rootsL, res, hend, hresl, hres, hrun⟩ :=
      ih (lvl + 1) _ cv' _ w' roots2 (by omega) (hmid hne) h2
    refine ⟨ys1 ++ ysM ++ ysQ ++ ys, os ++ os', cvL, wL, rootsL, res, by simpa using hend, hresl, hres,
      fun r o we st' htail => ?_⟩
    obtain ⟨L2, rest2, hrest2⟩ : ∃ L2 rest2, Lall.drop (lvl + 1) = L2 :: rest2 := by
      cases h' : Lall.drop (lvl + 1) with
      | nil => exact absurd h' hne
      | cons a b => exact ⟨a, b, rfl⟩
    have hrun' := hrun r o we st' htail
    rw [List.drop_eq_getElem_cons hl, show Lall[lvl] = Lall.getD lvl default by
      simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hl], os_whirLevelsOpen_cons]
    rw [← hw1l] at hrunM hrunQ
    simp only [List.append_assoc]
    refine Runs.bind (RunsTo.runs hrun1 _ _ _) ?_
    refine Runs.bind (hrunM _ _) ?_
    refine Runs.bind (hrunQ _ _) ?_
    rw [hrest2] at hrun' ⊢
    exact hrun'

end
end LeanVM.Guest.B1
