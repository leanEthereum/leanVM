/-
  LeanVM.Guest.B1.Place.LrPure

  `level_residual`'s loops place nothing and call only themselves, at every row.
-/

module

public import LeanVM.Guest.B1.Whir.HelperT
public import LeanVM.Guest.Memory.Placed

/-!
# `level_residual`'s loops are pure

The residual chains' blocks (`osResChain`, `novel_eval`'s levels, `residual_query`, the steps)
are atoms that place nothing; a loop adds its tail, a conditional call of itself. So both loops are
pure in themselves (`lrLoop1_pure`, `lrLoop2_pure`) at every row, by structure.
-/

namespace LeanVM.Guest.B1.Whir

open LeanVM.Guest.Core LeanVM.Guest.Memory

@[expose] public section

variable (S : List String)

theorem pureList_eq_all : ∀ ss : List Stmt, Stmt.pureList S ss = ss.all (Stmt.pure S)
  | [] => rfl
  | s :: ss => by rw [Stmt.pureList, pureList_eq_all ss, List.all_cons]

theorem osResChain_pure (bd ro vo ncols : ℕ) : ∀ (f t ch pe : ℕ) (ws : List ℕ) (k : ℕ),
    (osResChain bd ro vo ncols f t ch pe ws k).1.all (Stmt.pure S) = true
  | 0, _, _, _, _, _ => rfl
  | f + 1, t, ch, pe, ws, k => by
    unfold osResChain
    split_ifs <;> simp [Stmt.pure, atomUnplaced, osResChain_pure bd ro vo ncols f]

theorem osNovelLevel_pure (hp ho : ℕ) (ins : Option (List ℕ)) (nIn w : ℕ) :
    ∀ (f k : ℕ), (osNovelLevel hp ho ins nIn w f k).1.all (Stmt.pure S) = true
  | 0, _ => rfl
  | f + 1, k => by
    unfold osNovelLevel
    simp only [List.all_append, osNovelLevel_pure hp ho ins nIn w f, Bool.and_true]
    rcases ins with _ | vs <;> split_ifs <;> simp [Stmt.pure, atomUnplaced]

theorem osNovelLevels_pure (hp ho n nbits : ℕ) (ws : List ℕ) :
    ∀ (f i : ℕ) (ins : Option (List ℕ)) (k : ℕ),
      (osNovelLevels hp ho n nbits ws f i ins k).1.all (Stmt.pure S) = true
  | 0, _, _, _ => rfl
  | f + 1, i, ins, k => by
    unfold osNovelLevels
    simp only [List.all_append, osNovelLevel_pure, osNovelLevels_pure hp ho n nbits ws f,
      Bool.and_self]

theorem osResQuery_pure (pos bd ro hp ho vo ncols nhs hbits k : ℕ) :
    (osResQuery pos bd ro hp ho vo ncols nhs hbits k).1.all (Stmt.pure S) = true := by
  unfold osResQuery osNovelEval
  split_ifs <;> simp [Stmt.pure, atomUnplaced, osResChain_pure, osNovelLevels_pure]

theorem osResSteps_pure (pp bd ro hp ho vo ncols nhs hbits mu : ℕ) :
    ∀ (js : List ℕ) (h hh k : ℕ),
      (osResSteps pp bd ro hp ho vo ncols nhs hbits mu js h hh k).1.all (Stmt.pure S) = true
  | [], _, _, _ => rfl
  | j :: js, h, hh, k => by
    simp [osResSteps, osResStep, Stmt.pure, atomUnplaced, osResQuery_pure,
      osResSteps_pure pp bd ro hp ho vo ncols nhs hbits mu js]

theorem osLoopTail_pure (name : String) (n k : ℕ) : (osLoopTail name n k).all (Stmt.pure [name]) = true := by
  simp [osLoopTail, Stmt.pure, atomUnplaced]

/-- **The batches' loop is pure in itself.** -/
theorem lrLoop1_pure (cols nhs hbits : ℕ) (name : String) :
    Stmt.pureList [name] (lrLoop1Body cols nhs hbits name) = true := by
  rw [pureList_eq_all]
  simp [lrLoop1Body, Stmt.pure, atomUnplaced, osResSteps_pure, osLoopTail_pure]

/-- **The rest's loop is pure in itself.** -/
theorem lrLoop2_pure (cols nhs hbits : ℕ) (name : String) :
    Stmt.pureList [name] (lrLoop2Body cols nhs hbits name) = true := by
  rw [pureList_eq_all]
  simp [lrLoop2Body, Stmt.pure, atomUnplaced, osResQuery_pure, osLoopTail_pure]

end
end LeanVM.Guest.B1.Whir
