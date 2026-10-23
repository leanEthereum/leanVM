/-
  LeanVM.Guest.B1.Whir.OsStraight

  `open_stacked`'s blocks are straight-line.
-/

module

public import LeanVM.Guest.B1.Whir.StackedC7

/-!
# Straight blocks

Every block of `open_stacked`'s body is atoms, calls and guarded calls, so its calls are the
block's `Main.Stmt.callS` entries.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value

@[expose] public section

theorem os_all_append (a b : List Stmt) :
    (a ++ b).all Main.Stmt.straight = (a.all Main.Stmt.straight && b.all Main.Stmt.straight) := List.all_append

theorem osMat_straight (base off k : ℕ) : (osMat base off k).1.all Main.Stmt.straight = true := by
  unfold osMat; split <;> rfl

theorem osFsNext_straight (s : OsSt) : (osFsNext s).1.all Main.Stmt.straight = true := rfl

theorem osFold_straight (s : OsSt) (fch fo : ℕ) : (osFold s fch fo).1.all Main.Stmt.straight = true := by
  simp only [osFold, os_all_append, osMat_straight, Bool.true_and]; rfl

theorem osFolds_straight (fch : ℕ) : ∀ fo n s, (osFolds fch fo n s).1.all Main.Stmt.straight = true
  | _, 0, _ => rfl
  | fo, n + 1, s => by
    simp only [osFolds, os_all_append, osFold_straight, osFolds_straight fch (fo + 1) n, Bool.and_self]

theorem osFinal_straight (name : String) (fmsg : ℕ) (s : OsSt) :
    (osFinal name fmsg s).1.all Main.Stmt.straight = true := by
  simp only [osFinal, os_all_append, osMat_straight, Bool.true_and]; rfl

theorem osCommit_straight (lvl logCols roots oodz ood : ℕ) (s : OsSt) :
    (osCommit lvl logCols 1 roots oodz ood s).1.all Main.Stmt.straight = true := by
  simp only [osCommit, osOods, os_all_append, List.append_nil]; rfl

theorem osGrind_straight (bits : ℕ) (s : OsSt) : (osGrind bits s).1.all Main.Stmt.straight = true := by
  unfold osGrind; split <;> rfl

theorem osSqueezes_straight (maxSq nsq qpos qbp : ℕ) (loop : String) (s : OsSt) :
    (osSqueezes maxSq nsq qpos qbp loop s).1.all Main.Stmt.straight = true := rfl

theorem osLamPows_straight (lam qw base k : ℕ) : ∀ nq, (osLamPows lam qw base k nq).all Main.Stmt.straight = true
  | 0 => rfl
  | nq + 1 => by
    simp only [osLamPows]
    split
    · rfl
    · simp [List.all_flatten, List.all_map, Main.Stmt.straight]

theorem osQueries_straight (cfg : OsCfg) (lv : OsLvl) (lvl : ℕ) (s : OsSt) :
    (osQueries cfg lv lvl s).1.all Main.Stmt.straight = true := by
  simp only [osQueries, os_all_append, osMat_straight, Bool.and_true]; rfl

theorem osLvStA_straight (cfg : OsCfg) (lvl : ℕ) (s : OsSt) :
    ((osLvF cfg lvl s).1 ++ (osLvM cfg lvl s).1 ++ (osLvG cfg lvl s).1).all Main.Stmt.straight = true := by
  simp only [os_all_append, osLvF, osLvG, osFolds_straight, osGrind_straight, Bool.true_and, Bool.and_true]
  unfold osLvM; split
  · exact osFinal_straight _ _ _
  · unfold osCommit; simp only [os_all_append]
    have : ∀ (os n : ℕ) (st : OsSt),
        (osOods lvl (cfg.lv lvl).logCols osOodz osOod os n st).1.all Main.Stmt.straight = true := by
      intro os n
      induction n generalizing os with
      | zero => intro; rfl
      | succ n ih => intro st; simp only [osOods, os_all_append, ih, Bool.and_true]; rfl
    simp only [this, Bool.and_true]; rfl

theorem osLvStB_straight (cfg : OsCfg) (lvl : ℕ) (sg : OsSt) :
    (osLvStB cfg lvl sg).all Main.Stmt.straight = true := by
  simp only [osLvStB, os_all_append, osLvSq, osSqueezes_straight, osLvL, osLamPows_straight, osLvQ,
    osQueries_straight, Bool.true_and]
  have h1 : (osLvO cfg lvl sg).1.all Main.Stmt.straight = true := by
    unfold osLvO; split
    · rfl
    · have : ∀ (os n sc : ℕ) (st : OsSt),
          (osOodGlues lvl ((osLvSq cfg lvl sg).2.k - 1) os n sc st).1.all Main.Stmt.straight = true := by
        intro os n
        induction n generalizing os with
        | zero => intro _ _; rfl
        | succ n ih => intro sc st; simp only [osOodGlues, os_all_append, ih, Bool.and_true]; rfl
      exact this _ _ _ _
  simp only [h1, Bool.true_and]; rfl

end
end LeanVM.Guest.B1
