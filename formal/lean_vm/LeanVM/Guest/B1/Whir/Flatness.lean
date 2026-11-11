/-
  LeanVM.Guest.B1.Whir.Flatness

  The template's body is flat (atoms and calls) up to its final `ret`.
-/

module

public import LeanVM.Guest.B1.Whir.FinishSplit
public import LeanVM.Guest.B1.Whir.ResLoop
public import LeanVM.Guest.B1.Whir.SqLoop

/-!
# The body is flat

`osBodyA_flat`: every block of `osBodyA c` (`Whir/FinishSplit`) is atoms, calls and conditional
calls, so the body holds of a valuation exactly when each of its statements does and the `ret`'s
words are the returns (`Flat.holdsList_flat_ret`).
-/

namespace LeanVM.Guest.B1.Whir

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest LeanVM.Guest.B1

@[expose] public section

/-- A list of statements is flat. -/
abbrev Flat (l : List Stmt) : Prop := l.all Stmt.flat = true

theorem flat_append {a b : List Stmt} (ha : Flat a) (hb : Flat b) : Flat (a ++ b) := by
  simp only [Flat, List.all_append, ha, hb, Bool.and_self]

theorem flat_cons {s : Stmt} {a : List Stmt} (hs : Stmt.flat s = true) (ha : Flat a) :
    Flat (s :: a) := by
  simp only [Flat, List.all_cons, hs, ha, Bool.true_and]

theorem flat_flatten {l : List (List Stmt)} (h : ∀ a ∈ l, Flat a) : Flat l.flatten := by
  simp only [Flat, List.all_flatten, List.all_eq_true] at h ⊢
  exact h

theorem osMatP_flat (P : List (ℕ × ℕ × ℕ)) (m : List OsMat) (b o k : ℕ) :
    Flat (osMatP P m b o k).1 := by
  unfold osMatP; split_ifs <;> rfl

theorem osMatS_flat (P : List (ℕ × ℕ × ℕ)) (b o : ℕ) (s : OsSt) : Flat (osMatS P b o s).1 :=
  osMatP_flat _ _ _ _ _

theorem osCurS_flat (s : OsSt) : Flat (osCurS s).1 := osMat_flat _ _ _

theorem osPad_flat (pad : Option ℕ) (k : ℕ) : Flat (osPad pad k).1 := by
  cases pad <;> rfl

theorem osHeap_flat (e k : ℕ) : Flat (osHeap e k) := rfl

theorem osLoopCall_flat (name : String) (e0 n : ℕ) (args : List ℕ) (k : ℕ) :
    Flat (osLoopCall name e0 n args k) := rfl

theorem osRounds_flat (P : List (ℕ × ℕ × ℕ)) : ∀ i n s, Flat (osRounds P i n s).1
  | _, 0, _ => rfl
  | i, n + 1, _ => flat_append
    (flat_append (flat_append (flat_append (osCurS_flat _) (osMatS_flat _ _ _ _)) (osMatS_flat _ _ _ _))
      rfl) (osRounds_flat P (i + 1) n _)

theorem osFinalMsg_flat (c : OsCfg) (lv : OsLv) (s : OsSt) : Flat (osFinalMsg c lv s).1 :=
  flat_append (osCurS_flat _) rfl

theorem osCommit_flat (c : OsCfg) (lvl : ℕ) (lv : OsLv) (s : OsSt) : Flat (osCommit c lvl lv s).1 := by
  unfold osCommit
  simp only [Flat, List.all_append, List.all_cons, List.all_nil, List.all_map, Stmt.flat,
    osHeap_flat _ _, osCurS_flat _, osMatS_flat _ _ _ _, osPad_flat _ _, Bool.and_true, Bool.true_and]
  simp [Stmt.flat, osKeccak]

theorem osSqueezes_flat (c : OsCfg) (lvl : ℕ) (lv : OsLv) (s : OsSt) :
    Flat (osSqueezes c lvl lv s).1 := by
  unfold osSqueezes
  simp only [Flat, List.all_append, osHeap_flat _ _, osMatS_flat _ _ _ _, osLoopCall_flat _ _ _ _ _,
    Bool.and_true, Bool.true_and]
  simp [Stmt.flat]

theorem osLam_flat (s : OsSt) : Flat (osLam s).1 := by
  unfold osLam
  simp only [Flat, List.all_append, osPad_flat _ _]
  simp [Stmt.flat, osKeccak]

theorem osCap_flat (c : OsCfg) (lvl : ℕ) (lv : OsLv) (s : OsSt) : Flat (osCap c lvl lv s).1 := by
  unfold osCap
  simp only [Flat, List.all_append, osMatS_flat _ _ _ _, Bool.true_and]
  rfl

theorem osHsCoefs_flat (src dst : ℕ) (sc : ℕ → ℕ) (si di : ℕ) :
    ∀ n i k, Flat (osHsCoefs src dst sc si di n i k).1
  | 0, _, _ => rfl
  | n + 1, i, k => by
    refine flat_append ?_ (osHsCoefs_flat src dst sc si di n (i + 1) _)
    unfold osHsCoef; split_ifs <;> rfl

theorem osHsMid_flat (lvl : ℕ) (lv : OsLv) (s : OsSt) : Flat (osHsMid lvl lv s).1 :=
  osHsCoefs_flat _ _ _ _ _ _ _ _

theorem osHsFinal_flat (c : OsCfg) (lv : OsLv) (s : OsSt) : Flat (osHsFinal c lv s).1 :=
  flat_append (osHeap_flat _ _) (osHsCoefs_flat _ _ _ _ _ _ _ _)

theorem osQueries_flat (c : OsCfg) (lvl : ℕ) (lv : OsLv) (s : OsSt) : Flat (osQueries c lvl lv s).1 := by
  have hm : ∀ P b o (s : OsSt), (osMatS P b o s).1.all Stmt.flat = true := osMatS_flat
  unfold osQueries
  dsimp only
  split_ifs <;> simp only [Flat, List.all_append, hm, List.all_cons, List.all_nil, Stmt.flat,
    Bool.and_true]

theorem osGlue_flat (lvl : ℕ) (lv : OsLv) (s : OsSt) : Flat (osGlue lvl lv s).1 := by
  unfold osGlue
  simp only [Flat, List.all_append, osPowSteps_flat, Bool.and_true]
  simp [Stmt.flat]

theorem osLevel_flat (c : OsCfg) (lvl : ℕ) (lv : OsLv) (s : OsSt) : Flat (osLevel c lvl lv s).1 := by
  unfold osLevel
  simp only [Flat, List.all_append]
  refine Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨
    Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨
    Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨osRounds_flat _ _ _ _, ?_⟩, rfl⟩,
    osSqueezes_flat _ _ _ _⟩, ?_⟩, osCap_flat _ _ _ _⟩, ?_⟩, osQueries_flat _ _ _ _⟩, ?_⟩
  · split_ifs
    · exact osFinalMsg_flat _ _ _
    · exact osCommit_flat _ _ _ _
  · split_ifs
    · rfl
    · exact osLam_flat _
  · split_ifs
    · exact osHsFinal_flat _ _ _
    · exact osHsMid_flat _ _ _
  · split_ifs
    · rfl
    · exact osGlue_flat _ _ _

theorem osLevels_flat (c : OsCfg) : ∀ lvl lvs s, Flat (osLevels c lvl lvs s).1
  | _, [], _ => rfl
  | lvl, _ :: rest, _ => flat_append (osLevel_flat _ _ _ _) (osLevels_flat c (lvl + 1) rest _)

theorem osHead_flat (c : OsCfg) : Flat (osHead c).1 := rfl

theorem osTailRounds_flat (tch : ℕ) : ∀ j n s, Flat (osTailRounds tch j n s).1
  | _, 0, _ => rfl
  | j, n + 1, _ => flat_append (flat_append (osCurS_flat _) rfl) (osTailRounds_flat tch (j + 1) n _)

theorem osTail_flat (c : OsCfg) (s : OsSt) : Flat (osTail c s).1 := by
  unfold osTail
  refine flat_append (flat_append (osHeap_flat _ _) (osTailRounds_flat _ _ _ _)) ?_
  refine flat_flatten fun a ha ↦ ?_
  simp only [List.mem_map, List.mem_range] at ha
  obtain ⟨i, -, rfl⟩ := ha
  rfl

theorem osPtBlks_flat (c : OsCfg) (pt pt1 tch : ℕ) : ∀ i n k, Flat (osPtBlks c pt pt1 tch i n k).1
  | _, 0, _ => rfl
  | i, n + 1, k => by
    refine flat_append ?_ (osPtBlks_flat c pt pt1 tch (i + 1) n _)
    unfold osPtBlk; split <;> rfl

theorem osBasisRow_flat (bd : ℕ) : ∀ cs sc after k, Flat (osBasisRow bd cs sc after k).1
  | [], _, _, _ => rfl
  | (slot, src, inv) :: rest, sc, after, k => by
    refine flat_append ?_ (osBasisRow_flat bd rest _ _ _)
    unfold osBasisBlk
    dsimp only
    split_ifs <;> split <;> simp [Flat, Stmt.flat]

theorem osBases_flat (c : OsCfg) (tch bd ls la : ℕ) : ∀ lvl lvs k, Flat (osBases c tch bd ls la lvl lvs k).1
  | _, [], _ => rfl
  | lvl, _ :: rest, _ => flat_cons rfl (flat_append (flat_append (osBasisRow_flat _ _ _ _ _) rfl)
      (osBases_flat c tch bd ls la (lvl + 1) rest _))

theorem osResidual_flat (c : OsCfg) (ich bd ls la lvl : ℕ) (lv : OsLv) (k : ℕ) :
    Flat (osResidual c ich bd ls la lvl lv k).1 := by
  unfold osResidual
  simp only [Flat, List.all_append, osResSteps_flat, Bool.and_true]
  rfl

theorem osResiduals_flat (c : OsCfg) (ich bd ls la : ℕ) :
    ∀ lvl lvs k, Flat (osResiduals c ich bd ls la lvl lvs k).1
  | _, [], _ => rfl
  | lvl, _ :: rest, _ => flat_append (osResidual_flat _ _ _ _ _ _ _ _)
      (osResiduals_flat c ich bd ls la (lvl + 1) rest _)

theorem osOodFacs_flat (sc : ℕ) : ∀ cs k, Flat (osOodFacs sc cs k).1
  | [], _ => rfl
  | (_, _) :: rest, k => flat_append rfl (osOodFacs_flat (k + 5) rest _)

theorem osOodWeight_flat (c : OsCfg) (tch prevCols ol : ℕ) (lv : OsLv) (k : ℕ) :
    Flat (osOodWeight c tch prevCols ol lv k).1 := flat_cons rfl (osOodFacs_flat _ _ _)

theorem osAcc_flat (acc : Option ℕ) (w k : ℕ) : Flat (osAcc acc w k).1 := by
  cases acc <;> rfl

theorem osOodWeights_flat (c : OsCfg) (tch : ℕ) :
    ∀ prevCols ol lvs acc k, Flat (osOodWeights c tch prevCols ol lvs acc k).1
  | _, _, [], _, _ => rfl
  | _, _, _ :: rest, _, _ => flat_append (flat_append (osOodWeight_flat _ _ _ _ _ _)
      (osAcc_flat _ _ _)) (osOodWeights_flat c tch _ _ rest _ _)

theorem osFinishA_flat (c : OsCfg) (st : OsSt) (tch : ℕ) : Flat (osFinishA c st tch).1 := by
  unfold osFinishA
  dsimp only
  refine flat_append (flat_append (flat_append (flat_append (flat_append (flat_append
    (flat_append (flat_append (flat_append (flat_append rfl (osPtBlks_flat _ _ _ _ _ _ _))
    (osHeap_flat _ _)) (osHeap_flat _ _)) (osHeap_flat _ _)) (osBases_flat _ _ _ _ _ _ _ _))
    (osHeap_flat _ _)) rfl) (osResiduals_flat _ _ _ _ _ _ _ _)) (osOodWeights_flat _ _ _ _ _ _ _))
    rfl

/-- **The body before its `ret` is flat.** -/
theorem osBodyA_flat (c : OsCfg) : (osBodyA c).all Stmt.flat = true :=
  flat_append (flat_append (flat_append (osHead_flat c) (osLevels_flat _ _ _ _)) (osTail_flat _ _))
    (osFinishA_flat _ _ _)

end
end LeanVM.Guest.B1.Whir
