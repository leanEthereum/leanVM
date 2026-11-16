/-
  LeanVM.Guest.Backend.Guest.Cpl.Complete

  The guest is complete within the deployed budget, through the back end: the instance's frame
  runs fit their frames and are consecutive, and the pieces of completeness at the instance.
-/

module

public import LeanVM.Guest.Backend.Guest.Cpl.Jt
public import LeanVM.Guest.Backend.Guest.Cpl.Budget
public import LeanVM.Guest.Backend.Complete.PathRun

/-!
# Completeness through the back end

`guest_complete_backend` is `Budget.guest_complete`'s statement at the instance `HG CG certG` of
`Inst.lean`: B2's composition (`b2_completeG`, `b2_countG`) on `cplRunG` and `frameG`, the
checker's facts `kFactsAllG`, the counts' invariance `Deployed.cntRetemp`, the frame runs' facts
`runsFitG`, `runsConsecG`, and the jump
table's cells `jtCells`. It rests on the frame side of the back end's completeness
(`Complete.FrameWordsStmt`) and the per-function test passing for every entry (`CplOkAll`).
-/

namespace LeanVM.Guest.Backend.Cpl

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Memory GuestPiece
open LeanVM.Guest.Completeness LeanVM.Guest.Budget
open LeanVM.Guest.End (GuestCompleteWithin)
open LeanVM.Guest.B1.VerifySub (vsBoundAt vkBound)

@[expose] public section

/-- **Every frame run fits its frame** at the back end's cells. -/
theorem runsFitG (hok : CplOkAll) : Lift.RunsFit Deployed.fs certG := by
  intro f fn hf p r rs ha
  obtain ⟨i, hix⟩ := ix_of_find hf
  have F := fnAt hix
  rw [F.find] at hf
  cases hf
  have ha' : Atom.frameAddr p (r :: rs) ∈ Lift.blockAtoms (tfG i).core.body := by rw [F.core]; exact ha
  have h := (run_cells hok hix ha' rs.length (by simp)).2.2.1
  have hle := fsWant_le i
  rw [F.fs_eq]
  omega

/-- **Every frame run's cells are consecutive** at the back end's cells. -/
theorem runsConsecG (hok : CplOkAll) : B1.RunsConsec certG := by
  intro f fn hf p r rs ha k hk
  obtain ⟨i, hix⟩ := ix_of_find hf
  have F := fnAt hix
  rw [F.find] at hf
  cases hf
  have ha' : Atom.frameAddr p (r :: rs) ∈ Lift.blockAtoms (tfG i).core.body := by rw [F.core]; exact ha
  rw [F.cert (r :: rs)[k], (run_cells hok hix ha' k hk).1]
  rfl

/-- **The composition's hypotheses** at the instance through the back end. -/
theorem b2HypsG (hok : CplOkAll) (hFC : Complete.FrameConsistentStmt) :
    B2HypsG FHG HG CG certG :=
  ⟨cplRunG hok hFC jtCells, frameG hok hFC, fun _ _ _ _ ht => tableG hok ht⟩

/-- **The guest is complete within the deployed budget**, through the back end: given the frame
side of the back end's completeness and the per-function test of every entry
(`Budget.guest_complete`'s statement). -/
theorem guest_complete_backend (hFW : Complete.FrameWordsStmt) (hok : CplOkAll) :
    GuestCompleteWithin (deployedBudget (vsBoundAt Count.vsWordsOs vkBound)) :=
  have hB := b2HypsG hok (Complete.frameConsistent_of_words hFW)
  guest_complete_at (H := HG) (C := CG)
    (fun _ hm => ⟨hm, kFactsAllG hok, Deployed.cntRetemp coreProgram_fresh, fun _ _ _ _ ht => tableG hok ht,
      b2_completeG hB, b2_countG hB⟩)
    (runsFitG hok) (runsConsecG hok)

end
end LeanVM.Guest.Backend.Cpl

/-- info: 'LeanVM.Guest.Backend.Cpl.guest_complete_backend' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Backend.Cpl.guest_complete_backend
