/-
  LeanVM.Guest.B2C.RunsFit

  The deployed certificates' frame runs fit their frames (`Lift.RunsFit fs cert`) and meet only at
  common values (`Lift.RunsApart cert`), from the sharing check's lists (`FnStatic`).
-/

module

public import LeanVM.Guest.B2C.Cells
public import LeanVM.Guest.B2C.Static
public import LeanVM.Guest.B2C.Shared
public import LeanVM.Guest.SoundFacts
public import LeanVM.Guest.Lift.OqFits

/-!
# The deployed frame runs

The sharing check confirms, once per function, that every value of a frame run is listed with
its cell, the run's cells consecutive (`FnStatic.run`), every listed cell in the frame
(`FnStatic.runsIn`) and one value per cell (`FnStatic.runsFun`). So a run fits its frame
(`runsFit`), and two runs meeting at a cell hold one value there (`runsApart`).
-/

namespace LeanVM.Guest.B2C

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Memory
open LeanVM.Guest.Exec LeanVM.Guest.Check

@[expose] public section

/-- **The sharing check's facts of function `f`'s index.** -/
theorem fnStatic_of {f : String} {j : ℕ} (hj : idxOf f = some j) : FnStatic j := by
  obtain ⟨i, rfl, -, -, -, -, -, -, h1, h2⟩ := fn_of_idx hj
  exact fnStatic (Shared.all _ h1 h2) (End.winOk_of h1 h2)

theorem idx_of_find {f : String} {fn : Fn} (h : coreProgram.find? f = some fn) :
    ∃ j, idxOf f = some j ∧ coreOf j = fn ∧ fs f = fsN j ∧ ∀ v, cert f v = cellJ j v := by
  cases hj : idxOf f with
  | none =>
    have : coreProgram.indexOf? f = none := by
      unfold idxOf at hj; exact Option.map_eq_none_iff.mp hj
    rw [find?_none this] at h
    cases h
  | some j =>
    obtain ⟨i, rfl, hi, hn, hf, hc, hfs, hcert, -⟩ := fn_of_idx hj
    rw [hf, Option.some.injEq] at h
    exact ⟨_, rfl, by rw [hc, h], hfs, hcert⟩

mutual
theorem stmtAtoms_eq : ∀ s : Stmt, Lift.stmtAtoms s = sAtoms s
  | .atom _ => rfl
  | .ite _ z n => by rw [Lift.stmtAtoms, sAtoms, blockAtoms_eq z, blockAtoms_eq n]
  | .match_ _ arms => by rw [Lift.stmtAtoms, sAtoms, armsAtoms_eq arms]
  | .call .. => rfl
  | .callIf .. => rfl
  | .dispatch .. => rfl
  | .ret _ => rfl

theorem blockAtoms_eq : ∀ ss : List Stmt, Lift.blockAtoms ss = lAtoms ss
  | [] => rfl
  | s :: ss => by rw [Lift.blockAtoms, lAtoms, stmtAtoms_eq s, blockAtoms_eq ss]

theorem armsAtoms_eq : ∀ as : List (List Stmt), Lift.armsAtoms as = aAtoms as
  | [] => rfl
  | a :: as => by rw [Lift.armsAtoms, aAtoms, blockAtoms_eq a, armsAtoms_eq as]
end

/-- **Every deployed frame run fits its frame.** -/
theorem runsFit : Lift.RunsFit fs cert := by
  intro f fn hf p r rs hm
  obtain ⟨j, hj, hc, hfs, hcert⟩ := idx_of_find hf
  have FS := fnStatic_of hj
  rw [← hc, blockAtoms_eq] at hm
  obtain ⟨-, hcell, hrun⟩ := FS.run p r rs hm rs.length (by simp)
  have hin := (FS.runsIn _ hrun).2
  simp only at hin
  rw [hfs, hcert]
  omega

/-- **Two deployed frame runs of a body meet only at a common value.** -/
theorem runsApart : Lift.RunsApart cert := by
  intro f fn hf p r rs p' r' rs' hm hm' k hk k' hk' he
  obtain ⟨j, hj, hc, -, hcert⟩ := idx_of_find hf
  have FS := fnStatic_of hj
  rw [← hc, blockAtoms_eq] at hm hm'
  obtain ⟨hv, -, hrun⟩ := FS.run p r rs hm k hk
  obtain ⟨hv', -, hrun'⟩ := FS.run p' r' rs' hm' k' hk'
  rw [hcert, hcert] at he
  have hidx := FS.runsFun _ hrun _ hrun' he
  simp only at hidx
  rw [hv, hv', hidx]

end
end LeanVM.Guest.B2C
