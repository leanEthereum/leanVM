/-
  LeanVM.Guest.B1.Terminal.Body

  `check_opening_terminal`'s body is the template `termT`, by kernel evaluation.
-/

module

public import LeanVM.Guest.B1.Terminal.Template

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Guest.Core LeanVM.Guest.B1

@[expose] public section

/-- The function's parameters. -/
def termParams : List V :=
  [.n 0, .n 1, .n 2, .n 3, .n 4, .n 5, .n 6, .n 7, .n 8, .n 9, .n 10, .n 11, .n 12,
      .n 13, .n 14, .n 15, .n 16, .n 17]

/-- The function, found by name, has the eighteen parameters and the template's body. -/
noncomputable def termCheck : Bool :=
  match coreProgram.find? "check_opening_terminal" with
  | some fn => decide (fn.params = termParams) && stmtsEqb fn.body termT
  | none => false

theorem termCheck_eq : termCheck = true := by decide +kernel

theorem termFound : ∃ fn : Fn, coreProgram.find? "check_opening_terminal" = some fn ∧
    fn.params = termParams ∧ fn.body = termT := by
  have h := termCheck_eq
  unfold termCheck at h
  split at h
  · rename_i fn hf
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    exact ⟨fn, hf, h.1, stmtsEqb_sound h.2⟩
  · exact absurd h (by simp)

/-- The template's claims end at value `1746`, the sum at `1744`, `lam_out` at `1745`. -/
theorem termClaims_end : termClaims.2 = (1766, 1764, 1765) := by
  decide +kernel

end
end LeanVM.Guest.B1.VerifySub
