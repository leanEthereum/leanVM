/-
  LeanVM.Guest.B1.Terminal.Body

  `check_opening_terminal`'s body is the template `termT`, by kernel evaluation.
-/

module

public import LeanVM.Guest.B1.Terminal.Template
public import LeanVM.Guest.CoreData
import LeanVM.Guest.ValRef
import LeanVM.Guest.Data.ValNames.«check_opening_terminal»

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Guest.Core LeanVM.Guest.B1

@[expose] public section

/-- The function's parameters. -/
def termParams : List V :=
  [.n (val% «check_opening_terminal» "g_squares"), .n (val% «check_opening_terminal» "zeta"), .n (val% «check_opening_terminal» "chi"), .n (val% «check_opening_terminal» "rm"), .n (val% «check_opening_terminal» "g_bus_mu"), .n (val% «check_opening_terminal» "g_zc_n"), .n (val% «check_opening_terminal» "g_log_mem"), .n (val% «check_opening_terminal» "tau_keccak_g"), .n (val% «check_opening_terminal» "kappa_base"), .n (val% «check_opening_terminal» "lam_cl"), .n (val% «check_opening_terminal» "col_offsets"), .n (val% «check_opening_terminal» "z_vals"), .n (val% «check_opening_terminal» "c_table"),
      .n (val% «check_opening_terminal» "point"), .n (val% «check_opening_terminal» "point1"), .n (val% «check_opening_terminal» "inner_total"), .n (val% «check_opening_terminal» "yr_at_tail"), .n (val% «check_opening_terminal» "sumcheck_target"), .n (val% «check_opening_terminal» "ood_z"), .n (val% «check_opening_terminal» "gmv")]

/-- The function, found by name, has the twenty parameters and the template's body. -/
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

/-- The template's claims end at value `1694`, the sum at `1692`, `lam_out` at `1693`. -/
theorem termClaims_end : termClaims.2 = (1694, 1692, 1693) := by
  decide +kernel

end
end LeanVM.Guest.B1.VerifySub
