/-
  LeanVM.Guest.Res.SubDefs

  The `sub` residuals' families, checked per certificate: a run inside a split, a read inside
  `child_claim_list_any`'s table, a read of the gap walk.
-/

module

public import LeanVM.Guest.EndExecRS
public import LeanVM.Guest.Res.AnyData
public import LeanVM.Guest.Res.MonoDefs
public import LeanVM.Guest.Res.ResGiven
public import LeanVM.Guest.Res.FamDefs

/-!
# The `sub` residuals' families

`subB j x`: residual `x` of function `j` is no `sub` residual, or one of the families
(`splitB`, `anyResB anyLink`, `monoResB`, and those read off the function's code, `subFamB`). `SubOk exc K`: certificate `K` is listed in `exc`, or
each of its residuals passes `subB` at its function's index, decided per certificate (`subOk_of`).
`EndExec.resOpen_subOk` (`EndExecRF`): given `SubOk resExc` of every certificate and the listed
certificates' residuals, no `sub` residual outside the families is left open.
-/

namespace LeanVM.Guest.Res

open LeanVM.Guest LeanVM.Guest.Core

@[expose] public section

/-- **The `sub` residuals' families**, the families read off the code from the witness `w`. -/
noncomputable def subB (j : ℕ) (w : Wit) : Mode.Res → Bool
  | .sub a bs => splitB j (.sub a bs) || anyResB anyLink j (.sub a bs) || monoResB j (.sub a bs) ||
      subFamB j w (.sub a bs)
  | _ => true

/-- **A certificate's `sub` residuals in the families**: it is listed in `exc`, or each is at its
function's index `j`, with a witness `w` of its code. -/
def SubOk (exc : List Mode.Cert) (K : Mode.Cert) : Prop :=
  K ∈ exc ∨ ∃ j w, j < nFns ∧ (fnOf j).entryPc = K.F.entry ∧ witOk j w = true ∧
    allV (fun l ↦ l.all (subB j w)) K.F.res = true

theorem subOk_of {exc : List Mode.Cert} {K : Mode.Cert} {j : ℕ} {w : Wit}
    (h : (decide (j < nFns) && (fnOf j).entryPc == K.F.entry && witOk j w &&
      allV (fun l ↦ l.all (subB j w)) K.F.res) = true) :
    SubOk exc K := by
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  exact Or.inr ⟨j, w, h.1.1.1, h.1.1.2, h.1.2, h.2⟩

theorem subOk_exc {exc : List Mode.Cert} {K : Mode.Cert} (h : K ∈ exc) : SubOk exc K := Or.inl h

end

end LeanVM.Guest.Res
