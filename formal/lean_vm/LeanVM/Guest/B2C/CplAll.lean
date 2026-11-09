/-
  LeanVM.Guest.B2C.CplAll

  B2's completeness for every compiled function, from the completeness check alone.
-/

module

public import LeanVM.Guest.B2C.CplSpec
public import LeanVM.Guest.B2C.CplSites
public import LeanVM.Guest.SoundFacts

/-!
# Every function's run

`cpl_run`'s and `sitesApart_of`'s other hypotheses hold of every function: the soundness
windows' checks (`End.winOk_of`, from the checked modules) and the power tree's
(`End.certOf_pows_ok`).
-/

namespace LeanVM.Guest.B2C

open LeanVM.Guest LeanVM.Guest.Memory

@[expose] public section

/-- **B2's completeness for function `j`**, given its completeness check. -/
theorem cplRun_of {j : ℕ} (h1 : 1 ≤ j) (hj : j < nFns) (hok : CplOk j) : CplRun j :=
  cpl_run h1 hj hok (End.winOk_of h1 hj) (End.certOf_pows_ok j)

/-- **The call sites of every path are apart**, given every function's completeness check
(`FrameAll`'s hypothesis). -/
theorem sitesApart_all_of (hok : ∀ j, 1 ≤ j → j < nFns → CplOk j) :
    ∀ j σ es vs, 1 ≤ j → j < nFns → walk σ (coreOf j).body = .ret es vs → SitesApart j es :=
  fun j _ _ _ h1 hj hw ↦ sitesApart_of (hok j h1 hj) (End.winOk_of h1 hj) hw

end
end LeanVM.Guest.B2C
