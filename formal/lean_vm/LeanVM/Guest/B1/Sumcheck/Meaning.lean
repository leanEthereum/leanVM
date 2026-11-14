/-
  LeanVM.Guest.B1.Sumcheck.Meaning

  The statements that the guest's sumcheck functions compute their meanings (`MeaningP.lean`), at
  `coreProgram`.
-/

module

public import LeanVM.Guest.CoreData
public import LeanVM.Guest.B1.Sumcheck.MeaningP

namespace LeanVM.Guest.B1

open LeanVM.Guest.Core

@[expose] public section

/-- `sumcheck_round4`'s core IR is its meaning. -/
abbrev sumcheck_round4_Spec : Prop := sumcheck_round4_SpecP coreProgram

/-- `gkr_rounds__L{n}`'s core IR is its meaning, and `gkr_rounds__L0`'s returns `0`. -/
abbrev gkr_rounds_Spec : Prop := gkr_rounds_SpecP coreProgram

/-- `batch_sumcheck__L23`'s core IR is its meaning. -/
abbrev batch_sumcheck_Spec : Prop := batch_sumcheck_SpecP coreProgram

end
end LeanVM.Guest.B1
