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

/-- `batch_sumcheck__L23`'s core IR is its meaning. -/
abbrev batch_sumcheck_Spec : Prop := batch_sumcheck_SpecP coreProgram

end
end LeanVM.Guest.B1
