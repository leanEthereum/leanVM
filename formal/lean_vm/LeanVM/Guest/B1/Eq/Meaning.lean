/-
  LeanVM.Guest.B1.Eq.Meaning

  `MeaningP.lean`'s statements at the guest's `coreProgram`.
-/

module

public import LeanVM.Guest.CoreData
public import LeanVM.Guest.B1.Eq.MeaningP

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-- `eq_prefix_run_SpecP` at the guest's `coreProgram`. -/
abbrev eq_prefix_run_Spec : Prop := eq_prefix_run_SpecP coreProgram

/-- `eq_prefix_chain_SpecP` at the guest's `coreProgram`. -/
abbrev eq_prefix_chain_Spec : Prop := eq_prefix_chain_SpecP coreProgram

/-- `plus_one_run_SpecP` at the guest's `coreProgram`. -/
abbrev plus_one_run_Spec : Prop := plus_one_run_SpecP coreProgram

/-- `rs_eq_rows_SpecP` at the guest's `coreProgram`. -/
abbrev rs_eq_rows_Spec : Prop := rs_eq_rows_SpecP coreProgram

/-- `rs_eq_run_SpecP` at the guest's `coreProgram`. -/
abbrev rs_eq_run_Spec : Prop := rs_eq_run_SpecP coreProgram

/-- `fold_final_msg_SpecP` at the guest's `coreProgram`. -/
abbrev fold_final_msg_Spec : Prop := fold_final_msg_SpecP coreProgram

end
end LeanVM.Guest.B1
