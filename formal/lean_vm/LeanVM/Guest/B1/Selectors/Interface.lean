/-
  LeanVM.Guest.B1.Selectors.Interface

  `InterfaceP.lean`'s statements at the guest's `coreProgram`.
-/

module

public import LeanVM.Guest.CoreData
public import LeanVM.Guest.B1.Selectors.InterfaceP

namespace LeanVM.Guest.B1.Tables

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-- `index_mle_SpecP` at the guest's `coreProgram`. -/
abbrev index_mle_Spec : Prop := index_mle_SpecP coreProgram

/-- `index_mle_complete_SpecP` at the guest's `coreProgram`. -/
abbrev index_mle_complete_Spec : Prop := index_mle_complete_SpecP coreProgram

/-- `sel_partial_nibble_SpecP` at the guest's `coreProgram`. -/
abbrev sel_partial_nibble_Spec : Prop := sel_partial_nibble_SpecP coreProgram

/-- `sel_partial_nibble_complete_SpecP` at the guest's `coreProgram`. -/
abbrev sel_partial_nibble_complete_Spec : Prop := sel_partial_nibble_complete_SpecP coreProgram

/-- `shared_selector_tables_SpecP` at the guest's `coreProgram`. -/
abbrev shared_selector_tables_Spec : Prop := shared_selector_tables_SpecP coreProgram

/-- `shared_selector_tables_complete_SpecP` at the guest's `coreProgram`. -/
abbrev shared_selector_tables_complete_Spec : Prop := shared_selector_tables_complete_SpecP coreProgram

/-- `block_selector_tab_SpecP` at the guest's `coreProgram`. -/
abbrev block_selector_tab_Spec : Prop := block_selector_tab_SpecP coreProgram

/-- `block_selector_tab_complete_SpecP` at the guest's `coreProgram`. -/
abbrev block_selector_tab_complete_Spec : Prop := block_selector_tab_complete_SpecP coreProgram

/-- `block_selector_SpecP` at the guest's `coreProgram`. -/
abbrev block_selector_Spec : Prop := block_selector_SpecP coreProgram

/-- `block_selector_complete_SpecP` at the guest's `coreProgram`. -/
abbrev block_selector_complete_Spec : Prop := block_selector_complete_SpecP coreProgram

/-- `selector_tables_SpecP` at the guest's `coreProgram`. -/
abbrev selector_tables_Spec : Prop := selector_tables_SpecP coreProgram

/-- `column_selector_SpecP` at the guest's `coreProgram`. -/
abbrev column_selector_Spec : Prop := column_selector_SpecP coreProgram

/-- `column_selector_complete_SpecP` at the guest's `coreProgram`. -/
abbrev column_selector_complete_Spec : Prop := column_selector_complete_SpecP coreProgram

end
end LeanVM.Guest.B1.Tables
