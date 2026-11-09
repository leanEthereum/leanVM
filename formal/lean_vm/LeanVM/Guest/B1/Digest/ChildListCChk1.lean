/-
  LeanVM.Guest.B1.Digest.ChildListCChk1

  `child_claim_list_any`'s big frame loop `__loop17` (136 records), evaluated: `anycOk`'s head,
  canonical inputs and atoms around the records, each a kernel check of its own (the records by
  windows in `ChildListCW{q}`).
-/

module

public import LeanVM.Guest.B1.Digest.ChildListCChk

namespace LeanVM.Guest.B1.Digest

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.B1.Fwd

@[expose] public section

set_option maxRecDepth 100000 in
theorem any136c_head : anycHead (coreProgram.getD 349 default) "__loop17" = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem any136c_canon : anycCanon (coreProgram.getD 349 default) 136 22 1924 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem any136c_edge : anycEdge (coreProgram.getD 349 default) 136 22 15 21 1924 = true := by
  decide +kernel

end
end LeanVM.Guest.B1.Digest
