/-
  LeanVM.Guest.B1.Digest.ChildListCChk1

  `child_claim_list_any`'s big frame loop `child_claim_list_any_loop0` (136 records), evaluated:
  `anycOk`'s head, atoms around the records, each a kernel check of its own (the records by
  windows in `ChildListCW{q}`).
-/

module

public import LeanVM.Guest.B1.Digest.ChildListCChk
public import LeanVM.Guest.Data.NameStrings

namespace LeanVM.Guest.B1.Digest

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.B1.Fwd

@[expose] public section

set_option maxRecDepth 100000 in
theorem any136c_head : anycHead (coreProgram.getD idx% «child_claim_list_any_loop0» default)
    name% «child_claim_list_any_loop0» = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem any136c_edge : anycEdge (coreProgram.getD idx% «child_claim_list_any_loop0» default) 136 22
    15 21 1924 = true := by
  decide +kernel

end
end LeanVM.Guest.B1.Digest
