/-
  LeanVM.Guest.B1.Main.MainNoAdv

  No advised buffer below `main`'s callees but its claim lists' digests, `da_verify` and the children
  loop, nor below theirs but `verify_sub`, by the kernel.
-/

module

public import LeanVM.Guest.Memory.HeapSlots
public import LeanVM.Guest.CoreRef

/-!
# `main`'s callees without advised buffers

`NoAdvG` of `main`'s callees other than `claim_list_digest`, `da_verify` and the children loop
(`exponent_tables_noAdv` and the rest) and of the children loop's claim lists' digests
(`cc_noAdv`), each by the kernel through its caller's callee table (`noAdvG_of_callee`); the callees
of `claim_list_digest` and `da_verify` all pass it (`cld_noAdvBut`, `dv_noAdvBut`).
-/

namespace LeanVM.Guest.B1.Main

open LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest

@[expose] public section

theorem exponent_tables_noAdv : NoAdvG "exponent_tables" := noAdvG_of_callee (j := idx% «main») (by decide +kernel)
theorem main_loop0_noAdv : NoAdvG name% «main_loop0» := noAdvG_of_callee (j := idx% «main») (by decide +kernel)
theorem main_loop1_noAdv : NoAdvG name% «main_loop1» := noAdvG_of_callee (j := idx% «main») (by decide +kernel)
theorem main_loop2_noAdv : NoAdvG name% «main_loop2» := noAdvG_of_callee (j := idx% «main») (by decide +kernel)
theorem main_loop3_noAdv : NoAdvG name% «main_loop3» := noAdvG_of_callee (j := idx% «main») (by decide +kernel)
theorem aggregate_claims_noAdv : NoAdvG "aggregate_claims" := noAdvG_of_callee (j := idx% «main») (by decide +kernel)
theorem statement_digest_noAdv : NoAdvG "statement_digest" := noAdvG_of_callee (j := idx% «main») (by decide +kernel)
theorem cc_noAdv : NoAdvG "child_claim_list_digest" := noAdvG_of_callee (j := idx% «main_loop4») (by decide +kernel)

theorem cld_name : (coreProgram[idx% «claim_list_digest»]?).map Fn.name = some "claim_list_digest" := by
  decide +kernel
theorem dv_name : (coreProgram[idx% «da_verify»]?).map Fn.name = some "da_verify" := by decide +kernel

theorem cld_noAdvBut : noAdvBut 16 idx% «claim_list_digest» [] = true := by decide +kernel
theorem dv_noAdvBut : noAdvBut 16 idx% «da_verify» [] = true := by decide +kernel

end

end LeanVM.Guest.B1.Main
