/-
  LeanVM.Guest.B1.Digest.ChildListLasts

  The bodies of `child_claim_list_last__L{k}`, `k ≤ 16`, checked one kernel check each.
-/

module

public import LeanVM.Guest.B1.Digest.ChildListDefs

namespace LeanVM.Guest.B1.Digest

open LeanVM.Guest.Core

@[expose] public section

set_option maxRecDepth 100000 in
theorem ccl_0 : cclOk 0 (coreProgram.getD 344 default) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem ccl_1 : cclOk 1 (coreProgram.getD 345 default) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem ccl_2 : cclOk 2 (coreProgram.getD 346 default) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem ccl_3 : cclOk 3 (coreProgram.getD 347 default) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem ccl_4 : cclOk 4 (coreProgram.getD 348 default) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem ccl_5 : cclOk 5 (coreProgram.getD 349 default) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem ccl_6 : cclOk 6 (coreProgram.getD 350 default) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem ccl_7 : cclOk 7 (coreProgram.getD 351 default) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem ccl_8 : cclOk 8 (coreProgram.getD 352 default) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem ccl_9 : cclOk 9 (coreProgram.getD 353 default) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem ccl_10 : cclOk 10 (coreProgram.getD 354 default) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem ccl_11 : cclOk 11 (coreProgram.getD 355 default) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem ccl_12 : cclOk 12 (coreProgram.getD 356 default) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem ccl_13 : cclOk 13 (coreProgram.getD 357 default) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem ccl_14 : cclOk 14 (coreProgram.getD 358 default) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem ccl_15 : cclOk 15 (coreProgram.getD 359 default) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem ccl_16 : cclOk 16 (coreProgram.getD 360 default) = true := by decide +kernel

theorem ccl_all : ∀ k < 17, cclOk k (coreProgram.getD (344 + k) default) = true := by
  intro k hk
  interval_cases k
  exacts [ccl_0, ccl_1, ccl_2, ccl_3, ccl_4, ccl_5, ccl_6, ccl_7, ccl_8, ccl_9, ccl_10, ccl_11,
    ccl_12, ccl_13, ccl_14, ccl_15, ccl_16]

end
end LeanVM.Guest.B1.Digest
