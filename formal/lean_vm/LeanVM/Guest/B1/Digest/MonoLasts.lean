/-
  LeanVM.Guest.B1.Digest.MonoLasts

  The bodies of `child_claim_list_mono_last__L{k}`, `k ≤ 16`, checked one kernel check each.
-/

module

public import LeanVM.Guest.B1.Digest.MonoDefs

namespace LeanVM.Guest.B1.Digest

open LeanVM.Guest.Core

@[expose] public section

set_option maxRecDepth 100000 in
theorem ml_0 : mlOk 0 (coreProgram.getD 364 default) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem ml_1 : mlOk 1 (coreProgram.getD 365 default) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem ml_2 : mlOk 2 (coreProgram.getD 366 default) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem ml_3 : mlOk 3 (coreProgram.getD 367 default) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem ml_4 : mlOk 4 (coreProgram.getD 368 default) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem ml_5 : mlOk 5 (coreProgram.getD 369 default) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem ml_6 : mlOk 6 (coreProgram.getD 370 default) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem ml_7 : mlOk 7 (coreProgram.getD 371 default) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem ml_8 : mlOk 8 (coreProgram.getD 372 default) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem ml_9 : mlOk 9 (coreProgram.getD 373 default) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem ml_10 : mlOk 10 (coreProgram.getD 374 default) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem ml_11 : mlOk 11 (coreProgram.getD 375 default) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem ml_12 : mlOk 12 (coreProgram.getD 376 default) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem ml_13 : mlOk 13 (coreProgram.getD 377 default) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem ml_14 : mlOk 14 (coreProgram.getD 378 default) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem ml_15 : mlOk 15 (coreProgram.getD 379 default) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem ml_16 : mlOk 16 (coreProgram.getD 380 default) = true := by decide +kernel

theorem ml_all : ∀ k < 17, mlOk k (coreProgram.getD (370 + k) default) = true := by
  intro k hk
  interval_cases k
  exacts [ml_0, ml_1, ml_2, ml_3, ml_4, ml_5, ml_6, ml_7, ml_8, ml_9, ml_10, ml_11, ml_12, ml_13,
    ml_14, ml_15, ml_16]

set_option maxRecDepth 100000 in
theorem ml_idx : ∀ k < 17, coreProgram.indexOf? (mlNames.getD k "") = some (370 + k) := by
  decide +kernel

end
end LeanVM.Guest.B1.Digest
