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
theorem ml_0 : mlOk 0 (coreProgram.getD idx% «child_claim_list_mono_last__L0» default) = true :=
  by decide +kernel

set_option maxRecDepth 100000 in
theorem ml_1 : mlOk 1 (coreProgram.getD idx% «child_claim_list_mono_last__L1» default) = true :=
  by decide +kernel

set_option maxRecDepth 100000 in
theorem ml_2 : mlOk 2 (coreProgram.getD idx% «child_claim_list_mono_last__L2» default) = true :=
  by decide +kernel

set_option maxRecDepth 100000 in
theorem ml_3 : mlOk 3 (coreProgram.getD idx% «child_claim_list_mono_last__L3» default) = true :=
  by decide +kernel

set_option maxRecDepth 100000 in
theorem ml_4 : mlOk 4 (coreProgram.getD idx% «child_claim_list_mono_last__L4» default) = true :=
  by decide +kernel

set_option maxRecDepth 100000 in
theorem ml_5 : mlOk 5 (coreProgram.getD idx% «child_claim_list_mono_last__L5» default) = true :=
  by decide +kernel

set_option maxRecDepth 100000 in
theorem ml_6 : mlOk 6 (coreProgram.getD idx% «child_claim_list_mono_last__L6» default) = true :=
  by decide +kernel

set_option maxRecDepth 100000 in
theorem ml_7 : mlOk 7 (coreProgram.getD idx% «child_claim_list_mono_last__L7» default) = true :=
  by decide +kernel

set_option maxRecDepth 100000 in
theorem ml_8 : mlOk 8 (coreProgram.getD idx% «child_claim_list_mono_last__L8» default) = true :=
  by decide +kernel

set_option maxRecDepth 100000 in
theorem ml_9 : mlOk 9 (coreProgram.getD idx% «child_claim_list_mono_last__L9» default) = true :=
  by decide +kernel

set_option maxRecDepth 100000 in
theorem ml_10 : mlOk 10 (coreProgram.getD idx% «child_claim_list_mono_last__L10» default) = true :=
  by decide +kernel

set_option maxRecDepth 100000 in
theorem ml_11 : mlOk 11 (coreProgram.getD idx% «child_claim_list_mono_last__L11» default) = true :=
  by decide +kernel

set_option maxRecDepth 100000 in
theorem ml_12 : mlOk 12 (coreProgram.getD idx% «child_claim_list_mono_last__L12» default) = true :=
  by decide +kernel

set_option maxRecDepth 100000 in
theorem ml_13 : mlOk 13 (coreProgram.getD idx% «child_claim_list_mono_last__L13» default) = true :=
  by decide +kernel

set_option maxRecDepth 100000 in
theorem ml_14 : mlOk 14 (coreProgram.getD idx% «child_claim_list_mono_last__L14» default) = true :=
  by decide +kernel

set_option maxRecDepth 100000 in
theorem ml_15 : mlOk 15 (coreProgram.getD idx% «child_claim_list_mono_last__L15» default) = true :=
  by decide +kernel

set_option maxRecDepth 100000 in
theorem ml_16 : mlOk 16 (coreProgram.getD idx% «child_claim_list_mono_last__L16» default) = true :=
  by decide +kernel

theorem ml_all : ∀ k < 17, mlOk k (coreProgram.getD (idx% «child_claim_list_mono_last__L0» + k)
    default) = true := by
  intro k hk
  interval_cases k
  exacts [ml_0, ml_1, ml_2, ml_3, ml_4, ml_5, ml_6, ml_7, ml_8, ml_9, ml_10, ml_11, ml_12, ml_13,
    ml_14, ml_15, ml_16]

set_option maxRecDepth 100000 in
theorem ml_idx : ∀ k < 17, coreProgram.indexOf? (mlNames.getD k "") = some
    (idx% «child_claim_list_mono_last__L0» + k) :=
  coreProgram_indexOf?_run (by decide +kernel)

end
end LeanVM.Guest.B1.Digest
