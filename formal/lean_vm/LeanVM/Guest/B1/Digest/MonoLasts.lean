/-
  LeanVM.Guest.B1.Digest.MonoLasts

  The bodies of `child_claim_list_mono_last__L{k}`, `k ≤ 16`, checked by the kernel one at a time.
-/

module

public import LeanVM.Guest.B1.Digest.MonoDefs
import LeanVM.Guest.B1.Common.Find

namespace LeanVM.Guest.B1.Digest

open LeanVM.Guest.Core

@[expose] public section

theorem ml_all : ∀ k < 17, mlOk k (coreProgram.getD (idx% «child_claim_list_mono_last__L0» + k)
    default) = true := by
  intro k hk
  interval_cases k <;> decide +kernel

theorem ml_idx : ∀ k < 17, coreProgram.indexOf? (mlNames.getD k "") = some
    (idx% «child_claim_list_mono_last__L0» + k) :=
  coreProgram_indexOf?_run (by decide +kernel)

end
end LeanVM.Guest.B1.Digest
