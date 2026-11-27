/-
  LeanVM.Guest.B1.Digest.ChildListLasts

  The bodies of `child_claim_list_last__L{k}`, `k ≤ 16`, checked by the kernel one at a time.
-/

module

public import LeanVM.Guest.B1.Digest.ChildListDefs

namespace LeanVM.Guest.B1.Digest

open LeanVM.Guest.Core

@[expose] public section

theorem ccl_all : ∀ k < 17, cclOk k (coreProgram.getD (idx% «child_claim_list_last__L0» + k)
    default) = true := by
  intro k hk
  interval_cases k <;> decide +kernel

end
end LeanVM.Guest.B1.Digest
