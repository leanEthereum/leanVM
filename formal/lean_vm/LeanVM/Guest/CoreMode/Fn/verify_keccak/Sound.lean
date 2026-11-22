/-
  LeanVM.Guest.CoreMode.Fn.verify_keccak.Sound

  `verify_keccak`'s own routing facts and families, sound (`CoreMode/FnReg.lean`): its family.
-/

module

public import LeanVM.Guest.EndExecCoreRes
public import LeanVM.Guest.CoreMode.Fn.verify_keccak.EndExecCoreVk
public import LeanVM.Guest.CoreMode.Fn.verify_keccak.Fam

namespace LeanVM.Guest.CoreMode.Own.verify_keccak

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.EndExec
open LeanVM.Protocol.Verifier (gen)

public section

/-- **Its family** (`vkQC_inst`). -/
theorem fams_ok : ∀ c ∈ fams, OwnOk c := by
  simp only [fams, List.mem_cons, List.not_mem_nil, or_false, forall_eq]
  exact fun hr I hI σ bufs kids ht fn hf x h ↦ vkQC_inst hr hI ht hf x h

end

end LeanVM.Guest.CoreMode.Own.verify_keccak
