/-
  LeanVM.Guest.CoreMode.Fn.child_claim_list_mono.Sound

  `child_claim_list_mono`'s own routing facts and families, sound (`CoreMode/FnReg.lean`): its frame loops.
-/

module

public import LeanVM.Guest.EndExecCoreFn
public import LeanVM.Guest.CoreMode.Fn.child_claim_list_mono.EndExecCoreMono
public import LeanVM.Guest.CoreMode.Gen.MonoWalkOk
public import LeanVM.Guest.CoreMode.Fn.child_claim_list_mono.Data

namespace LeanVM.Guest.CoreMode.Own.child_claim_list_mono

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.EndExec

public section

/-- **Its frame loops' reads and links** (the gap walk, `mono_ok`). -/
theorem cmLoops_ok : ∀ c ∈ cmLoops, CmLoopOk c := by
  intro c _ r hr I hI σ bufs kids ht fn hf hk hdr
  obtain ⟨a, ha, ha5, hsub⟩ := cm_inst hr mono_ok hI ht hf hk
  exact ⟨_, hsub, fun Cf hCf hgl hgh ↦ by subst hCf; exact cmGlF hk hgl hgh (rd_hdr hdr ha) ha5⟩

end

end LeanVM.Guest.CoreMode.Own.child_claim_list_mono
