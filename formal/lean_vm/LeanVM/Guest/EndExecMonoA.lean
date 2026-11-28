/-
  LeanVM.Guest.EndExecMonoA

  `child_claim_list_mono`'s ghost families, sound at the honest instances of b2c's aligned tree: its frame
  loops' (`cm`) and its last claims' (`ml`) reads and links, from the gap walk (`mono_ok`).
-/

module

public import LeanVM.Guest.EndExecCoreGhost
public import LeanVM.Guest.CoreMode.Fn.child_claim_list_mono.EndExecCoreMono
public import LeanVM.Guest.CoreMode.Gen.MonoWalkOk

/-!
# The gap walk's ghost families, aligned

The bus era's `Fn/child_claim_list_mono/Sound.lean` and `Fn/child_claim_list_mono_last/Sound.lean` on
`honestInstsA`: `cmLoops_okA` (`cm_inst`, `cmGlF`) and `mlLoops_okA` (`ml_inst`, `mlGlF`), the
registry's (`FnReg.cmLoops`, `FnReg.mlLoops`) ghost families' soundness (`CmLoopOkA`, `MlLoopOkA`).
-/

namespace LeanVM.Guest.EndExec

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Memory

public section

variable {al : String → Bool} {D : Ref → RefD}

/-- **The frame loops' reads and links** (the gap walk, `mono_ok`). -/
theorem cmLoops_okA : ∀ c ∈ CoreMode.FnReg.cmLoops, CmLoopOkA al D c := by
  intro c _ r hR hr I hI σ bufs kids ht fn hf hk hdr
  obtain ⟨a, ha, ha5, hsub⟩ := cm_inst hR hr mono_ok hI ht hf hk
  exact ⟨_, hsub, fun Cf hCf hgl hgh ↦ by subst hCf; exact cmGlF hk hgl hgh (rd_hdr hdr ha) ha5⟩

/-- **The ghost family's reads and links** (the gap walk, `mono_ok`). -/
theorem mlLoops_okA : ∀ c ∈ CoreMode.FnReg.mlLoops, MlLoopOkA al D c := by
  intro c _ r hR hr I hI σ bufs kids ht fn hf hk hdr
  obtain ⟨hpar4, a, ha, h5, hm5, hsub⟩ := ml_inst hR hr mono_ok hI ht hf hk
  exact ⟨_, hsub, fun Cf hCf hgl hgh ↦ by subst hCf; exact mlGlF hk hgl hgh hpar4 (rd_hdr hdr ha) h5 hm5⟩

end

end LeanVM.Guest.EndExec
