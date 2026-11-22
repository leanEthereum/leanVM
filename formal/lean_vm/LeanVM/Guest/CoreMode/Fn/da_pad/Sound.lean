/-
  LeanVM.Guest.CoreMode.Fn.da_pad.Sound

  `da_pad`'s own routing facts and families, sound (`CoreMode/FnReg.lean`): its gap.
-/

module

public import LeanVM.Guest.EndExecCoreRes
public import LeanVM.Guest.CoreMode.Fn.da_pad.EndExecCoreDa
public import LeanVM.Guest.CoreMode.Fn.da_pad.Fam

namespace LeanVM.Guest.EndExec

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Memory
open LeanVM.Guest.CoreMode (CFun CRes CIdx ResF LtF rep_of capE resFam idxC baseC vw csSub)

public section

/-- **`da_pad`'s gap holds** at an honest instance (`daPadGap`): `DaPadQ`. -/
theorem daPadGap_inst {r : Ref} (hr : r.Ok) {I : Inst} (hI : I ∈ honestInsts coreProgram B2C.fs B2C.H r.hdr r.T)
    {f : String} {σ : Val} {bufs : List ℕ} {kids : List Tree} (ht : I.t = .node f σ bufs kids) {fn : Fn}
    (hf : coreProgram.find? f = some fn) : ∀ x : CRes, CoreMode.daPadGap fn x = true → x.Holds σ
  | .under gs r', h => fun _ ↦ daPadGap_inst hr hI ht hf r' h
  | .lt a (.num m), h => by
    simp only [CoreMode.daPadGap, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
    obtain ⟨⟨⟨hm, hn⟩, rfl⟩, hmr⟩ := h
    have hf' : f = name% «da_pad» := by rw [← find_name' hf, hn]
    subst hf'
    obtain ⟨k, hk, e2⟩ := daPadQ_all hr I hI σ bufs kids ht
    exact ltF_of_pow (e := k) hm (by omega) (by rw [e2, Value.gen_pow_eq_ofK])
  | .lt _ (.val _), h | .lt _ (.mono _), h | .nz _, h | .subR _ _, h | .subP _ _, h | .sub _ _, h => by
    simp [CoreMode.daPadGap] at h

end

end LeanVM.Guest.EndExec

namespace LeanVM.Guest.CoreMode.Own.da_pad

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.EndExec
open LeanVM.Protocol.Verifier (gen)

public section

/-- **Its family.** -/
theorem fams_ok : ∀ c ∈ fams, OwnOk c := by
  simp only [fams, List.mem_cons, List.not_mem_nil, or_false, forall_eq]
  exact fun hr I hI σ bufs kids ht fn hf x h ↦ daPadGap_inst hr hI ht hf x h

end

end LeanVM.Guest.CoreMode.Own.da_pad
