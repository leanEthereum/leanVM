/-
  LeanVM.Guest.CoreMode.Fn.da_verify.Sound

  `da_verify`'s own routing facts and families, sound (`CoreMode/FnReg.lean`): its blob count and gap.
-/

module

public import LeanVM.Guest.EndExecCoreRes
public import LeanVM.Guest.CoreMode.Fn.da_pad.EndExecCoreDa
import LeanVM.Guest.Data.Consts
public import LeanVM.Guest.CoreMode.Fn.da_verify.Fam

namespace LeanVM.Guest.EndExec

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Memory
open LeanVM.Guest.CoreMode (CFun CRes CIdx ResF LtF rep_of capE resFam idxC baseC vw csSub)

public section

/-- **`da_verify`'s blob count and gap hold** at an honest instance (`daVerifyGap`): `daV_inst`. -/
theorem daVerifyGap_inst {r : Ref} (hr : r.Ok) {I : Inst} (hI : I ∈ honestInsts coreProgram B2C.fs B2C.H r.hdr r.T)
    {f : String} {σ : Val} {bufs : List ℕ} {kids : List Tree} (ht : I.t = .node f σ bufs kids) {fn : Fn}
    (hf : coreProgram.find? f = some fn) : ∀ x : CRes, CoreMode.daVerifyGap fn x = true → x.Holds σ
  | .under gs r', h => fun _ ↦ daVerifyGap_inst hr hI ht hf r' h
  | .lt a (.num m), h => by
    simp only [CoreMode.daVerifyGap, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq] at h
    obtain ⟨⟨hm, hn⟩, ⟨rfl, hmr⟩ | ⟨rfl, hmr⟩⟩ := h
    · have hf' : f = name% «da_verify» := by rw [← find_name' hf, hn]
      subst hf'
      obtain ⟨n, -, hn32, e1, -⟩ := daV_inst hr hI ht
      exact ltF_of_pow (e := n) hm (by omega) (by rw [e1, Value.gen_pow_eq_ofK])
    · have hf' : f = name% «da_verify» := by rw [← find_name' hf, hn]
      subst hf'
      obtain ⟨n, hn1, -, -, e2⟩ := daV_inst hr hI ht
      exact ltF_of_pow (e := guest_const% DA_MAX_ROWS - n) hm (by omega) (by rw [e2, Value.gen_pow_eq_ofK])
  | .lt _ (.val _), h | .lt _ (.mono _), h | .nz _, h | .subR _ _, h | .subP _ _, h | .sub _ _, h => by
    simp [CoreMode.daVerifyGap] at h

end

end LeanVM.Guest.EndExec

namespace LeanVM.Guest.CoreMode.Own.da_verify

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.EndExec
open LeanVM.Protocol.Verifier (gen)

public section

/-- **Its family.** -/
theorem fams_ok : ∀ c ∈ fams, OwnOk c := by
  simp only [fams, List.mem_cons, List.not_mem_nil, or_false, forall_eq]
  exact fun hr I hI σ bufs kids ht fn hf x h ↦ daVerifyGap_inst hr hI ht hf x h

end

end LeanVM.Guest.CoreMode.Own.da_verify
