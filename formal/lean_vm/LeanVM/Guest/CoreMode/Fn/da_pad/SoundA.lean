/-
  LeanVM.Guest.CoreMode.Fn.da_pad.SoundA

  `da_pad`'s own family, sound at the honest instances of b2c's aligned tree (`OwnOkA`): its gap.
-/

module

public import LeanVM.Guest.EndExecCoreResA
public import LeanVM.Guest.CoreMode.Fn.da_pad.EndExecCoreDaA
public import LeanVM.Guest.CoreMode.Fn.da_pad.Fam

namespace LeanVM.Guest.EndExec

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Memory
open LeanVM.Guest.CoreMode (CRes capE)

public section

variable {al : String → Bool} {D : Ref → RefD} {r : Ref}

/-- **`da_pad`'s gap holds** at an honest instance (`daPadGap`): `DaPadQ`. -/
theorem daPadGap_instA (hR : RefH (layB al) (D r) r) (hr : r.Ok) {I : Inst} (hI : I ∈ instsR al D r)
    {f : String} {σ : Val} {bufs : List ℕ} {kids : List Tree} (ht : I.t = .node f σ bufs kids) {fn : Fn}
    (hf : coreProgram.find? f = some fn) : ∀ x : CRes, CoreMode.daPadGap fn x = true → x.Holds σ
  | .under _ r', h => fun _ ↦ daPadGap_instA hR hr hI ht hf r' h
  | .lt a (.num m), h => by
    simp only [CoreMode.daPadGap, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
    obtain ⟨⟨⟨hm, hn⟩, rfl⟩, hmr⟩ := h
    have hf' : f = name% «da_pad» := by rw [← find_name' hf, hn]
    subst hf'
    obtain ⟨k, hk, e2⟩ := daPadQ_allA hR hr I hI σ bufs kids ht
    exact ltF_of_pow (e := k) hm (by omega) (by rw [e2, Value.gen_pow_eq_ofK])
  | .lt _ (.val _), h | .lt _ (.mono _), h | .nz _, h | .subR _ _, h | .subP _ _, h | .sub _ _, h | .eq _ _, h => by
    simp [CoreMode.daPadGap] at h

end

end LeanVM.Guest.EndExec

namespace LeanVM.Guest.CoreMode.Own.da_pad

open LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.EndExec

public section

/-- **Its family**, aligned. -/
theorem fams_okA {al : String → Bool} {D : Ref → RefD} : ∀ c ∈ fams, OwnOkA al D c := by
  simp only [fams, List.mem_cons, List.not_mem_nil, or_false, forall_eq]
  exact fun hR hr I hI σ bufs kids ht fn hf x h ↦ daPadGap_instA hR hr hI ht hf x h

end

end LeanVM.Guest.CoreMode.Own.da_pad
