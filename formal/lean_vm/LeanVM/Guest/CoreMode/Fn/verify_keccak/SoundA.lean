/-
  LeanVM.Guest.CoreMode.Fn.verify_keccak.SoundA

  `verify_keccak`'s own family, sound at the honest instances of b2c's aligned tree (`OwnOkA`): its exponent facts
  (`expFam_okA_of`) from the table height `verify_sub` carries (`vkQ_allA`), its equation residual (`ptEq_holds`), its runs (`runFam_holds`), its stream (`stFam_holds`).
-/

module

public import LeanVM.Guest.CoreMode.Fn.verify_keccak.Runs
public import LeanVM.Guest.CoreMode.Fn.verify_keccak.Stream
public import LeanVM.Guest.CoreMode.Fn.verify_sub.VkCarry

namespace LeanVM.Guest.CoreMode.Own.verify_keccak

open LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.EndExec
open LeanVM.Protocol.Verifier (keccakMinStepsLog)

public section

/-- **Its family** (`expFam_okA_of`, `vkQ_allA`), aligned. -/
theorem fams_okA {al : String → Bool} {D : Ref → RefD} : ∀ c ∈ fams, OwnOkA al D c := by
  intro c hc
  simp only [fams, List.mem_cons, List.not_mem_nil, or_false] at hc
  subst hc
  intro r hR hr I hI σ bufs kids ht fn hf x hx
  simp only [Bool.or_eq_true, decide_eq_true_eq] at hx
  rcases hx with ((hx | rfl) | hx) | hx
  · refine expFam_okA_of (fun hR hr J hJ σ bufs kids ht ↦ ?_) hR hr I hI σ bufs kids ht fn hf x hx
    obtain ⟨h, h1, h2, h3⟩ := vkQ_allA hR hr J hJ σ bufs kids ht
    exact ⟨h, by rw [show keccakMinStepsLog = 9 from rfl] at h1; exact h1, h2, h3⟩
  · exact ptEq_holds hR hI ht
  · obtain ⟨h, h1, h2, h3⟩ := vkQ_allA hR hr I hI σ bufs kids ht
    rw [show keccakMinStepsLog = 9 from rfl] at h1
    obtain ⟨hP, hS, hRm⟩ := vk_headWords hR hI ht h1 h2 h3
    exact runFam_holds h1 h2 h3 hP hS hRm hx
  · obtain ⟨h, h1, h2, h3⟩ := vkQ_allA hR hr I hI σ bufs kids ht
    rw [show keccakMinStepsLog = 9 from rfl] at h1
    exact stFam_holds h1 h2 (vk_stEx hR hI ht h1 h2 h3) hx

end

end LeanVM.Guest.CoreMode.Own.verify_keccak
