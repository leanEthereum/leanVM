/-
  LeanVM.Guest.B1.KeccakGkr.VkCW

  `verify_keccak` complete, placed, within a bound.
-/

module

public import LeanVM.Guest.B1.KeccakGkr.VkCV
public import LeanVM.Guest.B1.KeccakGkr.VkKidsBW

/-!
# `verify_keccak` within its words

`VkCompleteAtBK fs cert κ Bvk`: `verify_keccak`'s completeness (`VkCV`) by trees of at most `Bvk` words.
At the deployed frame sizes `B2C.fs` the bound is
`vkBound = B2C.fs "verify_keccak" + 440 + 52659`: the frame, the seven buffers (`τ + 412`
words, `τ ≤ 28`) and the callees (`kidsB_fs_le`), by `completeAt_flatGB` on the same
obligations as the unbounded form (`vk_obl`).
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Guest.Memory LeanVM.Guest.B1.Fwd
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Protocol.KeccakGkr

@[expose] public section

/-- **`verify_keccak`, placed, within `Bvk` words.** -/
def VkCompleteAtBK (fs : String → ℕ) (cert : String → V → ℕ) (κ Bvk : ℕ) : Prop :=
  ∀ (τ : ℕ) (f chis outs xs op point slices : List E) (word : E) (s' : Fs)
    (curE chiE olE zvE slE tbE stE : ℕ), 9 ≤ τ → τ ≤ 28 → τ ≤ chis.length → outs.length = 25 →
    f.length = 5 → (∃ sp, (⟨f, []⟩ : Fs).Carries sp) →
    RunsTo (verifyKeccak τ (chis.take τ) outs) ⟨f, []⟩ xs ([⟨qkeccak, op, word⟩], point, slices) s' →
    CompleteAtB fs cert κ "verify_keccak"
      [(curE, xs), (chiE, chis), (olE, outs), (zvE, op), (zvE + qkeccakVarsCap, point),
        (slE, slices), (tbE, winTabWords)]
      (f ++ [ofK (Parameters.addressOfIndex curE), gen ^ τ, ofK (Parameters.addressOfIndex chiE),
        ofK (Parameters.addressOfIndex olE), ofK (Parameters.addressOfIndex zvE),
        ofK (Parameters.addressOfIndex slE), ofK (Parameters.addressOfIndex tbE),
        ofK (Parameters.addressOfIndex stE)])
      (Returns (capOf s'.perm ++ [ofK (Parameters.addressOfIndex curE) * gen ^ xs.length, word]))
      Bvk

/-- `verify_keccak`'s words at `B2C.fs`. -/
noncomputable def vkBound : ℕ := LeanVM.Guest.B2C.fs "verify_keccak" + 440 + 52659

theorem VkData.sizes_sum {D : VkData} (h : D.Ok) : D.sizes.sum = D.τ + 412 := by
  have := h.1
  simp [VkData.sizes]
  omega

variable {cert : String → V → ℕ}

open VkData in
set_option maxRecDepth 20000 in

end
end LeanVM.Guest.B1.VerifySub
