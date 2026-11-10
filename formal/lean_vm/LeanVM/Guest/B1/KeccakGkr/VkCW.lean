/-
  LeanVM.Guest.B1.KeccakGkr.VkCW

  `verify_keccak` complete, placed, within a bound (`verify_keccak_completeAtB_fs`).
-/

module

public import LeanVM.Guest.B1.KeccakGkr.VkCV
public import LeanVM.Guest.B1.KeccakGkr.VkKidsBW

/-!
# `verify_keccak` within its words

`VkCompleteAtBK fs cert κ Bvk`: `VkCompleteAtK` by trees of at most `Bvk` words.
`verify_keccak_completeAtB_fs`: it holds at the deployed frame sizes `B2C.fs` with
`vkBound = B2C.fs "verify_keccak" + 440 + 52647`: the frame, the seven buffers (`τ + 412`
words, `τ ≤ 28`) and the callees (`kidsB_fs_le`), by `completeAt_flatGB` on the same
obligations as the unbounded form (`vk_obl`).
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Guest.Memory LeanVM.Guest.B1.Fwd
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Protocol.KeccakGkr

@[expose] public section

/-- **`verify_keccak`, placed, within `Bvk` words** (`VkCompleteAtK` bounded). -/
def VkCompleteAtBK (fs : String → ℕ) (cert : String → V → ℕ) (κ Bvk : ℕ) : Prop :=
  ∀ (τ : ℕ) (f chis outs xs op point slices : List E) (word : E) (s' : Fs)
    (curE chiE olE zvE slE tbE : ℕ), 9 ≤ τ → τ ≤ 28 → τ ≤ chis.length → outs.length = 25 →
    f.length = 5 → (∃ sp, (⟨f, []⟩ : Fs).Carries sp) →
    RunsTo (verifyKeccak τ (chis.take τ) outs) ⟨f, []⟩ xs ([⟨qkeccak, op, word⟩], point, slices) s' →
    CompleteAtB fs cert κ "verify_keccak"
      [(curE, xs), (chiE, chis), (olE, outs), (zvE, op), (zvE + qkeccakVarsCap, point),
        (slE, slices), (tbE, winTabWords)]
      (f ++ [ofK (Parameters.addressOfIndex curE), gen ^ τ, ofK (Parameters.addressOfIndex chiE),
        ofK (Parameters.addressOfIndex olE), ofK (Parameters.addressOfIndex zvE),
        ofK (Parameters.addressOfIndex slE), ofK (Parameters.addressOfIndex tbE)])
      (Returns (capOf s'.perm ++ [ofK (Parameters.addressOfIndex curE) * gen ^ xs.length, word]))
      Bvk

/-- `verify_keccak`'s words at `B2C.fs`. -/
noncomputable def vkBound : ℕ := LeanVM.Guest.B2C.fs "verify_keccak" + 440 + 52647

theorem VkData.sizes_sum {D : VkData} (h : D.Ok) : D.sizes.sum = D.τ + 412 := by
  have := h.1
  simp [VkData.sizes]
  omega

variable {cert : String → V → ℕ}

open VkData in
set_option maxRecDepth 20000 in
/-- **`verify_keccak` is complete, placed, within `vkBound` words at `B2C.fs`.** -/
theorem verify_keccak_completeAtB_fs {κ : ℕ} (hκ : 11 ≤ κ) :
    VkCompleteAtBK LeanVM.Guest.B2C.fs cert κ vkBound := by
  intro τ f chis outs xs op point slices word s' curE chiE olE zvE slE tbE hτ1 hτ2 hchis houts
    hf hc hrun
  obtain ⟨D, rfl, rfl, rfl, rfl, rfl, rfl, h, rfl, rfl, rfl, rfl⟩ :=
    vkData_of_run hτ1 hτ2 hchis houts hf hc hrun
  refine CompleteAtB.mono (completeAt_flatGB (fs := LeanVM.Guest.B2C.fs) (cert := cert) find_vk
    vk_loop κ (D.lin curE chiE olE zvE slE tbE) (D.args curE chiE olE zvE slE tbE)
    (capOf D.sF.perm ++ [ptr curE * gen ^ D.xs.length, D.word]) (vk_body.trans vkT_pre)
    vkPre_kernel.1 vkPre_kernel.2.1 vk_noLoadIte D.sizes
    (fun fp fps ↦ D.own (fp + LeanVM.Guest.B2C.fs "verify_keccak") (D.lsOf LeanVM.Guest.B2C.fs fps))
    (fun fp fps ↦ own_fit h _ _)
    (fun fp ↦ D.kids LeanVM.Guest.B2C.fs (fp + LeanVM.Guest.B2C.fs "verify_keccak") curE chiE olE
      zvE slE tbE)
    (D.kidsB LeanVM.Guest.B2C.fs 17 374 77 250 178) 52647
    (fun fp ↦ kids_completeB_fs h hκ _ curE chiE olE zvE slE tbE)
    (fun fp ↦ (kids_boundB _ curE chiE olE zvE slE tbE 17 374 77 250 178).trans (kidsB_fs_le h).2)
    (fun fp fps outs hlen _ hout rd _ hB hLin hto ↦
      vk_obl h curE chiE olE zvE slE tbE fp fps outs hlen hout rd hB hLin hto)) le_rfl ?_
  show _ ≤ LeanVM.Guest.B2C.fs "verify_keccak" + 440 + 52647
  rw [sizes_sum h]
  have := h.2.1
  generalize LeanVM.Guest.B2C.fs "verify_keccak" = a
  omega

end
end LeanVM.Guest.B1.VerifySub
