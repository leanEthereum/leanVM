/-
  LeanVM.Guest.B1.KeccakGkr.VkCWE

  `verify_keccak` complete, placed, within its bound, by a tree exact at every node (`VkCompleteAtBKE`).
-/

module

public import LeanVM.Guest.B1.KeccakGkr.VkCW
public import LeanVM.Guest.B1.KeccakGkr.LayerCPlacedBE
public import LeanVM.Guest.B1.VerifySub.CompleteBTE

/-!
# `verify_keccak`, exact

`kids_completeBE_fs`: `kids_completeB_fs` by trees exact at every node: the layers by `layer_completeAtFBE`, the copy
loops and the plain rounds exact for free. `verify_keccak_completeAtBE_fs`: `verify_keccak_completeAtB_fs` by such a
tree (`completeAt_flatGBE`, `verify_keccak`'s paths exact by `vk_pathExact`), so `VkCompleteAtBKE` holds at
`B2C.fs` and `vkBound`.
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Guest.Memory LeanVM.Guest.B1.Fwd
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Protocol.KeccakGkr

@[expose] public section

namespace VkData

variable {D : VkData} {cert : String → V → ℕ}

/-- **`verify_keccak`'s calls, complete where it places them, within their words at `B2C.fs`, by trees exact at
every node.** -/
theorem kids_completeBE_fs (h : D.Ok) {κ : ℕ} (hκ : 11 ≤ κ) (B curE chiE olE zvE slE tbE stE : ℕ) :
    KidsGBT LeanVM.Guest.B2C.fs cert κ exT (D.kids LeanVM.Guest.B2C.fs B curE chiE olE zvE slE tbE stE)
      (D.kidsB LeanVM.Guest.B2C.fs 17 374 77 201 145) := by
  have hG := kidsGB_zip (kids_completeB_fs (cert := cert) h hκ B curE chiE olE zvE slE tbE stE)
  have hτ1 := h.1
  have hτ2 := h.2.1
  refine kidsGBT_of_zip (by simp [kids, kidsB]) fun kb hkb ht ps ↦ ?_
  have hG' := hG kb hkb ht ps
  rw [kids, kidsB, List.zip_append (by simp), List.zip_append (by simp), List.zip_map'] at hkb
  simp only [List.zip_cons_cons, List.zip_nil_right, List.mem_append, List.mem_cons,
    List.mem_map, List.mem_range, List.not_mem_nil, or_false] at hkb
  rcases hkb with ((rfl | ⟨s, hs, rfl⟩) | rfl | rfl | rfl | rfl | rfl)
  · exact hG'.toFBE (.free vk_loop0_exactFree)
  · -- the layers
    have hy := D.layer_y h (k := s) (by omega)
    have hcl := D.layer_cap h hs
    obtain ⟨hpl, hgr, hpm, hlm, hproj, hfin⟩ := D.layer_facts h hs
    have hf2 : firstOf s < 2 := by unfold firstOf; split <;> omega
    have H := layer_completeAtFBE (fs := LeanVM.Guest.B2C.fs) (cert := cert) (first := firstOf s)
      hf2 hκ (D.layer s)
      (D.CL B (D.lsOf LeanVM.Guest.B2C.fs ps) s) (curE + D.lcur s) (B + D.o201 + 22 * (s + 1)) tbE
      (p0 := (D.cells s).1) (p1 := (D.cells s).2) (st := ptr stE) (packLoop_totalLeOn_fs hf2) (remLoop_totalLeOn_fs hf2) hcl
      (fun hf1 ↦ by
        obtain rfl : s = 0 := by unfold firstOf at hf1; split at hf1 <;> omega
        rfl) (by rw [hy]; omega) (by rw [hy]; omega) hpl hpm hlm hproj hgr hfin
      (D.CL_ok h B _ (by omega)) B2C.fs_tailKey_le
    have hb : (D.CL B (D.lsOf LeanVM.Guest.B2C.fs ps) s).bclaim = B + D.o201 + 22 * s := by cases s <;> rfl
    rw [hb] at H
    simp only [layKid, List.dropLast_concat, List.getLast?_concat, Option.getD_some]
    exact H
  · exact hG'.toFBE (.free plain0_exactFree)
  · exact hG'.toFBE (.free vk_loop1_exactFree)
  · exact hG'.toFBE (.free plain1_exactFree)
  · exact hG'.toFBE (.free plain0_exactFree)
  · exact hG'.toFBE (.free vk_loop2_exactFree)

end VkData

variable {cert : String → V → ℕ}

open VkData in
/-- **`verify_keccak` is complete, placed, within `vkBound` words at `B2C.fs`, by a tree exact at every node.** -/
theorem verify_keccak_completeAtBE_fs {κ : ℕ} (hκ : 11 ≤ κ) :
    VkCompleteAtBKE LeanVM.Guest.B2C.fs cert κ vkBound := by
  intro τ f chis outs xs op point slices word s' curE chiE olE zvE slE tbE stE hτ1 hτ2 hchis houts
    hf hc hrun
  obtain ⟨D, rfl, rfl, rfl, rfl, rfl, rfl, h, rfl, rfl, rfl, rfl⟩ :=
    vkData_of_run hτ1 hτ2 hchis houts hf hc hrun
  refine (completeAt_flatGBE (fs := LeanVM.Guest.B2C.fs) (cert := cert) find_vk vk_loop vk_pathExact κ
    (D.lin curE chiE olE zvE slE tbE) (D.args curE chiE olE zvE slE tbE stE)
    (capOf D.sF.perm ++ [ptr curE * gen ^ D.xs.length, D.word]) (vk_body.trans vkT_pre)
    vkPre_kernel.1 vkPre_kernel.2.1 vk_noLoadIte D.sizes
    (fun fp fps ↦ D.own (fp + LeanVM.Guest.B2C.fs "verify_keccak") (D.lsOf LeanVM.Guest.B2C.fs fps))
    (fun fp fps ↦ own_fit h _ _)
    (fun fp ↦ D.kids LeanVM.Guest.B2C.fs (fp + LeanVM.Guest.B2C.fs "verify_keccak") curE chiE olE
      zvE slE tbE stE)
    (D.kidsB LeanVM.Guest.B2C.fs 17 374 77 201 145) 52659
    (fun fp ↦ kids_completeBE_fs h hκ _ curE chiE olE zvE slE tbE stE)
    (fun fp ↦ (kids_boundB _ curE chiE olE zvE slE tbE stE 17 374 77 201 145).trans (kidsB_fs_le h).2)
    (fun fp fps outs hlen _ hout rd _ hB hLin hto ↦
      vk_obl h curE chiE olE zvE slE tbE stE fp fps outs hlen hout rd hB hLin hto)).mono ?_ fun _ _ h ↦ h
  show _ ≤ LeanVM.Guest.B2C.fs "verify_keccak" + 440 + 52659
  rw [sizes_sum h]
  have := h.2.1
  generalize LeanVM.Guest.B2C.fs "verify_keccak" = a
  omega

end
end LeanVM.Guest.B1.VerifySub
