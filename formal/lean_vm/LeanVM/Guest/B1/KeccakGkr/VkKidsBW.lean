/-
  LeanVM.Guest.B1.KeccakGkr.VkKidsBW

  `kids_completeB` at the deployed frame sizes (`B2C.fs`): the callees' words from their words
  certificates, the bound in numbers.
-/

module

public import LeanVM.Guest.B1.KeccakGkr.VkKidsB
public import LeanVM.Guest.B1.KeccakGkr.LayerCPlacedBW

/-!
# `verify_keccak`'s callees within their words at `B2C.fs`

The words certificates (`Count.Words`) give, at the deployed frame sizes: the copy loops
`__loop10`, `__loop11`, `__loop12` (cores `262`, `266`, `268`, frames `17`) at most `17` words per
iteration and their runs' one phantom frame; `keccak_plain_rounds__L6_L0` (core `265`,
`plainName 0`) at most `250`, `keccak_plain_rounds__L4_L1` (core `267`, `plainName 1`) at most
`178`; the layers' eight-round loops `374` per iteration and remainder loops `77`, and their frames
(`LayerCPlacedBW`). So `verify_keccak`'s callees are complete within
`D.kidsB B2C.fs 17 374 77 250 178` (`kids_completeB_fs`), whose sum is at most
`3 * ((τ - 4) * 17) + 51 + 678 + 12 * (2241 + (y + 171) + (374 + y / 8 * 374) + (77 + y % 8 * 77) + 60)`
(`y = τ - 3`), at most `52647` words for `τ ≤ 28` (`kidsB_fs_le`).
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Guest.Memory LeanVM.Guest.Count
open LeanVM.Protocol LeanVM.Protocol.KeccakGkr

@[expose] public section

/-- **The copy loops' runs' words at `B2C.fs`**: at most `17` per iteration and their frame. -/
theorem copyLoop_totalLeOn_fs : ∀ name ∈ ["__loop10", "__loop11", "__loop12"],
    TotalLeOn coreProgram LeanVM.Guest.B2C.fs name LoopPre
      fun a ↦ logG (a.getD 1 0) * 17 + LeanVM.Guest.B2C.fs name := by
  intro name hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with rfl | rfl | rfl
  · exact loop_totalLeOn_at (j := 263) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact loop_totalLeOn_at (j := 267) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact loop_totalLeOn_at (j := 269) (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- **`keccak_plain_rounds__L6_L0`'s words at `B2C.fs`**: `250`. -/
theorem plain0_totalLe_fs :
    TotalLe coreProgram LeanVM.Guest.B2C.fs (plainName 0) fun _ ↦ 250 := by
  have h1 := wSB_totalLe (j := 266) (f := "keccak_plain_rounds__L6_L0") (by decide +kernel)
  rwa [wSB_idx (j := 266) (f := "keccak_plain_rounds__L6_L0") (by decide +kernel),
    show wSBJ 266 = 250 by decide +kernel] at h1

/-- **`keccak_plain_rounds__L4_L1`'s words at `B2C.fs`**: `178`. -/
theorem plain1_totalLe_fs :
    TotalLe coreProgram LeanVM.Guest.B2C.fs (plainName 1) fun _ ↦ 178 := by
  have h1 := wSB_totalLe (j := 268) (f := "keccak_plain_rounds__L4_L1") (by decide +kernel)
  rwa [wSB_idx (j := 268) (f := "keccak_plain_rounds__L4_L1") (by decide +kernel),
    show wSBJ 268 = 178 by decide +kernel] at h1

namespace VkData

variable {D : VkData} {cert : String → V → ℕ}

/-- **`verify_keccak`'s calls, complete where it places them, within their words at `B2C.fs`.** -/
theorem kids_completeB_fs (h : D.Ok) {κ : ℕ} (hκ : 11 ≤ κ) (B curE chiE olE zvE slE tbE : ℕ) :
    KidsGB LeanVM.Guest.B2C.fs cert κ (D.kids LeanVM.Guest.B2C.fs B curE chiE olE zvE slE tbE)
      (D.kidsB LeanVM.Guest.B2C.fs 17 374 77 250 178) :=
  kids_completeB h hκ B curE chiE olE zvE slE tbE copyLoop_totalLeOn_fs
    (fun _ hf ↦ packLoop_totalLeOn_fs hf) (fun _ hf ↦ remLoop_totalLeOn_fs hf)
    plain0_totalLe_fs plain1_totalLe_fs

/-- **The callees' words at `B2C.fs`, in numbers**: the copy loops `(τ - 4) * 17 + 17` each, the
openings' rounds `250 + 178 + 250`, each layer (`y = τ - 3`) at most
`2241 + (y + 171) + (374 + y / 8 * 374) + (77 + y % 8 * 77) + 60`; at most `52647` (`τ ≤ 28`, the
largest at `y = 23`). -/
theorem kidsB_fs_le (h : D.Ok) :
    (D.kidsB LeanVM.Guest.B2C.fs 17 374 77 250 178).sum ≤
      3 * ((D.τ - 4) * 17) + 51 + 678 + 12 * (2241 + (D.τ - 3 + 171) + (374 + (D.τ - 3) / 8 * 374) +
        (77 + (D.τ - 3) % 8 * 77) + 60) ∧
    (D.kidsB LeanVM.Guest.B2C.fs 17 374 77 250 178).sum ≤ 52647 := by
  have hτ := h.2.1
  have hτ1 := h.1
  have hL : ((List.range 12).map (fun s ↦ layerWords LeanVM.Guest.B2C.fs (firstOf s)
      (D.layer s).y 374 77)).sum ≤
      12 * (2241 + (D.τ - 3 + 171) + (374 + (D.τ - 3) / 8 * 374) + (77 + (D.τ - 3) % 8 * 77) + 60) := by
    have := List.sum_le_length_nsmul ((List.range 12).map (fun s ↦ layerWords
      LeanVM.Guest.B2C.fs (firstOf s) (D.layer s).y 374 77))
      (2241 + (D.τ - 3 + 171) + (374 + (D.τ - 3) / 8 * 374) + (77 + (D.τ - 3) % 8 * 77) + 60)
      (fun x hx ↦ ?_)
    · simpa using this
    obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hx
    have hs' := List.mem_range.mp hs
    rw [D.layer_y h (by omega)]
    exact layerWords_fs_le_y (by unfold firstOf; split <;> omega) _
  have hF : LeanVM.Guest.B2C.fs "__loop10" + LeanVM.Guest.B2C.fs "__loop11" +
      LeanVM.Guest.B2C.fs "__loop12" = 51 := by
    rw [fs_idx (j := 263) (f := "__loop10") (by decide +kernel),
      fs_idx (j := 267) (f := "__loop11") (by decide +kernel),
      fs_idx (j := 269) (f := "__loop12") (by decide +kernel)]
    decide +kernel
  rw [kidsB_sum, hF]
  refine ⟨by omega, ?_⟩
  refine le_trans (by omega : _ ≤ 3 * ((D.τ - 4) * 17) + 51 + 678 + 12 * (2241 + (D.τ - 3 + 171) +
    (374 + (D.τ - 3) / 8 * 374) + (77 + (D.τ - 3) % 8 * 77) + 60)) ?_
  generalize hT : D.τ = t at hτ hτ1
  interval_cases t <;> norm_num

end VkData

end
end LeanVM.Guest.B1.VerifySub
