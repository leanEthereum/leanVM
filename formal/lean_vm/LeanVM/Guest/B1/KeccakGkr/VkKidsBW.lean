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
`plainName 0`) at most `325`, `keccak_plain_rounds__L4_L1` (core `267`, `plainName 1`) at most
`229`; the layers' eight-round loops `473` per iteration and remainder loops `92`, and their frames
(`LayerCPlacedBW`). So `verify_keccak`'s callees are complete within
`D.kidsB B2C.fs 17 473 92 325 229` (`kids_completeB_fs`), whose sum is at most
`3 * ((τ - 4) * 17) + 51 + 879 + 12 * (2624 + (y + 171) + (473 + y / 8 * 473) + (92 + y % 8 * 92))`
(`y = τ - 3`), at most `61728` words for `τ ≤ 28` (`kidsB_fs_le`).
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
  · exact loop_totalLeOn_at (j := 266) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact loop_totalLeOn_at (j := 270) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact loop_totalLeOn_at (j := 272) (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- **`keccak_plain_rounds__L6_L0`'s words at `B2C.fs`**: `325`. -/
theorem plain0_totalLe_fs :
    TotalLe coreProgram LeanVM.Guest.B2C.fs (plainName 0) fun _ ↦ 325 := by
  have h1 := wSB_totalLe (j := 269) (f := "keccak_plain_rounds__L6_L0") (by decide +kernel)
  rwa [wSB_idx (j := 269) (f := "keccak_plain_rounds__L6_L0") (by decide +kernel),
    show wSBJ 269 = 325 by decide +kernel] at h1

/-- **`keccak_plain_rounds__L4_L1`'s words at `B2C.fs`**: `229`. -/
theorem plain1_totalLe_fs :
    TotalLe coreProgram LeanVM.Guest.B2C.fs (plainName 1) fun _ ↦ 229 := by
  have h1 := wSB_totalLe (j := 271) (f := "keccak_plain_rounds__L4_L1") (by decide +kernel)
  rwa [wSB_idx (j := 271) (f := "keccak_plain_rounds__L4_L1") (by decide +kernel),
    show wSBJ 271 = 229 by decide +kernel] at h1

namespace VkData

variable {D : VkData} {cert : String → V → ℕ}

/-- **`verify_keccak`'s calls, complete where it places them, within their words at `B2C.fs`.** -/
theorem kids_completeB_fs (h : D.Ok) (κ : ℕ) (B curE chiE olE zvE slE : ℕ) :
    KidsGB LeanVM.Guest.B2C.fs cert κ (D.kids LeanVM.Guest.B2C.fs B curE chiE olE zvE slE)
      (D.kidsB LeanVM.Guest.B2C.fs 17 473 92 325 229) :=
  kids_completeB h κ B curE chiE olE zvE slE copyLoop_totalLeOn_fs
    (fun _ hf ↦ packLoop_totalLeOn_fs hf) (fun _ hf ↦ remLoop_totalLeOn_fs hf)
    plain0_totalLe_fs plain1_totalLe_fs

/-- **The callees' words at `B2C.fs`, in numbers**: the copy loops `(τ - 4) * 17 + 17` each, the
openings' rounds `325 + 229 + 325`, each layer (`y = τ - 3`) at most
`2624 + (y + 171) + (473 + y / 8 * 473) + (92 + y % 8 * 92)`; at most `61728` (`τ ≤ 28`, the
largest at `y = 23`). -/
theorem kidsB_fs_le (h : D.Ok) :
    (D.kidsB LeanVM.Guest.B2C.fs 17 473 92 325 229).sum ≤
      3 * ((D.τ - 4) * 17) + 51 + 879 + 12 * (2624 + (D.τ - 3 + 171) + (473 + (D.τ - 3) / 8 * 473) +
        (92 + (D.τ - 3) % 8 * 92)) ∧
    (D.kidsB LeanVM.Guest.B2C.fs 17 473 92 325 229).sum ≤ 61728 := by
  have hτ := h.2.1
  have hτ1 := h.1
  have hL : ((List.range 12).map (fun s ↦ layerWords LeanVM.Guest.B2C.fs (firstOf s)
      (D.layer s).y 473 92)).sum ≤
      12 * (2624 + (D.τ - 3 + 171) + (473 + (D.τ - 3) / 8 * 473) + (92 + (D.τ - 3) % 8 * 92)) := by
    have := List.sum_le_length_nsmul ((List.range 12).map (fun s ↦ layerWords
      LeanVM.Guest.B2C.fs (firstOf s) (D.layer s).y 473 92))
      (2624 + (D.τ - 3 + 171) + (473 + (D.τ - 3) / 8 * 473) + (92 + (D.τ - 3) % 8 * 92))
      (fun x hx ↦ ?_)
    · simpa using this
    obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hx
    have hs' := List.mem_range.mp hs
    rw [D.layer_y h (by omega)]
    exact layerWords_fs_le_y (by unfold firstOf; split <;> omega) _
  have hF : LeanVM.Guest.B2C.fs "__loop10" + LeanVM.Guest.B2C.fs "__loop11" +
      LeanVM.Guest.B2C.fs "__loop12" = 51 := by
    rw [fs_idx (j := 266) (f := "__loop10") (by decide +kernel),
      fs_idx (j := 270) (f := "__loop11") (by decide +kernel),
      fs_idx (j := 272) (f := "__loop12") (by decide +kernel)]
    decide +kernel
  rw [kidsB_sum, hF]
  refine ⟨by omega, ?_⟩
  refine le_trans (by omega : _ ≤ 3 * ((D.τ - 4) * 17) + 51 + 879 + 12 * (2624 + (D.τ - 3 + 171) +
    (473 + (D.τ - 3) / 8 * 473) + (92 + (D.τ - 3) % 8 * 92))) ?_
  generalize hT : D.τ = t at hτ hτ1
  interval_cases t <;> norm_num

end VkData

end
end LeanVM.Guest.B1.VerifySub
