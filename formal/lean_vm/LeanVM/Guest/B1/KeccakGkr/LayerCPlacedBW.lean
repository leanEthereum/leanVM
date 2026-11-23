/-
  LeanVM.Guest.B1.KeccakGkr.LayerCPlacedBW

  `keccak_layer`'s words at the deployed frame sizes (`B2C.fs`): the callees' words from their
  words certificates, the bound in numbers.
-/

module

public import LeanVM.Guest.B1.KeccakGkr.LayerCPlacedB
public import LeanVM.Guest.Count.Words
public import LeanVM.Guest.Data.NameStrings

/-!
# `keccak_layer` within its words at `B2C.fs`

At the deployed frame sizes the words certificates (`Count.Words`) bound the eight-round pack loops by `374` words per iteration and their frame by as many, the remainder loops by `77` per iteration and their frame by as many, and the layers' frames by `2242`. Thus `layerWords B2C.fs first y 374 77` is at most `2242 + (y + 171) + (374 + ⌊y/8⌋ * 374) + (77 + (y % 8) * 77)` (`layerWords_fs_le_y`).
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Guest.Memory LeanVM.Guest.Count
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.Main (MemL RegionL)
open LeanVM.Protocol.KeccakGkr

@[expose] public section

/-- A loop's run's words at `B2C.fs`, from its certificate: `K` per iteration and its one phantom
frame. -/
theorem loop_totalLeOn_at {j K : ℕ} {f : String} (h : wOkK j f = true) (he : wSKtJ j ≤ K)
    (hj : (coreProgram[j]?).map Fn.name = some f) :
    TotalLeOn coreProgram LeanVM.Guest.B2C.fs f LoopPre fun a ↦
      logG (a.getD 1 0) * K + LeanVM.Guest.B2C.fs f := by
  have h1 := wSKt_totalLeOn h
  rw [wSKt_idx hj] at h1
  intro rd t args rets hn hp hv hb
  exact (h1 rd t args rets hn hp hv hb).trans
    (Nat.add_le_add_right (Nat.mul_le_mul_left _ he) _)

/-- **The eight-round pack loops' runs' words at `B2C.fs`**: at most `374` per iteration and
their frame. -/
theorem packLoop_totalLeOn_fs {first : ℕ} (hf : first < 2) :
    TotalLeOn coreProgram LeanVM.Guest.B2C.fs (packLoopName first) LoopPre
      fun a ↦ logG (a.getD 1 0) * 374 + LeanVM.Guest.B2C.fs (packLoopName first) := by
  interval_cases first
  · exact loop_totalLeOn_at (j := idx% «keccak_layer__L0_loop0») (by decide +kernel)
      (by decide +kernel) (by decide +kernel)
  · exact loop_totalLeOn_at (j := idx% «keccak_layer__L1_loop0») (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

/-- **The remainder loops' runs' words at `B2C.fs`**: at most `77` per iteration and their
frame. -/
theorem remLoop_totalLeOn_fs {first : ℕ} (hf : first < 2) :
    TotalLeOn coreProgram LeanVM.Guest.B2C.fs (remLoopName first) LoopPre
      fun a ↦ logG (a.getD 1 0) * 77 + LeanVM.Guest.B2C.fs (remLoopName first) := by
  interval_cases first
  · exact loop_totalLeOn_at (j := idx% «keccak_layer__L0_loop1») (by decide +kernel)
      (by decide +kernel) (by decide +kernel)
  · exact loop_totalLeOn_at (j := idx% «keccak_layer__L1_loop1») (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

/-- The pack loops' frame at `B2C.fs`: at most their words per iteration. -/
theorem packLoopName_fs {first : ℕ} (hf : first < 2) :
    LeanVM.Guest.B2C.fs (packLoopName first) ≤ 374 := by
  interval_cases first
  · rw [show packLoopName 0 = name% «keccak_layer__L0_loop0» from rfl,
      fs_idx (j := idx% «keccak_layer__L0_loop0») (f := name% «keccak_layer__L0_loop0»)
          (by decide +kernel)]
    decide +kernel
  · rw [show packLoopName 1 = name% «keccak_layer__L1_loop0» from rfl,
      fs_idx (j := idx% «keccak_layer__L1_loop0») (f := name% «keccak_layer__L1_loop0»)
          (by decide +kernel)]
    decide +kernel

/-- The remainder loops' frame at `B2C.fs`: at most their words per iteration. -/
theorem remLoopName_fs {first : ℕ} (hf : first < 2) :
    LeanVM.Guest.B2C.fs (remLoopName first) ≤ 77 := by
  interval_cases first
  · rw [show remLoopName 0 = name% «keccak_layer__L0_loop1» from rfl,
      fs_idx (j := idx% «keccak_layer__L0_loop1») (f := name% «keccak_layer__L0_loop1»)
          (by decide +kernel)]
    decide +kernel
  · rw [show remLoopName 1 = name% «keccak_layer__L1_loop1» from rfl,
      fs_idx (j := idx% «keccak_layer__L1_loop1») (f := name% «keccak_layer__L1_loop1»)
          (by decide +kernel)]
    decide +kernel

/-- The layers' frames at `B2C.fs`: at most `2242`. -/
theorem layerName_fs {first : ℕ} (hf : first < 2) :
    LeanVM.Guest.B2C.fs (layerName first) ≤ 2242 := by
  interval_cases first
  · rw [show layerName 0 = "keccak_layer__L0" from rfl,
      fs_idx (j := idx% «keccak_layer__L0») (f := "keccak_layer__L0") (by decide +kernel)]
    decide +kernel
  · rw [show layerName 1 = "keccak_layer__L1" from rfl,
      fs_idx (j := idx% «keccak_layer__L1») (f := "keccak_layer__L1") (by decide +kernel)]
    decide +kernel

/-- **A layer's words at `B2C.fs`**, its frame at most `2242`. -/
theorem layerWords_fs_le_y {first : ℕ} (hf : first < 2) (y : ℕ) :
    layerWords LeanVM.Guest.B2C.fs first y 374 77 ≤
      2242 + (y + 171) + (374 + y / 8 * 374) + (77 + y % 8 * 77) := by
  have := layerName_fs hf
  have := packLoopName_fs hf
  have := remLoopName_fs hf
  simp only [layerWords]
  omega

end
end LeanVM.Guest.B1.VerifySub
