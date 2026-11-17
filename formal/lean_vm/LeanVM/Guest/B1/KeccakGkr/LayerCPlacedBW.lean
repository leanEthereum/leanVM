/-
  LeanVM.Guest.B1.KeccakGkr.LayerCPlacedBW

  `layer_completeAtFB` at the deployed frame sizes (`B2C.fs`): the callees' words from their
  words certificates, the bound in numbers.
-/

module

public import LeanVM.Guest.B1.KeccakGkr.LayerCPlacedB
public import LeanVM.Guest.Count.Words
public import LeanVM.Guest.Data.NameStrings

/-!
# `keccak_layer` within its words at `B2C.fs`

At the deployed frame sizes the words certificates (`Count.Words`) bound the eight-round pack loops by `374` words per iteration and their frame of `349` words, and the remainder loops by `77` per iteration and their frame of `73` words. The constant per-iteration bounds remain conservative. `grind_check__L3` has a frame of `60` words. The layers have frames of `2239` (`keccak_layer__L0`) and `1887` (`keccak_layer__L1`). Thus `layerWords B2C.fs first y 374 77` is at most `2241 + (y + 171) + (374 + ⌊y/8⌋ * 374) + (77 + (y % 8) * 77) + 60`, hence at most `4233` words for `y ≤ 25` and `4537` for `y ≤ 30`.
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

/-- The pack loops' frame at `B2C.fs`: `349`. -/
theorem packLoopName_fs {first : ℕ} (hf : first < 2) :
    LeanVM.Guest.B2C.fs (packLoopName first) = 349 := by
  interval_cases first
  · rw [show packLoopName 0 = name% «keccak_layer__L0_loop0» from rfl,
      fs_idx (j := idx% «keccak_layer__L0_loop0») (f := name% «keccak_layer__L0_loop0»)
          (by decide +kernel)]
    decide +kernel
  · rw [show packLoopName 1 = name% «keccak_layer__L1_loop0» from rfl,
      fs_idx (j := idx% «keccak_layer__L1_loop0») (f := name% «keccak_layer__L1_loop0»)
          (by decide +kernel)]
    decide +kernel

/-- The remainder loops' frame at `B2C.fs`: `73`. -/
theorem remLoopName_fs {first : ℕ} (hf : first < 2) :
    LeanVM.Guest.B2C.fs (remLoopName first) = 73 := by
  interval_cases first
  · rw [show remLoopName 0 = name% «keccak_layer__L0_loop1» from rfl,
      fs_idx (j := idx% «keccak_layer__L0_loop1») (f := name% «keccak_layer__L0_loop1»)
          (by decide +kernel)]
    decide +kernel
  · rw [show remLoopName 1 = name% «keccak_layer__L1_loop1» from rfl,
      fs_idx (j := idx% «keccak_layer__L1_loop1») (f := name% «keccak_layer__L1_loop1»)
          (by decide +kernel)]
    decide +kernel

/-- `grind_check__L3`'s frame at `B2C.fs`: `60`. -/
theorem grind3_fs : LeanVM.Guest.B2C.fs (grindCheckName 3) = 60 := by
  rw [fs_idx (j := idx% «grind_check__L3») (f := grindCheckName 3) (by decide +kernel)]
  decide +kernel

/-- The layers' frames at `B2C.fs` are bounded by `2241`. -/
theorem layerName_fs {first : ℕ} (hf : first < 2) :
    LeanVM.Guest.B2C.fs (layerName first) ≤ 2241 := by
  interval_cases first
  · rw [show layerName 0 = "keccak_layer__L0" from rfl,
      fs_idx (j := idx% «keccak_layer__L0») (f := "keccak_layer__L0") (by decide +kernel)]
    decide +kernel
  · rw [show layerName 1 = "keccak_layer__L1" from rfl,
      fs_idx (j := idx% «keccak_layer__L1») (f := "keccak_layer__L1") (by decide +kernel)]
    decide +kernel

/-- **A layer's words at `B2C.fs`**, its frame at most `2241`. -/
theorem layerWords_fs_le_y {first : ℕ} (hf : first < 2) (y : ℕ) :
    layerWords LeanVM.Guest.B2C.fs first y 374 77 ≤
      2241 + (y + 171) + (374 + y / 8 * 374) + (77 + y % 8 * 77) + 60 := by
  have := layerName_fs hf
  simp only [layerWords, packLoopName_fs hf, remLoopName_fs hf, grind3_fs]
  omega

/-- **A layer's words at `B2C.fs`, in numbers**: at most `4233` for `y ≤ 25`, `4537` for
`y ≤ 30`. -/
theorem layerWords_fs_le {first y : ℕ} (hf : first < 2) :
    (y ≤ 25 → layerWords LeanVM.Guest.B2C.fs first y 374 77 ≤ 4233) ∧
      (y ≤ 30 → layerWords LeanVM.Guest.B2C.fs first y 374 77 ≤ 4537) := by
  have h := layerWords_fs_le_y hf y
  constructor <;> intro hy <;> refine h.trans ?_ <;> interval_cases y <;> norm_num

variable {cert : String → V → ℕ}

set_option maxRecDepth 20000 in
/-- **`keccak_layer` is complete, placed, within `layerWords B2C.fs first D.y 374 77` words** at
the deployed frame sizes. -/
theorem layer_completeAtFB_fs {first : ℕ} (hf : first < 2) {κ : ℕ} (hκ : 11 ≤ κ) (D : LayerData)
    (CL : ClaimLay) (bcur bout tbE : ℕ) {p0 p1 iota : E}
    (hcl : D.cap.length = 5)
    (hw : first = 1 → (p0, p1) = Keccak.scalarCells D.w0 dsObserve)
    (hy1 : 1 ≤ D.y) (hy30 : D.y ≤ 30) (hpl : D.product.length = 47)
    (hpm : D.packMsgs.length = D.y) (hlm : D.localMsgs.length = 11)
    (hproj : projectedOf D.c D.product + iota * sumE D.c.mu = D.c.value)
    (hgrind : ((D.s0 first).absorbAll D.product dsObserve).GrindOk sGrindBits D.nonce)
    (hfin : LayerFinal D.c (D.s0 first) D.product D.nonce D.packMsgs D.localMsgs D.t)
    (hCL : CL.Ok first D.c D.y) :
    CompleteAtFB LeanVM.Guest.B2C.fs cert κ (layerName first)
      (fun fp ↦ layerLin D first CL bcur bout tbE (fp + LeanVM.Guest.B2C.fs (layerName first)))
      (D.cap ++ [p0, p1, ptr bcur, gen ^ D.y, gen ^ (D.y / 8), gen ^ (D.y % 8), ptr CL.bclaim,
        ptr bout, iota, ptr tbE])
      (fun fp rets Lout ↦ rets = D.rets first (ptr bcur) ∧
        Lout = layerBufs D first (ptr bcur) (fp + LeanVM.Guest.B2C.fs (layerName first)))
      (layerWords LeanVM.Guest.B2C.fs first D.y 374 77) :=
  layer_completeAtFB hf hκ D CL bcur bout tbE (packLoop_totalLeOn_fs hf) (remLoop_totalLeOn_fs hf)
    hcl hw hy1 hy30 hpl hpm hlm hproj hgrind hfin hCL

end
end LeanVM.Guest.B1.VerifySub
