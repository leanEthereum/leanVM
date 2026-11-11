/-
  LeanVM.Guest.B1.KeccakGkr.LayerCPlacedBW

  `layer_completeAtFB` at the deployed frame sizes (`B2C.fs`): the callees' words from their
  words certificates, the bound in numbers.
-/

module

public import LeanVM.Guest.B1.KeccakGkr.LayerCPlacedB
public import LeanVM.Guest.Count.Words

/-!
# `keccak_layer` within its words at `B2C.fs`

At the deployed frame sizes the words certificates (`Count.Words`) give the callees' runs' words:
the eight-round pack loops `__loop37`, `__loop39` (core `425`, `427`, frame `473`) at most `473`
words per iteration and the run's one phantom frame (its last, skipped call's), the remainder loops
`__loop38`, `__loop40` (core `426`, `428`, frame `92`) at most `92` and their frame. So
`keccak_layer__L{first}` (core `264` for `first = 0`, frame `2624`; core `263` for `first = 1`,
frame `2245`) is complete within `layerWords B2C.fs first y 473 92`
`= fs (layerName first) + (y + 171) + (473 + ⌊y/8⌋ * 473) + (92 + (y % 8) * 92)`
(`layer_completeAtFB_fs`), at most `2624 + (y + 171) + (473 + ⌊y/8⌋ * 473) + (92 + (y % 8) * 92)`
(`layerWords_fs_le_y`): at most `4973` words for `y ≤ 25` (at `y = 23`), `5361` for `y ≤ 30`
(`layerWords_fs_le`).
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
theorem loop_totalLeOn_at {j K : ℕ} {f : String} (h : wOkK j f = true) (he : wSKtJ j = K)
    (hj : (coreProgram[j]?).map Fn.name = some f) :
    TotalLeOn coreProgram LeanVM.Guest.B2C.fs f LoopPre fun a ↦
      logG (a.getD 1 0) * K + LeanVM.Guest.B2C.fs f := by
  have h1 := wSKt_totalLeOn h
  rwa [wSKt_idx hj, he] at h1

/-- **The eight-round pack loops' runs' words at `B2C.fs`**: at most `473` per iteration and
their frame. -/
theorem packLoop_totalLeOn_fs {first : ℕ} (hf : first < 2) :
    TotalLeOn coreProgram LeanVM.Guest.B2C.fs (packLoopName first) LoopPre
      fun a ↦ logG (a.getD 1 0) * 473 + LeanVM.Guest.B2C.fs (packLoopName first) := by
  interval_cases first
  · exact loop_totalLeOn_at (j := 414) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact loop_totalLeOn_at (j := 412) (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- **The remainder loops' runs' words at `B2C.fs`**: at most `92` per iteration and their
frame. -/
theorem remLoop_totalLeOn_fs {first : ℕ} (hf : first < 2) :
    TotalLeOn coreProgram LeanVM.Guest.B2C.fs (remLoopName first) LoopPre
      fun a ↦ logG (a.getD 1 0) * 92 + LeanVM.Guest.B2C.fs (remLoopName first) := by
  interval_cases first
  · exact loop_totalLeOn_at (j := 415) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact loop_totalLeOn_at (j := 413) (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- The pack loops' frame at `B2C.fs`: `473`. -/
theorem packLoopName_fs {first : ℕ} (hf : first < 2) :
    LeanVM.Guest.B2C.fs (packLoopName first) = 473 := by
  interval_cases first
  · rw [show packLoopName 0 = "__loop39" from rfl,
      fs_idx (j := 414) (f := "__loop39") (by decide +kernel)]
    decide +kernel
  · rw [show packLoopName 1 = "__loop37" from rfl,
      fs_idx (j := 412) (f := "__loop37") (by decide +kernel)]
    decide +kernel

/-- The remainder loops' frame at `B2C.fs`: `92`. -/
theorem remLoopName_fs {first : ℕ} (hf : first < 2) :
    LeanVM.Guest.B2C.fs (remLoopName first) = 92 := by
  interval_cases first
  · rw [show remLoopName 0 = "__loop40" from rfl,
      fs_idx (j := 415) (f := "__loop40") (by decide +kernel)]
    decide +kernel
  · rw [show remLoopName 1 = "__loop38" from rfl,
      fs_idx (j := 413) (f := "__loop38") (by decide +kernel)]
    decide +kernel

/-- The layers' frames at `B2C.fs`: `2624` (`keccak_layer__L0`), `2245` (`keccak_layer__L1`). -/
theorem layerName_fs {first : ℕ} (hf : first < 2) :
    LeanVM.Guest.B2C.fs (layerName first) ≤ 2624 := by
  interval_cases first
  · rw [show layerName 0 = "keccak_layer__L0" from rfl,
      fs_idx (j := 266) (f := "keccak_layer__L0") (by decide +kernel)]
    decide +kernel
  · rw [show layerName 1 = "keccak_layer__L1" from rfl,
      fs_idx (j := 265) (f := "keccak_layer__L1") (by decide +kernel)]
    decide +kernel

/-- **A layer's words at `B2C.fs`**, its frame at most `2624`. -/
theorem layerWords_fs_le_y {first : ℕ} (hf : first < 2) (y : ℕ) :
    layerWords LeanVM.Guest.B2C.fs first y 473 92 ≤
      2624 + (y + 171) + (473 + y / 8 * 473) + (92 + y % 8 * 92) := by
  have := layerName_fs hf
  simp only [layerWords, packLoopName_fs hf, remLoopName_fs hf]
  omega

/-- **A layer's words at `B2C.fs`, in numbers**: at most `4973` for `y ≤ 25`, `5361` for
`y ≤ 30`. -/
theorem layerWords_fs_le {first y : ℕ} (hf : first < 2) :
    (y ≤ 25 → layerWords LeanVM.Guest.B2C.fs first y 473 92 ≤ 4973) ∧
      (y ≤ 30 → layerWords LeanVM.Guest.B2C.fs first y 473 92 ≤ 5361) := by
  have h := layerWords_fs_le_y hf y
  constructor <;> intro hy <;> refine h.trans ?_ <;> interval_cases y <;> norm_num

variable {cert : String → V → ℕ}

set_option maxRecDepth 20000 in
/-- **`keccak_layer` is complete, placed, within `layerWords B2C.fs first D.y 473 92` words** at
the deployed frame sizes. -/
theorem layer_completeAtFB_fs {first : ℕ} (hf : first < 2) (κ : ℕ) (D : LayerData)
    (CL : ClaimLay) (bcur bout : ℕ) {p0 p1 iota : E}
    (hcl : D.cap.length = 5) (hcap : AllCanonical D.cap)
    (hw : first = 1 → (p0, p1) = Keccak.scalarCells D.w0 dsObserve)
    (hy1 : 1 ≤ D.y) (hy30 : D.y ≤ 30) (hpl : D.product.length = 47)
    (hpm : D.packMsgs.length = D.y) (hlm : D.localMsgs.length = 11)
    (hproj : projectedOf D.c D.product + iota * sumE D.c.mu = D.c.value)
    (hfin : LayerFinal D.c (D.s0 first) D.product D.packMsgs D.localMsgs D.t)
    (hCL : CL.Ok first D.c D.y) :
    CompleteAtFB LeanVM.Guest.B2C.fs cert κ (layerName first)
      (fun fp ↦ layerLin D first CL bcur bout (fp + LeanVM.Guest.B2C.fs (layerName first)))
      (D.cap ++ [p0, p1, ptr bcur, gen ^ D.y, gen ^ (D.y / 8), gen ^ (D.y % 8), ptr CL.bclaim,
        ptr bout, iota])
      (fun fp rets Lout ↦ rets = D.rets first (ptr bcur) ∧
        Lout = layerBufs D first (ptr bcur) (fp + LeanVM.Guest.B2C.fs (layerName first)))
      (layerWords LeanVM.Guest.B2C.fs first D.y 473 92) :=
  layer_completeAtFB hf κ D CL bcur bout (packLoop_totalLeOn_fs hf) (remLoop_totalLeOn_fs hf)
    hcl hcap hw hy1 hy30 hpl hpm hlm hproj hfin hCL

end
end LeanVM.Guest.B1.VerifySub
