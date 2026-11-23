/-
  LeanVM.Guest.B1.Da.BlobDefs

  The bodies of `da_verify_blob` and of its cell loop `da_verify_blob_loop0`.
-/

module

public import LeanVM.Guest.B1.Da.VecFn
public import LeanVM.Guest.B1.Da.CellSound
public import LeanVM.Guest.B1.Main.Frames
public import LeanVM.Guest.Data.NameStrings
import LeanVM.Guest.ValRef
import LeanVM.Guest.Data.ValNames.«da_verify_blob»
import LeanVM.Guest.Data.ValNames.«da_verify_blob_loop0»

namespace LeanVM.Guest.B1.Da

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.Digest LeanVM.Guest.B1.Main

@[expose] public section

/-! ## The bodies -/

/-- `da_verify_blob_loop0(x, weights, base)`'s body: cell `log x`, `da_verify_cell` on
`weights[x]`, its sum added to the running sum (words `512`, `513` through `base·x`), its digest
the leaf at `base·x²`; then the next cell while `x·g ≠ g^128`. -/
def cBody : List Stmt :=
  [.atom (.mul (.n (val% «da_verify_blob_loop0» "d0~3")) (.n (val% «da_verify_blob_loop0» "weights")) (.n (val% «da_verify_blob_loop0» "xb"))), .atom (.load (.n (val% «da_verify_blob_loop0» "d0~4")) (.n (val% «da_verify_blob_loop0» "d0~3")) 0),
    .call "da_verify_cell" [.n (val% «da_verify_blob_loop0» "d0~4")] [.n (val% «da_verify_blob_loop0» "d0"), .n (val% «da_verify_blob_loop0» "d1"), .n (val% «da_verify_blob_loop0» "s")],
    .atom (.mul (.n (val% «da_verify_blob_loop0» "chain")) (.n (val% «da_verify_blob_loop0» "base")) (.n (val% «da_verify_blob_loop0» "xb"))), .atom (.load (.n (val% «da_verify_blob_loop0» "s2#0")) (.n (val% «da_verify_blob_loop0» "chain")) 512),
    .atom (.add (.n (val% «da_verify_blob_loop0» "s2#1")) (.n (val% «da_verify_blob_loop0» "s2#0")) (.n (val% «da_verify_blob_loop0» "s"))), .atom (.load (.n (val% «da_verify_blob_loop0» "s2#1")) (.n (val% «da_verify_blob_loop0» "chain")) 513),
    .atom (.mul (.n (val% «da_verify_blob_loop0» "leaf~0")) (.n (val% «da_verify_blob_loop0» "xb")) (.n (val% «da_verify_blob_loop0» "xb"))), .atom (.mul (.n (val% «da_verify_blob_loop0» "leaf")) (.n (val% «da_verify_blob_loop0» "base")) (.n (val% «da_verify_blob_loop0» "leaf~0"))),
    .atom (.load (.n (val% «da_verify_blob_loop0» "d0")) (.n (val% «da_verify_blob_loop0» "leaf")) 0), .atom (.load (.n (val% «da_verify_blob_loop0» "d1")) (.n (val% «da_verify_blob_loop0» "leaf")) 1),
    .atom (.const (.n (val% «da_verify_blob_loop0» "s7#0")) (word 2 0)), .atom (.mul (.n (val% «da_verify_blob_loop0» "s7#1")) (.n (val% «da_verify_blob_loop0» "xb")) (.n (val% «da_verify_blob_loop0» "s7#0"))),
    .atom (.const (.n (val% «da_verify_blob_loop0» "s7#2")) (word 325 0)), .atom (.add (.n (val% «da_verify_blob_loop0» "s7#3")) (.n (val% «da_verify_blob_loop0» "s7#1")) (.n (val% «da_verify_blob_loop0» "s7#2"))),
    .atom (.const (.n (val% «da_verify_blob_loop0» "s7#4")) (word 2 0)), .atom (.mul (.n (val% «da_verify_blob_loop0» "s7#5")) (.n (val% «da_verify_blob_loop0» "xb")) (.n (val% «da_verify_blob_loop0» "s7#4"))),
    .callIf (.n (val% «da_verify_blob_loop0» "s7#3")) name% «da_verify_blob_loop0» [.n (val% «da_verify_blob_loop0» "s7#5"), .n (val% «da_verify_blob_loop0» "weights"), .n (val% «da_verify_blob_loop0» "base")], .ret []]

/-- `da_verify_blob_loop0`, checked. -/
def cOk (fn : Fn) : Bool := decide (fn.params = [.n (val% «da_verify_blob_loop0» "xb"), .n (val% «da_verify_blob_loop0» "weights"), .n (val% «da_verify_blob_loop0» "base")]) && stmtsEqb fn.body cBody

/-- `da_verify_blob(weights)`'s body: its region (`HeapBuf(641)`), the running sum's first word
`0`, the cell loop from `1`, the sum's last word `0`, the root of the region's tree. -/
def blobBody : List Stmt :=
  [.atom (.hint (.alloc (.n (val% «da_verify_blob» "base")) 641)), .atom (.const (.n (val% «da_verify_blob» "s1#0")) (word 0 0)), .atom (.load (.n (val% «da_verify_blob» "s1#0")) (.n (val% «da_verify_blob» "base")) 512),
    .atom (.const (.n (val% «da_verify_blob» "s2#0")) (word 1 0)), .call name% «da_verify_blob_loop0» [.n (val% «da_verify_blob» "s2#0"), .n (val% «da_verify_blob» "weights"), .n (val% «da_verify_blob» "base")] [],
    .atom (.load (.n (val% «da_verify_blob» "s3#0")) (.n (val% «da_verify_blob» "base")) 640), .atom (.const (.n (val% «da_verify_blob» "s3#1")) (word 0 0)), .atom (.assertEq (.n (val% «da_verify_blob» "s3#0")) (.n (val% «da_verify_blob» "s3#1"))),
    .call "da_levels__L128_L7" [.n (val% «da_verify_blob» "base")] [.n (val% «da_verify_blob» "b0"), .n (val% «da_verify_blob» "b1")], .atom (.copy (.n (val% «da_verify_blob» "s5#0")) (.n (val% «da_verify_blob» "b0"))),
    .atom (.copy (.n (val% «da_verify_blob» "s5#0[1]")) (.n (val% «da_verify_blob» "b1"))), .ret [.n (val% «da_verify_blob» "s5#0"), .n (val% «da_verify_blob» "s5#0[1]")]]

/-- `da_verify_blob`, checked. -/
def blobOk (fn : Fn) : Bool := decide (fn.params = [.n (val% «da_verify_blob» "weights")]) && stmtsEqb fn.body blobBody

/-! ## The frames -/

/-- The valuation of `da_verify_blob`'s call on the weights at `w` returning `c0, c1`, at the frame
map `Vm`. -/
def blobV (Vm : FrameMap) (w c0 c1 : E) : Val := Vm "da_verify_blob" [w] [c0, c1]

/-- The valuation of cell `h`'s iteration of that call's cell loop. -/
def blobCellV (Vm : FrameMap) (w c0 c1 : E) (h : ℕ) : Val :=
  Vm name% «da_verify_blob_loop0» [gen ^ h, w, blobV Vm w c0 c1 (.n (val% «da_verify_blob» "base"))] []

/-- The symbols of cell `h` of that blob: its cell check's. -/
def blobSyms (Vm : FrameMap) (w c0 c1 : E) (h : ℕ) : List E :=
  cellSymsOf (Vm "da_verify_cell" [blobCellV Vm w c0 c1 h (.n (val% «da_verify_blob_loop0» "d0~4"))]
    [blobCellV Vm w c0 c1 h (.n (val% «da_verify_blob_loop0» "d0")), blobCellV Vm w c0 c1 h (.n (val% «da_verify_blob_loop0» "d1")), blobCellV Vm w c0 c1 h (.n (val% «da_verify_blob_loop0» "s"))])

/-- **The weights at `w` are the dual codeword of `z`**, column by column: `weights[h]` is a
pointer to the entries `128 h + e`. -/
def WeightsAt (rd : Reader) (z w : E) : Prop :=
  ∀ h < 128, ∃ lv : E, LoadHolds rd (w * gen ^ h) 0 lv ∧
    ∀ e < 128, ∀ v, rd (lv.limb 0 * addressOfIndex e) = some v → v = dualAt z (128 * h + e)

end
end LeanVM.Guest.B1.Da
