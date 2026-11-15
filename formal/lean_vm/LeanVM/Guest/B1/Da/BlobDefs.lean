/-
  LeanVM.Guest.B1.Da.BlobDefs

  The bodies of `da_verify_blob` and of its cell loop `da_verify_blob_loop0` (G:4575-4590).
-/

module

public import LeanVM.Guest.B1.Da.VecFn
public import LeanVM.Guest.B1.Da.CellSound
public import LeanVM.Guest.B1.Main.Frames
public import LeanVM.Guest.Data.NameStrings

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
  [.atom (.mul (.n 3) (.n 1) (.n 0)), .atom (.load (.n 4) (.n 3) 0),
    .call "da_verify_cell" [.n 4] [.n 5, .n 6, .n 7],
    .atom (.mul (.n 8) (.n 2) (.n 0)), .atom (.load (.n 9) (.n 8) 512),
    .atom (.add (.n 10) (.n 9) (.n 7)), .atom (.load (.n 10) (.n 8) 513),
    .atom (.mul (.n 11) (.n 0) (.n 0)), .atom (.mul (.n 12) (.n 2) (.n 11)),
    .atom (.load (.n 5) (.n 12) 0), .atom (.load (.n 6) (.n 12) 1),
    .atom (.const (.n 13) (word 2 0)), .atom (.mul (.n 14) (.n 0) (.n 13)),
    .atom (.const (.n 15) (word 325 0)), .atom (.add (.n 16) (.n 14) (.n 15)),
    .atom (.const (.n 17) (word 2 0)), .atom (.mul (.n 18) (.n 0) (.n 17)),
    .callIf (.n 16) name% «da_verify_blob_loop0» [.n 18, .n 1, .n 2], .ret []]

/-- `da_verify_blob_loop0`, checked. -/
def cOk (fn : Fn) : Bool := decide (fn.params = [.n 0, .n 1, .n 2]) && stmtsEqb fn.body cBody

/-- `da_verify_blob(weights)`'s body: its region (`HeapBuf(641)`), the running sum's first word
`0`, the cell loop from `1`, the sum's last word `0`, the root of the region's tree. -/
def blobBody : List Stmt :=
  [.atom (.hint (.alloc (.n 1) 641)), .atom (.const (.n 2) (word 0 0)), .atom (.load (.n 2) (.n 1) 512),
    .atom (.const (.n 3) (word 1 0)), .call name% «da_verify_blob_loop0» [.n 3, .n 0, .n 1] [],
    .atom (.load (.n 4) (.n 1) 640), .atom (.const (.n 5) (word 0 0)), .atom (.assertEq (.n 4) (.n 5)),
    .call "da_levels__L128_L7" [.n 1] [.n 6, .n 7], .atom (.copy (.n 8) (.n 6)),
    .atom (.copy (.n 9) (.n 7)), .ret [.n 8, .n 9]]

/-- `da_verify_blob`, checked. -/
def blobOk (fn : Fn) : Bool := decide (fn.params = [.n 0]) && stmtsEqb fn.body blobBody

/-! ## The frames -/

/-- The valuation of `da_verify_blob`'s call on the weights at `w` returning `c0, c1`, at the frame
map `Vm`. -/
def blobV (Vm : FrameMap) (w c0 c1 : E) : Val := Vm "da_verify_blob" [w] [c0, c1]

/-- The valuation of cell `h`'s iteration of that call's cell loop. -/
def blobCellV (Vm : FrameMap) (w c0 c1 : E) (h : ℕ) : Val :=
  Vm name% «da_verify_blob_loop0» [gen ^ h, w, blobV Vm w c0 c1 (.n 1)] []

/-- The symbols of cell `h` of that blob: its cell check's. -/
def blobSyms (Vm : FrameMap) (w c0 c1 : E) (h : ℕ) : List K :=
  cellSymsOf (Vm "da_verify_cell" [blobCellV Vm w c0 c1 h (.n 4)]
    [blobCellV Vm w c0 c1 h (.n 5), blobCellV Vm w c0 c1 h (.n 6), blobCellV Vm w c0 c1 h (.n 7)])

/-- **The weights at `w` are the dual codeword of `z`**, column by column: `weights[h]` is a
pointer to the entries `256 h + e`. -/
def WeightsAt (rd : Reader) (z w : E) : Prop :=
  ∀ h < 128, ∃ lv : E, LoadHolds rd (w * gen ^ h) 0 lv ∧
    ∀ e < 256, ∀ v, rd (lv.limb 0 * addressOfIndex e) = some v → v = dualAt z (256 * h + e)

end
end LeanVM.Guest.B1.Da
