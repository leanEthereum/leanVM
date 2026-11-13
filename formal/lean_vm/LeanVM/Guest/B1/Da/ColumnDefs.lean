/-
  LeanVM.Guest.B1.Da.ColumnDefs

  The checks of `da_verify_column`'s body and of its blob loop `da_verify_column_loop0` (G:4562-4576).
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

variable {rd : Reader}

/-! ## The checks -/

/-- `da_verify_column_loop0`: blob `x`'s cell of the column. -/
def l21Ok (fn : Fn) : Bool :=
  let A := atomsIn (loopPre fn)
  loopShapeF fn name% «da_verify_column_loop0» && decide (fn.params.length = 6) &&
  hasCall (loopPre fn) "da_verify_cell" [.n 2] [.n 6, .n 7, .n 8] &&
  isMul A (.n 9) (.n 3) (.n 0) && A.any (isLoadAt (.n 10) (.n 9) 0) &&
  isMul A (.n 11) (.n 10) (.n 4) && A.any (isLoadAt (.n 12) (.n 11) 512) &&
  A.any (isAddAt (.n 13) (.n 12) (.n 8)) && A.any (isLoadAt (.n 13) (.n 11) 513) &&
  isMul A (.n 14) (.n 10) (.n 5) && A.any (isLoadAt (.n 6) (.n 14) 0) &&
  A.any (isLoadAt (.n 7) (.n 14) 1)

/-- `da_verify_column`'s block (its body but the final `ret`). -/
noncomputable def colP : List Stmt := (Fn.body fn% «da_verify_column»).dropLast

/-- **`da_verify_column`'s block, checked.** -/
noncomputable def colOk : Bool :=
  let P := colP
  let A := atomsIn P
  decide ((fn% «da_verify_column»).params = (List.range 7).map V.n) &&
  stmtsEqb (Fn.body fn% «da_verify_column») (P ++ [.ret []]) && P.all Stmt.flat &&
  isMul A (.n 7) (.n 4) (.n 0) && A.any (isLoadAt (.n 8) (.n 7) 0) &&
  monoIs A (.n 12) (.n 6) (.n 0) 8 &&
  hasCall P "da_expand__L7_L8" [.n 8, .n 5, .n 3, .n 12] [.n 13] &&
  isMul A (.n 14) (.n 0) (.n 0) &&
  guardOk P (.n 16) name% «da_verify_column_loop0» (.n 17) (.n 1) [.n 13, .n 2, .n 0, .n 14]

/-! ## A blob's step and the frames -/

/-- **Blob `x`'s cell of the column, at the loop's valuation `σr`**: a `da_verify_cell` call on
the weights at `lv`, its sum `σr (.n 8)` added to the running sum of the region at `rowbase[x]`
(through `xb`), its digest `σr (.n 6)`, `σr (.n 7)` the region's leaf (through `xb2`). -/
def CellStepW (C : CallRel) (rd : Reader) (σr : Val) (lv rowbase xb xb2 x : E) : Prop :=
  C "da_verify_cell" [lv] [σr (.n 6), σr (.n 7), σr (.n 8)] ∧
    ∃ base a : E, LoadHolds rd (rowbase * x) 0 base ∧ LoadHolds rd (base * xb) 512 a ∧
      LoadHolds rd (base * xb) 513 (a + σr (.n 8)) ∧ LoadHolds rd (base * xb2) 0 (σr (.n 6)) ∧
      LoadHolds rd (base * xb2) 1 (σr (.n 7))

/-- The valuation of blob `i`'s iteration of `da_verify_column_loop0` in the column called with `cargs`
(`[g^h, n_blob_g, rowbase, zs, top_leaves, cell_factors, offsets]`), at the frame map `Vm`. -/
def colRowV (Vm : FrameMap) (cargs : List E) (i : ℕ) : Val :=
  Vm name% «da_verify_column_loop0» [gen ^ i, cargs.getD 1 0, Vm "da_verify_column" cargs [] (.n 13), cargs.getD 2 0,
    cargs.getD 0 0, Vm "da_verify_column" cargs [] (.n 14)] []

/-- The symbols of blob `i`'s cell in the column called with `cargs`: its cell check's. -/
def colSyms (Vm : FrameMap) (cargs : List E) (i : ℕ) : List K :=
  cellSymsOf (Vm "da_verify_cell" [Vm "da_verify_column" cargs [] (.n 13)]
    [colRowV Vm cargs i (.n 6), colRowV Vm cargs i (.n 7), colRowV Vm cargs i (.n 8)])

end
end LeanVM.Guest.B1.Da
