/-
  LeanVM.Guest.B1.Da.CellComplete

  `da_verify_cell`, completely: `128` symbols (the hint) and the weights in memory give its core
  IR relation, its returns the cell's digest and the dot product.
-/

module

public import LeanVM.Guest.B1.Da.Padding
import LeanVM.Guest.B1.Da.CellLink

/-!
# `da_verify_cell`, completely

The symbols and the weights satisfy the meaning, so the reference function (`cellRef_sem`) and,
through the link (`cell_linked`), the core function relate the weights' pointer to `cellRets`.
-/

namespace LeanVM.Guest.B1.Da

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Ref
open LeanVM.Protocol.KeccakHash LeanVM.Guest.B1.Digest

@[expose] public section

/-- The cell's returns: its symbols' digest's cells, then their dot product with the weights. -/
def cellRets (syms ws : List E) : List E :=
  digestCells (keccak256 (syms.flatMap E.toBytes)) ++
    [((List.range LeanDa.cellSymbols).map fun e ↦ ws.getD e 0 * syms.getD e 0).sum]

/-- `da_verify_cell`'s meaning, for given symbols and weights in memory, gives its core IR. -/
def da_verify_cell_complete_Spec : Prop :=
  ∀ (rd : Reader) (lv : E) (syms ws : List E), syms.length = LeanDa.cellSymbols →
    ws.length = LeanDa.cellSymbols → ReadsAt rd lv ws →
      coreProgram.Rel rd "da_verify_cell" [lv] (cellRets syms ws)

/-- **`da_verify_cell` is complete.** -/
theorem da_verify_cell_complete : da_verify_cell_complete_Spec := fun rd _ syms ws hsl hwl hr =>
  (rel_iff_sem find_da_verify_cell _ _).mpr <| (Map.check_sem_iff cell_linked _ _).mpr <|
    (cellRef_sem rd _ _).mpr ⟨syms, ws, hsl, hr, hwl, rfl⟩

end
end LeanVM.Guest.B1.Da
