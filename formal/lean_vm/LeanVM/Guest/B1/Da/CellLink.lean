/-
  LeanVM.Guest.B1.Da.CellLink

  `da_verify_cell`'s compiled function is linked to its reference function, its hinted symbols
  owning their names.
-/

module

public import LeanVM.Guest.B1.Da.CellRef
-- Read by the check; it also keeps `lake-build.py --dev`'s kernel on this module (`CORE_READ`).
public import LeanVM.Guest.Pack.P7.Core
meta import LeanVM.Guest.Ref.Elab
meta import LeanVM.Guest.B1.Da.CellRef

/-!
# `da_verify_cell`, linked

`cell_linked` is one kernel evaluation of the link check (`LeanVM.Guest.Ref.Link`) of
`da_verify_cell` against `cellRef`, given the map `cellMap`. The map is computed when this module is
elaborated (`cell_map%`): the inference `infer`'s walk, started with the hinted symbols named, since
the loop's products read them before the first `KECCAK` does. Unverified: a wrong entry can only
make the check fail. `cell_owners`: the hinted values own the names of the symbols.
-/

namespace LeanVM.Guest.B1.Da

open LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Ref

meta section

deriving instance Lean.ToExpr for CellName

/-- `cell_map%`: the map of `da_verify_cell`'s core function and `cellRef`, inferred with the
parameter and the hinted symbols `.n 1 … .n 128` named first, as a literal. -/
syntax (name := cellMapStx) "cell_map%" : term

open Lean Elab Term in
def elabCellMap : TermElab := fun _ _ => do
  let f ← Ref.Elab.decFn ``Fn.«da_verify_cell».core
  let a := (⟨[], 0, 0⟩ : Acc CellName).names (f.params ++ (List.range 128).map (V.n <| · + 1))
    (cellRef.params.map .v ++ (List.range 128).map (Tm.v <| .sym ·))
  match a.stmts f.body cellRef.body with
  | (⟨rev, _, _⟩, _) => return Ref.Elab.mapE ⟨rev.reverse.map (·.getD (.const 0, false))⟩

end

attribute [local term_elab cellMapStx] elabCellMap

@[expose] public section

/-- `da_verify_cell`'s map, computed at elaboration. -/
noncomputable def cellMap : Map CellName := cell_map%

/-- **`da_verify_cell`'s core function is linked to `cellRef`.** -/
theorem cell_linked : cellMap.check Fn.«da_verify_cell».core cellRef = true := by decide +kernel

/-- The hinted values own the names of the symbols. -/
theorem cell_owners : ownersAt cellMap ((List.range 128).map fun j => (j + 1, .sym j)) = true := by
  decide +kernel

end
end LeanVM.Guest.B1.Da
