/-
  LeanVM.Guest.CoreMode.CellLanes

  A function's values' cells (`B2C.cellJ`) as a lane vector the generator writes, checked against the certificate's
  cells in one streamed pass (`Packed.lanesEq`): a pointer's or a returned value's cell is then one shift of a literal.
-/

module

public import LeanVM.Guest.CoreMode.Route
public import LeanVM.Guest.Packed.Lanes

/-!
# The cells as lanes

Where `L` holds the certificate's cells in lanes of `Bridge.cellBits` (`lanesEq`), `B2C.cellJ j` is `L`'s lane at the
value's number (`cellJ_of_lanes`), so the pointers' and returned values' checks with the cells read from `L`
(`ptrCellAt`, `retCellAt` at `laneCell L`) are `ptrCellB j`, `retCellB j`.
-/

namespace LeanVM.Guest.CoreMode

open LeanVM.Guest LeanVM.Guest.Core
open LeanVM.Guest.Packed (lane lanesEq lanesEq_getD)

/-- A value's cell read from the lanes `L`. -/
@[expose] public def laneCell (L : ℕ) (v : V) : ℕ := lane L Bridge.cellBits v.idx

public section

theorem cellJ_of_lanes {j L : ℕ} (h : lanesEq Bridge.cellBits (certOf j).locs L = true) :
    B2C.cellJ j = laneCell L :=
  funext fun v ↦ lanesEq_getD h v.idx

/-- **The pointers' cells, from the lanes.** -/
theorem all_ptrCellB_of_P {j L : ℕ} {l : List Stmt} (h : lanesEq Bridge.cellBits (certOf j).locs L = true)
    (hl : l.all (ptrCellAt (laneCell L) j) = true) : l.all (ptrCellB j) = true := by
  rw [ptrCellB, cellJ_of_lanes h]
  exact hl

/-- **The returned values' cells, from the lanes.** -/
theorem all_retCellB_of_P {j L : ℕ} {l : List Stmt} (h : lanesEq Bridge.cellBits (certOf j).locs L = true)
    (hl : l.all (retCellAt (laneCell L) j) = true) : l.all (retCellB j) = true := by
  rw [retCellB, cellJ_of_lanes h]
  exact hl

end

end LeanVM.Guest.CoreMode
