/-
  Rv64mc.Table.CellLanesT

  `keccak_cell_lanes`'s total contract (`CellLanesSafeT`) at the image, a leaf.

  ## Main results

  * `keccakCellLanesT`
-/

import Rv64mc.Proof.Layout.KeccakCellLanesT
import Rv64mc.Gen.Needs
import Rv64mc.Gen.Link.Verifier.Layout

namespace Rv64mc.Table.CellLanesT

open MachineChecked.RiscV.Lift Rv64mc.Gen

variable (env : Env)

/-- **`keccak_cell_lanes` at the image** (function 208). -/
theorem keccakCellLanesT : Proof.Layout.KeccakCellLanesT.CellLanesSafeT env (liftProg fns)
    Idx.Verifier.Layout.KeccakCellLanes Needs.Verifier.Layout.KeccakCellLanes :=
  HoldsT.mono_need (Proof.Layout.KeccakCellLanesT.total Verifier.Layout.KeccakCellLanes.tmpl_eq) (by decide)

end Rv64mc.Table.CellLanesT

/-- info: 'Rv64mc.Table.CellLanesT.keccakCellLanesT' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rv64mc.Table.CellLanesT.keccakCellLanesT
