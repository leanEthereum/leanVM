/-
  Rv64mc.Table.LayoutLeafT

  The layout's leaves' total contracts at the image (`liftProg Gen.fns`): `Layout::committed`, `qkeccak_slot` and
  `is_output_lane`, each at its index with the generated link and the stack `Gen.Needs` gives. Leaves: no
  hypothesis.

  ## Main results

  * `committed`, `qkeccakSlot`, `isOutputLane`
-/

import Rv64mc.Proof.Layout.CommittedT
import Rv64mc.Proof.Layout.QkeccakSlotT
import Rv64mc.Proof.Layout.IsOutputLaneT
import Rv64mc.Gen.Needs
import Rv64mc.Gen.Link.Verifier.Layout

namespace Rv64mc.Table.LayoutLeafT

open MachineChecked.RiscV.Lift Rv64mc.Gen Rv64mc.Proof.Layout

variable (env : Env)

theorem committed :
    CommittedT.specT env (liftProg fns) Idx.Verifier.Layout.Layout.Committed Needs.Verifier.Layout.Layout.Committed :=
  CommittedT.total env _ _ _ Verifier.Layout.Layout.Committed.tmpl_eq

theorem qkeccakSlot :
    QkeccakSlotT.specT env (liftProg fns) Idx.Verifier.Layout.QkeccakSlot Needs.Verifier.Layout.QkeccakSlot :=
  QkeccakSlotT.total env _ _ _ Verifier.Layout.QkeccakSlot.tmpl_eq _

theorem isOutputLane :
    IsOutputLaneT.specT env (liftProg fns) Idx.Verifier.Layout.IsOutputLane Needs.Verifier.Layout.IsOutputLane :=
  IsOutputLaneT.total env _ _ _ Verifier.Layout.IsOutputLane.tmpl_eq _

end Rv64mc.Table.LayoutLeafT

/-- info: 'Rv64mc.Table.LayoutLeafT.committed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rv64mc.Table.LayoutLeafT.committed

/-- info: 'Rv64mc.Table.LayoutLeafT.qkeccakSlot' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rv64mc.Table.LayoutLeafT.qkeccakSlot

/-- info: 'Rv64mc.Table.LayoutLeafT.isOutputLane' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rv64mc.Table.LayoutLeafT.isOutputLane
