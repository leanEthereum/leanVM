/-
  Rv64mc.Table.LayoutT2

  `layout.rs`'s total contracts at the image (`liftProg Gen.fns`), new in wave 4a, each at its index with the
  generated link, the stack `Gen.Needs` gives, and its callees' total theorems (`RuntimeT`, `LayoutLeafT`). No
  hypothesis is left open.

  ## Main results

  * `placementNext`
-/

import Rv64mc.Table.RuntimeT
import Rv64mc.Table.LayoutLeafT
import Rv64mc.Proof.Layout.PlacementNextT

namespace Rv64mc.Table.LayoutT2

open MachineChecked.RiscV.Lift Rv64mc.Gen Rv64mc.Proof.Layout

variable (env : Env)

/-- **`GenericShunt::next` over `build_layout`'s placements at the image** (function 183). -/
theorem placementNext :
    PlacementNextT.SpecT env (liftProg fns) Idx.Core.Iter.Adapters.GenericShuntMapEnumerateHad7e794e.AsIterator.Next
      Needs.Core.Iter.Adapters.GenericShuntMapEnumerateHad7e794e.AsIterator.Next :=
  PlacementNextT.total env _ _ Core.Iter.Adapters.GenericShuntMapEnumerateHad7e794e.AsIterator.Next.link
    Core.Iter.Adapters.GenericShuntMapEnumerateHad7e794e.AsIterator.Next.tmpl_eq
    Core.Iter.Adapters.GenericShuntMapEnumerateHad7e794e.AsIterator.Next.wf (by decide) (by decide) (by decide)
    (Table.LayoutLeafT.qkeccakSlot env) (Table.LayoutLeafT.isOutputLane env) (Table.RuntimeT.panicBoundsCheck env)

end Rv64mc.Table.LayoutT2

/-- info: 'Rv64mc.Table.LayoutT2.placementNext' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rv64mc.Table.LayoutT2.placementNext
