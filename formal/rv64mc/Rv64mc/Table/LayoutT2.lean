/-
  Rv64mc.Table.LayoutT2

  `layout.rs`'s total contracts at the image (`liftProg Gen.fns`), new in wave 4a, each at its index with the
  generated link, the stack `Gen.Needs` gives, and its callees' total theorems (`RuntimeT`, `LayoutLeafT`,
  `FieldT`). Left as hypotheses, environment facts: `alloc`'s two (`RuntimeT.alloc`) and `clmul_low`'s table
  (`FieldT.ClmulTable`, which `E::mul` reads), where a function needs them.

  ## Main results

  * `placementNext`, `jumpConstraints`
-/

import Rv64mc.Table.RuntimeT
import Rv64mc.Table.LayoutLeafT
import Rv64mc.Proof.Layout.PlacementNextT
import Rv64mc.Proof.Layout.JumpConstraintsT
import Rv64mc.Table.FieldT

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

/-- **`jump_constraints` at the image** (function 148). -/
theorem jumpConstraints (hnext : VerifierRv64.Bump.AsGlobalAlloc.Alloc.link.d_NEXT.addr = env.nextAddr)
    (hend : env.heapEnd = 0x78000000#64) (hd : Table.FieldT.ClmulTable env) :
    JumpConstraintsT.SpecT env (liftProg fns) Idx.Verifier.Layout.JumpConstraints
      Needs.Verifier.Layout.JumpConstraints :=
  JumpConstraintsT.total env _ _ Verifier.Layout.JumpConstraints.link Verifier.Layout.JumpConstraints.tmpl_eq
    Verifier.Layout.JumpConstraints.wf (by decide) (by decide) (by decide) (by decide)
    (Table.RuntimeT.alloc env hnext hend) (Table.FieldT.eMul env hd) (Table.RuntimeT.panicNounwindFmt env)
    (Table.RuntimeT.panicBoundsCheck env)

end Rv64mc.Table.LayoutT2

/-- info: 'Rv64mc.Table.LayoutT2.placementNext' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rv64mc.Table.LayoutT2.placementNext

/-- info: 'Rv64mc.Table.LayoutT2.jumpConstraints' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rv64mc.Table.LayoutT2.jumpConstraints
