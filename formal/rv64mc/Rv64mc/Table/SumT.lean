/-
  Rv64mc.Table.SumT

  The total contracts of the `E::sum` closures at the image (`liftProg Gen.fns`): each function's total theorem at
  its index, with the generated link, the stack `Gen.Needs` gives, and `panic_bounds_check`'s `Aborts`
  (`RuntimeT.panicBoundsCheck`, raised to the caller's stack by `HoldsT.mono_need`). No hypothesis is left.

  ## Main results

  * `eSumU16`, `eSumRcBits`, `eSumEmbedBits`
-/

import Rv64mc.Table.RuntimeT
import Rv64mc.Proof.Field.ESumU16T
import Rv64mc.Proof.Field.ESumRcBitsT
import Rv64mc.Proof.Field.ESumEmbedBitsT
import Rv64mc.Gen.Link.Verifier.Field.E

namespace Rv64mc.Table.SumT

open MachineChecked.RiscV.Lift Rv64mc.Gen Rv64mc.Proof.Field

variable (env : Env)

theorem eSumU16 :
    ESumU16T.SumSafeT env (liftProg fns) Idx.Verifier.Field.E.SumMapIterU16EvaluateCloH33077ef9
      Needs.Verifier.Field.E.SumMapIterU16EvaluateCloH33077ef9 :=
  ESumU16T.total env _ _ _ Verifier.Field.E.SumMapIterU16EvaluateCloH33077ef9.tmpl_eq
    Verifier.Field.E.SumMapIterU16EvaluateCloH33077ef9.wf (HoldsT.mono_need (RuntimeT.panicBoundsCheck env) (by decide))

theorem eSumRcBits :
    ESumRcBitsT.SumSafeT env (liftProg fns) Idx.Verifier.Field.E.SumMapFilterRangeUsizeVeHdfe1ff21
      Needs.Verifier.Field.E.SumMapFilterRangeUsizeVeHdfe1ff21 :=
  ESumRcBitsT.total env _ _ _ Verifier.Field.E.SumMapFilterRangeUsizeVeHdfe1ff21.tmpl_eq
    Verifier.Field.E.SumMapFilterRangeUsizeVeHdfe1ff21.wf (HoldsT.mono_need (RuntimeT.panicBoundsCheck env) (by decide))

theorem eSumEmbedBits :
    ESumEmbedBitsT.SumSafeT env (liftProg fns) Idx.Verifier.Field.E.SumMapFilterRangeUsizeInHbf23f0ea
      Needs.Verifier.Field.E.SumMapFilterRangeUsizeInHbf23f0ea :=
  ESumEmbedBitsT.total env _ _ _ Verifier.Field.E.SumMapFilterRangeUsizeInHbf23f0ea.tmpl_eq
    Verifier.Field.E.SumMapFilterRangeUsizeInHbf23f0ea.wf (HoldsT.mono_need (RuntimeT.panicBoundsCheck env) (by decide))

end Rv64mc.Table.SumT

/-- info: 'Rv64mc.Table.SumT.eSumU16' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rv64mc.Table.SumT.eSumU16

/-- info: 'Rv64mc.Table.SumT.eSumRcBits' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rv64mc.Table.SumT.eSumRcBits

/-- info: 'Rv64mc.Table.SumT.eSumEmbedBits' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rv64mc.Table.SumT.eSumEmbedBits
