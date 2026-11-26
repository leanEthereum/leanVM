/-
  Rv64mc.Table.WhirT2

  The WHIR functions' total contracts of wave 4b at the image (`liftProg Gen.fns`): each function's total theorem at
  its index, with the generated link, the stack `Gen.Needs` gives (a caller's bound over its callee's by `decide`),
  and its callees' total theorems (`FieldT.eMul`, `RuntimeT.assertFailedUsizeUsize`; for `fold_row` also
  `FieldT.baseMul`, `RuntimeT.panicBoundsCheck`; for `ring_weight` also `FieldT.eSquare`, `RuntimeT.alloc`,
  `RuntimeT.handleError`, `CopyUseT.memcpy`; `RingWeight::evaluate` takes `ringWeight`). Left as hypotheses: `clmul_low`'s constant table in the image's static
  data (`FieldT.ClmulTable`), and for `ring_weight` and `RingWeight::evaluate` the allocator's two facts (`NEXT`'s data reference and the heap's
  end), environment facts.

  ## Main results

  * `foldRow`, `ringWeight`, `ringWeightEvaluate`
-/

import Rv64mc.Table.FieldT
import Rv64mc.Table.RuntimeT
import Rv64mc.Table.CopyUseT
import Rv64mc.Proof.Whir.FoldRowT
import Rv64mc.Proof.Whir.RingWeightT
import Rv64mc.Proof.Whir.RingWeightEvaluateT
import Rv64mc.Gen.Link.Verifier.RingSwitch
import Rv64mc.Gen.Link.Verifier.Whir

namespace Rv64mc.Table.WhirT2

open MachineChecked.RiscV.Lift Rv64mc.Gen Rv64mc.Proof.Whir

variable (env : Env)

theorem foldRow (hd : FieldT.ClmulTable env) :
    FoldRowT.specT env (liftProg fns) Idx.Verifier.Whir.FoldRow Needs.Verifier.Whir.FoldRow :=
  FoldRowT.total env _ _ _ Verifier.Whir.FoldRow.tmpl_eq Verifier.Whir.FoldRow.wf (by decide) (by decide) (by decide)
    (by decide) (FieldT.eMul env hd) (RuntimeT.panicBoundsCheck env) (FieldT.baseMul env hd)
    (RuntimeT.assertFailedUsizeUsize env)

theorem ringWeight (hnext : VerifierRv64.Bump.AsGlobalAlloc.Alloc.link.d_NEXT.addr = env.nextAddr)
    (hend : env.heapEnd = 0x78000000#64) (hd : FieldT.ClmulTable env) :
    RingWeightT.specT env (liftProg fns) Idx.Verifier.RingSwitch.RingWeight Needs.Verifier.RingSwitch.RingWeight :=
  RingWeightT.total env _ _ _ Verifier.RingSwitch.RingWeight.tmpl_eq Verifier.RingSwitch.RingWeight.wf (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (RuntimeT.alloc env hnext hend)
    (RuntimeT.handleError env) (CopyUseT.memcpy env) (FieldT.eMul env hd) (FieldT.eSquare env)
    (RuntimeT.assertFailedUsizeUsize env)

theorem ringWeightEvaluate (hnext : VerifierRv64.Bump.AsGlobalAlloc.Alloc.link.d_NEXT.addr = env.nextAddr)
    (hend : env.heapEnd = 0x78000000#64) (hd : FieldT.ClmulTable env) :
    RingWeightEvaluateT.specT env (liftProg fns) Idx.Verifier.RingSwitch.RingWeight.Evaluate
      Needs.Verifier.RingSwitch.RingWeight.Evaluate :=
  RingWeightEvaluateT.total env _ _ _ Verifier.RingSwitch.RingWeight.Evaluate.tmpl_eq
    Verifier.RingSwitch.RingWeight.Evaluate.wf (by decide) (ringWeight env hnext hend hd)

end Rv64mc.Table.WhirT2

/-- info: 'Rv64mc.Table.WhirT2.foldRow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rv64mc.Table.WhirT2.foldRow

/-- info: 'Rv64mc.Table.WhirT2.ringWeight' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rv64mc.Table.WhirT2.ringWeight

/-- info: 'Rv64mc.Table.WhirT2.ringWeightEvaluate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rv64mc.Table.WhirT2.ringWeightEvaluate
