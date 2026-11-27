/-
  Rv64mc.Table.SumT6f

  The total contracts of wave 6f's `E::sum` closures at the image (`liftProg Gen.fns`): each function's total theorem
  at its index, with the generated link, the stack `Gen.Needs` gives (bounds over the callees' by `decide`), and the
  callees' total theorems (`FieldT.baseMul`, `FieldT.eMul`, `SumT.eSumU16`, `DotT2.dotOwn`,
  `RuntimeT.panicBoundsCheck`, raised by `HoldsT.mono_need` where the caller has no frame). Open: `clmul_low`'s
  table (`FieldT.ClmulTable`) and `RMFE_PROJECT` (`ESumProjectT.Tab`), environment facts.

  ## Main results

  * `eSumNovel`, `eSumProject`, `eSumForm`, `eSumBlock`, `eSumLane`
-/

import Rv64mc.Table.FieldT
import Rv64mc.Table.RuntimeT
import Rv64mc.Proof.Field.ESumNovelT
import Rv64mc.Proof.Field.ESumProjectT
import Rv64mc.Proof.Field.ESumFormT
import Rv64mc.Proof.Field.ESumBlockT
import Rv64mc.Table.SumT
import Rv64mc.Table.DotT2
import Rv64mc.Proof.Field.ESumLaneT
import Rv64mc.Gen.Link.Verifier.Field.E

namespace Rv64mc.Table.SumT6f

open MachineChecked.RiscV.Lift Rv64mc.Gen Rv64mc.Proof.Field

variable (env : Env)

/-- `novel_eval`'s sum (18). -/
theorem eSumNovel (hd : FieldT.ClmulTable env) :
    ESumNovelT.SumSafeT env (liftProg fns) Idx.Verifier.Field.E.SumMapZipIterEIntoIterKNovelEvalClosure0
      Needs.Verifier.Field.E.SumMapZipIterEIntoIterKNovelEvalClosure0 :=
  ESumNovelT.total env _ _ _ Verifier.Field.E.SumMapZipIterEIntoIterKNovelEvalClosure0.tmpl_eq
    Verifier.Field.E.SumMapZipIterEIntoIterKNovelEvalClosure0.wf (by decide) (FieldT.baseMul env hd)

/-- `verify_layer`'s functional term (29). -/
theorem eSumProject (hd : ESumProjectT.Tab env Verifier.Field.E.SumMapFilterRangeUsizeVeHf05a01b5.link) :
    ESumProjectT.SumSafeT env (liftProg fns) Idx.Verifier.Field.E.SumMapFilterRangeUsizeVeHf05a01b5
      Needs.Verifier.Field.E.SumMapFilterRangeUsizeVeHf05a01b5 :=
  ESumProjectT.total env _ _ _ Verifier.Field.E.SumMapFilterRangeUsizeVeHf05a01b5.tmpl_eq
    Verifier.Field.E.SumMapFilterRangeUsizeVeHf05a01b5.wf hd
    (HoldsT.mono_need (RuntimeT.panicBoundsCheck env) (by decide))

/-- `Form::evaluate`'s sum (33). -/
theorem eSumForm (hd : FieldT.ClmulTable env) :
    ESumFormT.SumSafeT env (liftProg fns) Idx.Verifier.Field.E.SumMapIterTVecUsizeEEEvaluateClosure0
      Needs.Verifier.Field.E.SumMapIterTVecUsizeEEEvaluateClosure0 :=
  ESumFormT.total env _ _ _ Verifier.Field.E.SumMapIterTVecUsizeEEEvaluateClosure0.tmpl_eq
    Verifier.Field.E.SumMapIterTVecUsizeEEEvaluateClosure0.wf (by decide) (by decide)
    (FieldT.eMul env hd) (RuntimeT.panicBoundsCheck env)

/-- `Bytecode::evaluate`'s block value (24). -/
theorem eSumBlock (hd : FieldT.ClmulTable env) :
    ESumBlockT.SumSafeT env (liftProg fns) Idx.Verifier.Field.E.SumMapIterTKVecU16EEvaluH09540813
      Needs.Verifier.Field.E.SumMapIterTKVecU16EEvaluH09540813 :=
  ESumBlockT.total env _ _ _ Verifier.Field.E.SumMapIterTKVecU16EEvaluH09540813.tmpl_eq
    Verifier.Field.E.SumMapIterTKVecU16EEvaluH09540813.wf (by decide) (by decide) (SumT.eSumU16 env)
    (FieldT.baseMul env hd)

/-- `verify_layer`'s bit-position sum (27). -/
theorem eSumLane (hd : FieldT.ClmulTable env) :
    ESumLaneT.SumSafeT env (liftProg fns) Idx.Verifier.Field.E.SumMapZipChunksEIterEVerifyLayerClosure3
      Needs.Verifier.Field.E.SumMapZipChunksEIterEVerifyLayerClosure3 :=
  ESumLaneT.total env _ _ _ Verifier.Field.E.SumMapZipChunksEIterEVerifyLayerClosure3.tmpl_eq
    Verifier.Field.E.SumMapZipChunksEIterEVerifyLayerClosure3.wf (by decide) (by decide) (DotT2.dotOwn env hd)
    (FieldT.eMul env hd)

end Rv64mc.Table.SumT6f

/-- info: 'Rv64mc.Table.SumT6f.eSumNovel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rv64mc.Table.SumT6f.eSumNovel

/-- info: 'Rv64mc.Table.SumT6f.eSumProject' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rv64mc.Table.SumT6f.eSumProject

/-- info: 'Rv64mc.Table.SumT6f.eSumForm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rv64mc.Table.SumT6f.eSumForm

/-- info: 'Rv64mc.Table.SumT6f.eSumBlock' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rv64mc.Table.SumT6f.eSumBlock

/-- info: 'Rv64mc.Table.SumT6f.eSumLane' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rv64mc.Table.SumT6f.eSumLane
