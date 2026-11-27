/-
  Rv64mc.Table.SumT6f

  The total contracts of wave 6f's `E::sum` closures at the image (`liftProg Gen.fns`): each function's total theorem
  at its index, with the generated link, the stack `Gen.Needs` gives (bounds over the callees' by `decide`), and the
  callees' total theorems (`FieldT.baseMul`, `RuntimeT.panicBoundsCheck` raised by `HoldsT.mono_need`). Open:
  `clmul_low`'s table (`FieldT.ClmulTable`) and `RMFE_PROJECT` (`ESumProjectT.Tab`), environment facts.

  ## Main results

  * `eSumNovel`, `eSumProject`
-/

import Rv64mc.Table.FieldT
import Rv64mc.Table.RuntimeT
import Rv64mc.Proof.Field.ESumNovelT
import Rv64mc.Proof.Field.ESumProjectT
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

end Rv64mc.Table.SumT6f

/-- info: 'Rv64mc.Table.SumT6f.eSumNovel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rv64mc.Table.SumT6f.eSumNovel

/-- info: 'Rv64mc.Table.SumT6f.eSumProject' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rv64mc.Table.SumT6f.eSumProject
