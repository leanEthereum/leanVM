/-
  Rv64mc.Table.SumT6f

  The total contracts of wave 6f's `E::sum` closures at the image (`liftProg Gen.fns`): each function's total theorem
  at its index, with the generated link, the stack `Gen.Needs` gives (bounds over the callees' by `decide`), and the
  callees' total theorems (`FieldT.baseMul`). Open: `clmul_low`'s table (`FieldT.ClmulTable`), an environment fact.

  ## Main results

  * `eSumNovel`
-/

import Rv64mc.Table.FieldT
import Rv64mc.Proof.Field.ESumNovelT
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

end Rv64mc.Table.SumT6f

/-- info: 'Rv64mc.Table.SumT6f.eSumNovel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rv64mc.Table.SumT6f.eSumNovel
