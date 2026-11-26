/-
  Rv64mc.Table.WhirT2

  The WHIR functions' total contracts of wave 4b at the image (`liftProg Gen.fns`): each function's total theorem at
  its index, with the generated link, the stack `Gen.Needs` gives (a caller's bound over its callee's by `decide`),
  and its callees' total theorems (for `fold_row`: `FieldT.eMul`, `FieldT.baseMul`, `RuntimeT.panicBoundsCheck`,
  `RuntimeT.assertFailedUsizeUsize`). Left as a hypothesis: `clmul_low`'s constant table in the image's static data
  (`FieldT.ClmulTable`), an environment fact.

  ## Main results

  * `foldRow`
-/

import Rv64mc.Table.FieldT
import Rv64mc.Table.RuntimeT
import Rv64mc.Proof.Whir.FoldRowT
import Rv64mc.Gen.Link.Verifier.Whir

namespace Rv64mc.Table.WhirT2

open MachineChecked.RiscV.Lift Rv64mc.Gen Rv64mc.Proof.Whir

variable (env : Env)

theorem foldRow (hd : FieldT.ClmulTable env) :
    FoldRowT.specT env (liftProg fns) Idx.Verifier.Whir.FoldRow Needs.Verifier.Whir.FoldRow :=
  FoldRowT.total env _ _ _ Verifier.Whir.FoldRow.tmpl_eq Verifier.Whir.FoldRow.wf (by decide) (by decide) (by decide)
    (by decide) (FieldT.eMul env hd) (RuntimeT.panicBoundsCheck env) (FieldT.baseMul env hd)
    (RuntimeT.assertFailedUsizeUsize env)

end Rv64mc.Table.WhirT2

/-- info: 'Rv64mc.Table.WhirT2.foldRow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rv64mc.Table.WhirT2.foldRow
