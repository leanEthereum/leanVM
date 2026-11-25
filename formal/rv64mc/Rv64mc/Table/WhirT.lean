/-
  Rv64mc.Table.WhirT

  `whir_queries`' and `frobenius_8`'s total contracts at the image (`liftProg Gen.fns`). Left as a hypothesis:
  `WHIR_QUERIES`' tables in the image's static data (`DataRef.InData`, as `Whir.lean`'s `whirQueries` takes it), an
  environment fact; `Whir.lean`'s `whirQueriesTable` reads the table from it.

  ## Main results

  * `whirQueries`, `frobenius8`
-/

import Rv64mc.Table.Whir
import Rv64mc.Table.FieldT
import Rv64mc.Proof.Whir.WhirQueriesT
import Rv64mc.Proof.Whir.Frobenius8T

namespace Rv64mc.Table.WhirT

open MachineChecked.RiscV.Lift Rv64mc.Gen Rv64mc.Proof.Whir

variable (env : Env)

theorem whirQueries
    (hdata : DataRef.InData env (Verifier.Whir.WhirQueries.tables Verifier.Whir.WhirQueries.link)) :
    WhirQueriesT.specT env (liftProg fns) Idx.Verifier.Whir.WhirQueries Needs.Verifier.Whir.WhirQueries :=
  WhirQueriesT.total env _ _ _ Verifier.Whir.WhirQueries.tmpl_eq Verifier.Whir.WhirQueries.wf
    (Table.Whir.whirQueriesTable env hdata)

theorem frobenius8 :
    Frobenius8T.specT env (liftProg fns) Idx.Verifier.RingSwitch.Frobenius8 Needs.Verifier.RingSwitch.Frobenius8 :=
  Frobenius8T.total env _ _ _ Verifier.RingSwitch.Frobenius8.tmpl_eq Verifier.RingSwitch.Frobenius8.wf (by decide)
    (Table.FieldT.eSquare env)

end Rv64mc.Table.WhirT

/-- info: 'Rv64mc.Table.WhirT.whirQueries' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rv64mc.Table.WhirT.whirQueries

/-- info: 'Rv64mc.Table.WhirT.frobenius8' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rv64mc.Table.WhirT.frobenius8
