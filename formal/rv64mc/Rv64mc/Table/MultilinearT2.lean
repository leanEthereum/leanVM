/-
  Rv64mc.Table.MultilinearT2

  `dot`'s second total contract at the image (`liftProg Gen.fns`), next to `MultilinearT.lean`'s `dot`: over slices
  owned by the caller (`DotOwnT`), with the generated link, the stack `Gen.Needs` gives and its callees' total
  theorems (`FieldT.eMul`, `RuntimeT.assertFailedUsizeUsize`). Left as a hypothesis: `clmul_low`'s constant in the
  image's static data (`FieldT.ClmulTable`), an environment fact.

  ## Main results

  * `dotOwn`
-/

import Rv64mc.Table.FieldT
import Rv64mc.Table.RuntimeT
import Rv64mc.Proof.Multilinear.DotOwnT
import Rv64mc.Gen.Link.Verifier.Multilinear

namespace Rv64mc.Table.MultilinearT2

open MachineChecked.RiscV.Lift Rv64mc.Gen Rv64mc.Proof.Multilinear

variable (env : Env) (hd : FieldT.ClmulTable env)
include hd

theorem dotOwn : DotOwnT.specT env (liftProg fns) Idx.Verifier.Multilinear.Dot Needs.Verifier.Multilinear.Dot :=
  DotOwnT.total env _ _ _ Verifier.Multilinear.Dot.tmpl_eq Verifier.Multilinear.Dot.wf (by decide) (by decide)
    (FieldT.eMul env hd) (RuntimeT.assertFailedUsizeUsize env)

end Rv64mc.Table.MultilinearT2

/-- info: 'Rv64mc.Table.MultilinearT2.dotOwn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rv64mc.Table.MultilinearT2.dotOwn
