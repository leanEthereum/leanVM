/-
  Rv64mc.Table.FieldT2

  The field's vector builders' total contracts at the image (`liftProg Gen.fns`), each at its index with the
  generated link, the stack `Gen.Needs` gives, and its callees' total theorems in `RuntimeT` and `FieldT`. Left as
  hypotheses: the environment's two facts about the image that `alloc` reads, and `clmul_low`'s constant table
  (`FieldT.ClmulTable`).

  ## Main results

  * `powers`
-/

import Rv64mc.Table.FieldT
import Rv64mc.Table.RuntimeT
import Rv64mc.Proof.Field.PowersT

namespace Rv64mc.Table.FieldT2

open MachineChecked.RiscV.Lift Rv64mc.Gen Rv64mc.Proof.Field

variable (env : Env) (hnext : VerifierRv64.Bump.AsGlobalAlloc.Alloc.link.d_NEXT.addr = env.nextAddr)
  (hend : env.heapEnd = 0x78000000#64)
include hnext hend

/-- **`powers` at the image** (function 53). -/
theorem powers (hd : FieldT.ClmulTable env) :
    PowersT.SpecT env (liftProg fns) Idx.Verifier.Field.Powers Needs.Verifier.Field.Powers :=
  PowersT.total env _ _ Verifier.Field.Powers.link Verifier.Field.Powers.tmpl_eq Verifier.Field.Powers.wf
    (by decide) (by decide) (by decide)
    (RuntimeT.alloc env hnext hend) (FieldT.eMul env hd) (RuntimeT.handleError env)

end Rv64mc.Table.FieldT2

/-- info: 'Rv64mc.Table.FieldT2.powers' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rv64mc.Table.FieldT2.powers

/-- info: 'Rv64mc.Proof.Field.PowersT.total' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rv64mc.Proof.Field.PowersT.total
