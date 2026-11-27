/-
  Rv64mc.Table.FormT6g

  `<Form>::sum::<[Form; 3]>` (`SumArr3T`) at the image (`liftProg Gen.fns`), over `<Form as Add>::add`
  (`FormT6e.formAdd`). Left as hypotheses, environment facts: `alloc`'s two (`RuntimeT.alloc`) and `clmul_low`'s
  constant (`FieldT.ClmulTable`), through `add`.

  ## Main results

  * `sumArr3`
-/

import Rv64mc.Table.FormT6e
import Rv64mc.Proof.Layout.SumArr3T

namespace Rv64mc.Table.FormT6g

open MachineChecked.RiscV.Lift Rv64mc.Gen Rv64mc.Proof.Layout

variable (env : Env) (hnext : VerifierRv64.Bump.AsGlobalAlloc.Alloc.link.d_NEXT.addr = env.nextAddr)
  (hend : env.heapEnd = 0x78000000#64)
include hnext hend

/-- **`<Form>::sum::<[Form; 3]>` at the image** (function 204). -/
theorem sumArr3 (hd : FieldT.ClmulTable env) :
    SumArr3T.SpecT env (liftProg fns) Idx.Verifier.Layout.Form.SumArrFormN3 Needs.Verifier.Layout.Form.SumArrFormN3 :=
  SumArr3T.total env _ _ _ Verifier.Layout.Form.SumArrFormN3.tmpl_eq Verifier.Layout.Form.SumArrFormN3.wf
    (by decide) (FormT6e.formAdd env hnext hend hd)

end Rv64mc.Table.FormT6g

/-- info: 'Rv64mc.Table.FormT6g.sumArr3' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rv64mc.Table.FormT6g.sumArr3
