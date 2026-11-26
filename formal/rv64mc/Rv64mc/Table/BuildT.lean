/-
  Rv64mc.Table.BuildT

  Wave 4a's vector builders' total contracts at the image (`liftProg Gen.fns`), each at its index with the generated
  link, the stack `Gen.Needs` gives, and its callees' total theorems in `RuntimeT`, `AllocT` and `CopyUseT`. Left
  as hypotheses, as in `RuntimeT`: the environment's two facts about the image that `alloc` reads.

  ## Main results

  * `specExtendE`
-/

import Rv64mc.Table.AllocT
import Rv64mc.Table.CopyUseT
import Rv64mc.Proof.Runtime.SpecExtendT

namespace Rv64mc.Table.BuildT

open MachineChecked.RiscV.Lift Rv64mc.Gen Rv64mc.Proof.Runtime

variable (env : Env) (hnext : VerifierRv64.Bump.AsGlobalAlloc.Alloc.link.d_NEXT.addr = env.nextAddr)
  (hend : env.heapEnd = 0x78000000#64)
include hnext hend

/-- **`Vec<E>::spec_extend` from a slice at the image** (function 106). -/
theorem specExtendE :
    SpecExtendT.SpecT env (liftProg fns) Idx.Alloc.Vec.SpecExtend.VecE.AsSpecExtendRefEIterE.SpecExtend
      Needs.Alloc.Vec.SpecExtend.VecE.AsSpecExtendRefEIterE.SpecExtend :=
  SpecExtendT.total env _ _ Alloc.Vec.SpecExtend.VecE.AsSpecExtendRefEIterE.SpecExtend.link
    Alloc.Vec.SpecExtend.VecE.AsSpecExtendRefEIterE.SpecExtend.tmpl_eq
    Alloc.Vec.SpecExtend.VecE.AsSpecExtendRefEIterE.SpecExtend.wf (by decide) (by decide)
    (AllocT.reserveE env hnext hend) (CopyUseT.memcpy env)

end Rv64mc.Table.BuildT

/-- info: 'Rv64mc.Table.BuildT.specExtendE' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rv64mc.Table.BuildT.specExtendE
