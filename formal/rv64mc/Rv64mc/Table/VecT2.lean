/-
  Rv64mc.Table.VecT2

  The vector builders' total contracts at the image (`liftProg Gen.fns`), each at its index with the generated link,
  the stack `Gen.Needs` gives, and its callees' total theorems in `RuntimeT` and `AllocT`. Left as hypotheses, as
  in `RuntimeT`: the environment's two facts about the image that `alloc` reads.

  ## Main results

  * `fromElemE`
-/

import Rv64mc.Table.AllocT
import Rv64mc.Proof.Runtime.FromElemT

namespace Rv64mc.Table.VecT2

open MachineChecked.RiscV.Lift Rv64mc.Gen Rv64mc.Proof.Runtime
open Rv64mc.Proof.Runtime.FromElemT (FromElemSpecT)

variable (env : Env) (hnext : VerifierRv64.Bump.AsGlobalAlloc.Alloc.link.d_NEXT.addr = env.nextAddr)
  (hend : env.heapEnd = 0x78000000#64)
include hnext hend

theorem fromElemE :
    FromElemSpecT env (liftProg fns) Idx.Alloc.Vec.SpecFromElem.E.AsSpecFromElem.FromElemGlobal
      Needs.Alloc.Vec.SpecFromElem.E.AsSpecFromElem.FromElemGlobal :=
  FromElemT.e_total env _ _ Alloc.Vec.SpecFromElem.E.AsSpecFromElem.FromElemGlobal.link
    Alloc.Vec.SpecFromElem.E.AsSpecFromElem.FromElemGlobal.tmpl_eq
    Alloc.Vec.SpecFromElem.E.AsSpecFromElem.FromElemGlobal.wf (by decide) (by decide) (by decide)
    (RuntimeT.alloc env hnext hend) (AllocT.reserveE env hnext hend) (RuntimeT.handleError env)

end Rv64mc.Table.VecT2

/-- info: 'Rv64mc.Table.VecT2.fromElemE' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rv64mc.Table.VecT2.fromElemE
