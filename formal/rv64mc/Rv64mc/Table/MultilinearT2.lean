/-
  Rv64mc.Table.MultilinearT2

  The multilinear builders' total contracts at the image (`liftProg Gen.fns`), each at its index with the generated
  link, the stack `Gen.Needs` gives, and its callees' total theorems in `RuntimeT` and `AllocT`. Left as hypotheses,
  as in `RuntimeT`: the environment's two facts about the image that `alloc` reads.

  ## Main results

  * `selectorPoint`
-/

import Rv64mc.Table.AllocT
import Rv64mc.Proof.Multilinear.SelectorPointT
import Rv64mc.Gen.Link.Verifier.Multilinear

namespace Rv64mc.Table.MultilinearT2

open MachineChecked.RiscV.Lift Rv64mc.Gen Rv64mc.Proof.Runtime Rv64mc.Proof.Multilinear

variable (env : Env) (hnext : VerifierRv64.Bump.AsGlobalAlloc.Alloc.link.d_NEXT.addr = env.nextAddr)
  (hend : env.heapEnd = 0x78000000#64)
include hnext hend

theorem selectorPoint :
    SelectorPointT.SpecT env (liftProg fns) Idx.Verifier.Multilinear.SelectorPoint
      Needs.Verifier.Multilinear.SelectorPoint :=
  SelectorPointT.total env _ _ Verifier.Multilinear.SelectorPoint.link Verifier.Multilinear.SelectorPoint.tmpl_eq
    Verifier.Multilinear.SelectorPoint.wf (by decide) (by decide) (by decide)
    (RuntimeT.alloc env hnext hend) (AllocT.reserveE env hnext hend) (RuntimeT.handleError env)

end Rv64mc.Table.MultilinearT2

/-- info: 'Rv64mc.Table.MultilinearT2.selectorPoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rv64mc.Table.MultilinearT2.selectorPoint

/-- info: 'Rv64mc.Proof.Multilinear.SelectorPointT.total' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rv64mc.Proof.Multilinear.SelectorPointT.total
