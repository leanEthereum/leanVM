/-
  Rv64mc.Table.VecT6c

  The total contracts of the vector builders new in wave 6c at the image (`liftProg Gen.fns`), each at its index with
  the generated link, the stack `Gen.Needs` gives, and its callees' total theorems. Left as hypotheses, environment
  facts only: `alloc`'s two (`RuntimeT.alloc`).

  ## Main results

  * `concatVecE`
-/

import Rv64mc.Table.RuntimeT
import Rv64mc.Table.BuildT
import Rv64mc.Proof.Runtime.ConcatVecET
import Rv64mc.Gen.Link.Alloc

namespace Rv64mc.Table.VecT6c

open MachineChecked.RiscV.Lift Rv64mc.Gen Rv64mc.Proof.Runtime

variable (env : Env) (hnext : VerifierRv64.Bump.AsGlobalAlloc.Alloc.link.d_NEXT.addr = env.nextAddr)
  (hend : env.heapEnd = 0x78000000#64)
include hnext hend

/-- **`<[Vec<E>] as Concat<E>>::concat` at the image** (function 110). -/
theorem concatVecE :
    ConcatVecET.SpecT env (liftProg fns) Idx.Alloc.Slice.SliceVecE.AsConcatE.Concat
      Needs.Alloc.Slice.SliceVecE.AsConcatE.Concat :=
  ConcatVecET.total env _ _ Alloc.Slice.SliceVecE.AsConcatE.Concat.link
    Alloc.Slice.SliceVecE.AsConcatE.Concat.tmpl_eq Alloc.Slice.SliceVecE.AsConcatE.Concat.wf (by decide) (by decide)
    (by decide) (RuntimeT.alloc env hnext hend) (BuildT.specExtendE env hnext hend) (RuntimeT.handleError env)

end Rv64mc.Table.VecT6c

/-- info: 'Rv64mc.Table.VecT6c.concatVecE' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rv64mc.Table.VecT6c.concatVecE
