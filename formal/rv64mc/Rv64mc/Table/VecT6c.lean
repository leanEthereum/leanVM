/-
  Rv64mc.Table.VecT6c

  The total contracts of the vector builders and drops new in wave 6c at the image (`liftProg Gen.fns`), each at its
  index with the generated link, the stack `Gen.Needs` gives, and its callees' total theorems. Left as hypotheses,
  environment facts only: `alloc`'s two (`RuntimeT.alloc`), for the two `concat`s.

  ## Main results

  * `concatVecE`, `concatSliceE`, `dropVecTable`, `dropLayout`
-/

import Rv64mc.Table.RuntimeT
import Rv64mc.Table.BuildT
import Rv64mc.Proof.Runtime.ConcatVecET
import Rv64mc.Proof.Runtime.ConcatSliceET
import Rv64mc.Proof.Runtime.DropLayoutT
import Rv64mc.Table.VecT
import Rv64mc.Gen.Link.Core
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

/-- **`<[&[E]] as Concat<E>>::concat` at the image** (function 87). -/
theorem concatSliceE :
    ConcatSliceET.SpecT env (liftProg fns) Idx.Alloc.Slice.SliceRefSliceE.AsConcatE.Concat
      Needs.Alloc.Slice.SliceRefSliceE.AsConcatE.Concat :=
  ConcatSliceET.total env _ _ Alloc.Slice.SliceRefSliceE.AsConcatE.Concat.link
    Alloc.Slice.SliceRefSliceE.AsConcatE.Concat.tmpl_eq Alloc.Slice.SliceRefSliceE.AsConcatE.Concat.wf (by decide)
    (by decide) (by decide) (RuntimeT.alloc env hnext hend) (BuildT.specExtendE env hnext hend)
    (RuntimeT.handleError env)

omit hnext hend in
/-- **The drop glue of `Vec<Table>` at the image** (function 71). -/
theorem dropVecTable :
    DropTablesT.SpecT env (liftProg fns) Idx.Core.Ptr.DropGlueVecTable Needs.Core.Ptr.DropGlueVecTable :=
  DropTablesT.total env _ _ Core.Ptr.DropGlueVecTable.link Core.Ptr.DropGlueVecTable.tmpl_eq
    Core.Ptr.DropGlueVecTable.wf (by decide) (VecT.dropVecVecForm env)

omit hnext hend in
/-- **The drop glue of `Layout` at the image** (function 70). -/
theorem dropLayout :
    DropLayoutT.SpecT env (liftProg fns) Idx.Core.Ptr.DropGlueLayout Needs.Core.Ptr.DropGlueLayout :=
  DropLayoutT.total env _ _ Core.Ptr.DropGlueLayout.link Core.Ptr.DropGlueLayout.tmpl_eq Core.Ptr.DropGlueLayout.wf
    (by decide) (by decide) (dropVecTable env) (VecT.dropVecBusBlock env)

end Rv64mc.Table.VecT6c

/-- info: 'Rv64mc.Table.VecT6c.concatVecE' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rv64mc.Table.VecT6c.concatVecE

/-- info: 'Rv64mc.Table.VecT6c.concatSliceE' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rv64mc.Table.VecT6c.concatSliceE

/-- info: 'Rv64mc.Table.VecT6c.dropVecTable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rv64mc.Table.VecT6c.dropVecTable

/-- info: 'Rv64mc.Table.VecT6c.dropLayout' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rv64mc.Table.VecT6c.dropLayout
