/-
  Rv64mc.Table.VecT2

  The vector builders' total contracts at the image (`liftProg Gen.fns`), each at its index with the generated link,
  the stack `Gen.Needs` gives, and its callees' total theorems in `RuntimeT` and `AllocT`. Left as hypotheses, as
  in `RuntimeT`: the environment's two facts about the image that `alloc` reads, and the static data words a
  builder reads (`DataRef.InData`).

  ## Main results

  * `fromElemE`, `fromElemOptionE`, `fromIterOptionE`
-/

import Rv64mc.Table.AllocT
import Rv64mc.Proof.Runtime.FromElemT
import Rv64mc.Proof.Runtime.FromElemOptT
import Rv64mc.Proof.Runtime.FromIterOptT

namespace Rv64mc.Table.VecT2

open MachineChecked.RiscV.Lift Rv64mc.Gen Rv64mc.Proof.Runtime
open Rv64mc.Proof.Runtime.FromElemT (FromElemSpecT)
open Rv64mc.Proof.Runtime.FromElemOptT (FromElemOptSpecT)
open Rv64mc.Proof.Runtime.FromIterOptT (FromIterSpecT)

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

theorem fromElemOptionE
    (hd : DataRef.InData env [(Alloc.Vec.SpecFromElem.OptionE.AsSpecFromElem.FromElemGlobal.link.d_c8_d6dfd6bc,
      Alloc.Vec.SpecFromElem.OptionE.AsSpecFromElem.FromElemGlobal.d_c8_d6dfd6bc_words)]) :
    FromElemOptSpecT env (liftProg fns) Idx.Alloc.Vec.SpecFromElem.OptionE.AsSpecFromElem.FromElemGlobal
      Needs.Alloc.Vec.SpecFromElem.OptionE.AsSpecFromElem.FromElemGlobal :=
  FromElemOptT.total env _ _ Alloc.Vec.SpecFromElem.OptionE.AsSpecFromElem.FromElemGlobal.link
    Alloc.Vec.SpecFromElem.OptionE.AsSpecFromElem.FromElemGlobal.tmpl_eq
    Alloc.Vec.SpecFromElem.OptionE.AsSpecFromElem.FromElemGlobal.wf hd (by decide) (by decide) (by decide)
    (RuntimeT.alloc env hnext hend) (AllocT.reserveOptionE env hnext hend) (RuntimeT.handleError env)

theorem fromIterOptionE
    (hd : DataRef.InData env
      [(Alloc.Vec.SpecFromIterNested.VecOptionE.AsSpecFromIterNestedOptiH0c7a0891.FromIter.link.d_c8_131d94e1,
        Alloc.Vec.SpecFromIterNested.VecOptionE.AsSpecFromIterNestedOptiH0c7a0891.FromIter.d_c8_131d94e1_words)]) :
    FromIterSpecT env (liftProg fns)
      Idx.Alloc.Vec.SpecFromIterNested.VecOptionE.AsSpecFromIterNestedOptiH0c7a0891.FromIter
      Needs.Alloc.Vec.SpecFromIterNested.VecOptionE.AsSpecFromIterNestedOptiH0c7a0891.FromIter :=
  FromIterOptT.total env _ _ Alloc.Vec.SpecFromIterNested.VecOptionE.AsSpecFromIterNestedOptiH0c7a0891.FromIter.link
    Alloc.Vec.SpecFromIterNested.VecOptionE.AsSpecFromIterNestedOptiH0c7a0891.FromIter.tmpl_eq
    Alloc.Vec.SpecFromIterNested.VecOptionE.AsSpecFromIterNestedOptiH0c7a0891.FromIter.wf hd
    (by decide) (by decide) (by decide)
    (RuntimeT.alloc env hnext hend) (AllocT.reserveOptionE env hnext hend) (RuntimeT.handleError env)

end Rv64mc.Table.VecT2

/-- info: 'Rv64mc.Table.VecT2.fromElemE' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rv64mc.Table.VecT2.fromElemE

/-- info: 'Rv64mc.Table.VecT2.fromElemOptionE' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rv64mc.Table.VecT2.fromElemOptionE

/-- info: 'Rv64mc.Table.VecT2.fromIterOptionE' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rv64mc.Table.VecT2.fromIterOptionE
