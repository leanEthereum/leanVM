/-
  Rv64mc.Table.BuildT

  Wave 4a's vector builders' total contracts at the image (`liftProg Gen.fns`), each at its index with the generated
  link, the stack `Gen.Needs` gives, and its callees' total theorems in `RuntimeT`, `AllocT` and `CopyUseT`. Left
  as hypotheses, as in `RuntimeT`: the environment's two facts about the image that `alloc` reads, and
  `clmul_low`'s table where a builder multiplies (`FieldT.ClmulTable`), and the static data words a builder reads
  (`DataRef.InData`).

  ## Main results

  * `specExtendE`, `fromIterE`, `tryMapClaims`, `tryFromFnLanes`
-/

import Rv64mc.Table.AllocT
import Rv64mc.Table.CopyUseT
import Rv64mc.Table.FieldT
import Rv64mc.Proof.Runtime.SpecExtendT
import Rv64mc.Proof.Runtime.FromIterET
import Rv64mc.Proof.Bus.TryMapT
import Rv64mc.Proof.Keccak.TryFromFnT

namespace Rv64mc.Table.BuildT

open MachineChecked.RiscV.Lift Rv64mc.Gen Rv64mc.Proof Rv64mc.Proof.Runtime

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

/-- **`Vec<E>`'s `spec_from_iter_nested` over `verify_layer`'s products at the image** (function 143). -/
theorem fromIterE (hd : FieldT.ClmulTable env) :
    FromIterET.SpecT env (liftProg fns) Idx.Alloc.Vec.SpecFromIterNested.VecE.AsSpecFromIterNestedEMapH4a41f075.FromIter
      Needs.Alloc.Vec.SpecFromIterNested.VecE.AsSpecFromIterNestedEMapH4a41f075.FromIter :=
  FromIterET.total env _ _ Alloc.Vec.SpecFromIterNested.VecE.AsSpecFromIterNestedEMapH4a41f075.FromIter.link
    Alloc.Vec.SpecFromIterNested.VecE.AsSpecFromIterNestedEMapH4a41f075.FromIter.tmpl_eq
    Alloc.Vec.SpecFromIterNested.VecE.AsSpecFromIterNestedEMapH4a41f075.FromIter.wf
    (by decide) (by decide) (by decide) (by decide) (by decide)
    (RuntimeT.alloc env hnext hend) (AllocT.reserveE env hnext hend) (RuntimeT.handleError env)
    (FieldT.eMul env hd) (RuntimeT.panicBoundsCheck env)

/-- **`<[usize; 2]>::try_map` with `verify_bus_balance`'s claim closure at the image** (function 153). -/
theorem tryMapClaims :
    Bus.TryMapT.SpecT env (liftProg fns) Idx.Core.Array.ArrUsizeN2.TryMapNeverShortCircuitCH2be087e3
      Needs.Core.Array.ArrUsizeN2.TryMapNeverShortCircuitCH2be087e3 :=
  Bus.TryMapT.total env _ _ Core.Array.ArrUsizeN2.TryMapNeverShortCircuitCH2be087e3.link
    Core.Array.ArrUsizeN2.TryMapNeverShortCircuitCH2be087e3.tmpl_eq
    Core.Array.ArrUsizeN2.TryMapNeverShortCircuitCH2be087e3.wf (by decide) (by decide) (by decide) (by decide)
    (RuntimeT.alloc env hnext hend) (CopyUseT.memcpy env) (RuntimeT.handleError env) (RuntimeT.panicBoundsCheck env)

omit hnext hend in
/-- **`try_from_fn` building `verify_layer`'s lane weights at the image** (function 142). -/
theorem tryFromFnLanes (hd : FieldT.ClmulTable env)
    (hdat : DataRef.InData env [(Core.Array.TryFromFnNeverShortCircuHc949fc7d.link.d_c8_e5d50e4a,
      Core.Array.TryFromFnNeverShortCircuHc949fc7d.d_c8_e5d50e4a_words)]) :
    Keccak.TryFromFnT.SpecT env (liftProg fns) Idx.Core.Array.TryFromFnNeverShortCircuHc949fc7d
      Needs.Core.Array.TryFromFnNeverShortCircuHc949fc7d :=
  Keccak.TryFromFnT.total env _ _ Core.Array.TryFromFnNeverShortCircuHc949fc7d.link
    Core.Array.TryFromFnNeverShortCircuHc949fc7d.tmpl_eq Core.Array.TryFromFnNeverShortCircuHc949fc7d.wf hdat
    (by decide) (by decide) (by decide) (FieldT.eMul env hd) (RuntimeT.panicBoundsCheck env) (CopyUseT.memcpy env)

end Rv64mc.Table.BuildT

/-- info: 'Rv64mc.Table.BuildT.specExtendE' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rv64mc.Table.BuildT.specExtendE

/-- info: 'Rv64mc.Table.BuildT.fromIterE' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rv64mc.Table.BuildT.fromIterE

/-- info: 'Rv64mc.Table.BuildT.tryMapClaims' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rv64mc.Table.BuildT.tryMapClaims

/-- info: 'Rv64mc.Table.BuildT.tryFromFnLanes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rv64mc.Table.BuildT.tryFromFnLanes
