/-
  Rv64mc.Table.FlushesT6g

  `Flushes::memory` (`MemoryT`) at the image (`liftProg Gen.fns`), over `constant`, `col` (`FormT6e`) and `counted`
  (`FlushesT6e.counted`). Left as hypotheses, environment facts: `alloc`'s two (`RuntimeT.alloc`), `clmul_low`'s
  constant (`FieldT.ClmulTable`, through `col`), and `concat`'s and `spec_extend`'s bounds' words in the static data
  (`DataRef.InData`, through `counted`).

  ## Main results

  * `memory`
-/

import Rv64mc.Table.FlushesT6e
import Rv64mc.Proof.Layout.MemoryT

namespace Rv64mc.Table.FlushesT6g

open MachineChecked.RiscV.Lift Rv64mc.Gen Rv64mc.Proof.Layout

variable (env : Env) (hnext : VerifierRv64.Bump.AsGlobalAlloc.Alloc.link.d_NEXT.addr = env.nextAddr)
  (hend : env.heapEnd = 0x78000000#64)
include hnext hend

/-- **`Flushes::memory` at the image** (function 197). -/
theorem memory (hd : FieldT.ClmulTable env)
    (hdc : DataRef.InData env [(Alloc.Slice.SliceRefSliceForm.AsConcatForm.Concat.link.d_c8_d6dfd6bc,
      Alloc.Slice.SliceRefSliceForm.AsConcatForm.Concat.d_c8_d6dfd6bc_words)])
    (hds : DataRef.InData env
      [(Alloc.Vec.SpecExtend.VecForm.AsSpecExtendRefFormIterForm.SpecExtend.link.d_c8_51ab739d,
        Alloc.Vec.SpecExtend.VecForm.AsSpecExtendRefFormIterForm.SpecExtend.d_c8_51ab739d_words)]) :
    MemoryT.SpecT env (liftProg fns) Idx.Verifier.Layout.Flushes.Memory Needs.Verifier.Layout.Flushes.Memory :=
  MemoryT.total env _ _ _ Verifier.Layout.Flushes.Memory.tmpl_eq Verifier.Layout.Flushes.Memory.wf
    (by decide) (by decide) (by decide) (FormT6e.constantAl env hnext hend) (FormT6e.colAl env hnext hend hd)
    (FlushesT6e.counted env hnext hend hd hdc hds)

end Rv64mc.Table.FlushesT6g

/-- info: 'Rv64mc.Table.FlushesT6g.memory' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rv64mc.Table.FlushesT6g.memory
