/-
  Rv64mc.Table.FlushesT6e

  `Flushes::pair` over a `Flushes` of `Form`s (`PairFormT`) at the image (`liftProg Gen.fns`), from its total
  contract there (`FlushesT.pair`). Left as hypotheses, environment facts: `alloc`'s two (`RuntimeT.alloc`, through
  `grow_one`).

  ## Main results

  * `pairForm`
-/

import Rv64mc.Table.FlushesT
import Rv64mc.Proof.Layout.PairFormT

namespace Rv64mc.Table.FlushesT6e

open MachineChecked.RiscV.Lift Rv64mc.Gen Rv64mc.Proof.Layout

variable (env : Env) (hnext : VerifierRv64.Bump.AsGlobalAlloc.Alloc.link.d_NEXT.addr = env.nextAddr)
  (hend : env.heapEnd = 0x78000000#64)
include hnext hend

/-- **`Flushes::pair` at the image** (function 200), keeping a `Flushes` of `Form`s. -/
theorem pairForm :
    PairFormT.SpecT env (liftProg fns) Idx.Verifier.Layout.Flushes.Pair Needs.Verifier.Layout.Flushes.Pair :=
  PairFormT.SpecT.of_pairT (FlushesT.pair env hnext hend)

end Rv64mc.Table.FlushesT6e

/-- info: 'Rv64mc.Table.FlushesT6e.pairForm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rv64mc.Table.FlushesT6e.pairForm
