/-
  Rv64mc.Table.FlushesT

  `layout.rs`'s `Flushes` builders' total contracts at the image (`liftProg Gen.fns`), new in wave 5a, each at its
  index with the generated link, the stack `Gen.Needs` gives, and its callees' total theorems (`AllocT`). Left as
  hypotheses, environment facts: `alloc`'s two (`RuntimeT.alloc`, through `grow_one`).

  ## Main results

  * `pair`
-/

import Rv64mc.Table.AllocT
import Rv64mc.Proof.Layout.PairT
import Rv64mc.Gen.Link.Verifier.Layout.Flushes

namespace Rv64mc.Table.FlushesT

open MachineChecked.RiscV.Lift Rv64mc.Gen Rv64mc.Proof.Layout

variable (env : Env) (hnext : VerifierRv64.Bump.AsGlobalAlloc.Alloc.link.d_NEXT.addr = env.nextAddr)
  (hend : env.heapEnd = 0x78000000#64)
include hnext hend

/-- **`Flushes::pair` at the image** (function 200). -/
theorem pair :
    PairT.SpecT env (liftProg fns) Idx.Verifier.Layout.Flushes.Pair Needs.Verifier.Layout.Flushes.Pair :=
  PairT.total env _ _ Verifier.Layout.Flushes.Pair.link Verifier.Layout.Flushes.Pair.tmpl_eq
    Verifier.Layout.Flushes.Pair.wf (by decide) (Table.AllocT.growOneVecForm env hnext hend)

end Rv64mc.Table.FlushesT

/-- info: 'Rv64mc.Table.FlushesT.pair' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rv64mc.Table.FlushesT.pair
