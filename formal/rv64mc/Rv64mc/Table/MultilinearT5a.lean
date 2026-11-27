/-
  Rv64mc.Table.MultilinearT5a

  `multilinear.rs`'s total contracts at the image (`liftProg Gen.fns`) new in wave 5a, each at its index with the
  generated link, the stack `Gen.Needs` gives, and its callees' total theorems (`AllocT`, `RuntimeT`). Left as
  hypotheses, environment facts: `alloc`'s two (`RuntimeT.alloc`).

  ## Main results

  * `stackOffsets`
-/

import Rv64mc.Table.AllocT
import Rv64mc.Proof.Multilinear.StackOffsetsT
import Rv64mc.Gen.Link.Verifier.Multilinear

namespace Rv64mc.Table.MultilinearT5a

open MachineChecked.RiscV.Lift Rv64mc.Gen Rv64mc.Proof.Multilinear

variable (env : Env) (hnext : VerifierRv64.Bump.AsGlobalAlloc.Alloc.link.d_NEXT.addr = env.nextAddr)
  (hend : env.heapEnd = 0x78000000#64)
include hnext hend

/-- **`stack_offsets` at the image** (function 174). -/
theorem stackOffsets :
    StackOffsetsT.SpecT env (liftProg fns) Idx.Verifier.Multilinear.StackOffsets
      Needs.Verifier.Multilinear.StackOffsets :=
  StackOffsetsT.total env _ _ Verifier.Multilinear.StackOffsets.link Verifier.Multilinear.StackOffsets.tmpl_eq
    Verifier.Multilinear.StackOffsets.wf (by decide) (by decide) (by decide)
    (Table.AllocT.tryAllocateIn env hnext hend) (Table.RuntimeT.panicBoundsCheck env) (Table.RuntimeT.handleError env)

end Rv64mc.Table.MultilinearT5a

/-- info: 'Rv64mc.Table.MultilinearT5a.stackOffsets' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rv64mc.Table.MultilinearT5a.stackOffsets
