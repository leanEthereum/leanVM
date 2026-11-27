/-
  Rv64mc.Table.LayoutT6c

  The total contracts of the layout functions new in wave 6c's second pass at the image (`liftProg Gen.fns`), each at
  its index with the generated link, the stack `Gen.Needs` gives, and its callees' total theorems. Left as
  hypotheses, environment facts only: `alloc`'s two (`RuntimeT.alloc`).

  ## Main results

  * `layoutStack`
-/

import Rv64mc.Table.LayoutT5a
import Rv64mc.Table.MultilinearT5a
import Rv64mc.Proof.Layout.StackT

namespace Rv64mc.Table.LayoutT6c

open MachineChecked.RiscV.Lift Rv64mc.Gen Rv64mc.Proof.Layout

variable (env : Env) (hnext : VerifierRv64.Bump.AsGlobalAlloc.Alloc.link.d_NEXT.addr = env.nextAddr)
  (hend : env.heapEnd = 0x78000000#64)
include hnext hend

/-- **`stack` at the image** (function 182). -/
theorem layoutStack :
    StackT.SpecT env (liftProg fns) Idx.Verifier.Layout.Stack Needs.Verifier.Layout.Stack :=
  StackT.total env _ _ Verifier.Layout.Stack.link Verifier.Layout.Stack.tmpl_eq Verifier.Layout.Stack.wf
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (Table.LayoutT5a.stackedBlocks env hnext hend) (Table.RuntimeT.handleError env) (Table.RuntimeT.alloc env hnext hend)
    (Table.AllocT.reserveUsize env hnext hend) (Table.MultilinearT5a.stackOffsets env hnext hend)
    (Table.AllocT.tryAllocateIn env hnext hend) (Table.RuntimeT.panicBoundsCheck env)

end Rv64mc.Table.LayoutT6c

/-- info: 'Rv64mc.Table.LayoutT6c.layoutStack' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rv64mc.Table.LayoutT6c.layoutStack
