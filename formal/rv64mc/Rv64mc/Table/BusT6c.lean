/-
  Rv64mc.Table.BusT6c

  `bus_layout`'s total contract at the image (`liftProg Gen.fns`), with the generated link, the stack `Gen.Needs`
  gives and its callees' total theorems. Left as hypotheses, environment facts only: `alloc`'s two
  (`RuntimeT.alloc`).

  ## Main results

  * `busLayout`
-/

import Rv64mc.Table.AllocT
import Rv64mc.Table.MemT
import Rv64mc.Table.MultilinearT5a
import Rv64mc.Proof.Bus.BusLayoutT
import Rv64mc.Gen.Link.Verifier.Bus

namespace Rv64mc.Table.BusT6c

open MachineChecked.RiscV.Lift Rv64mc.Gen Rv64mc.Proof.Bus

variable (env : Env) (hnext : VerifierRv64.Bump.AsGlobalAlloc.Alloc.link.d_NEXT.addr = env.nextAddr)
  (hend : env.heapEnd = 0x78000000#64)
include hnext hend

/-- **`bus_layout` at the image** (function 150). -/
theorem busLayout :
    BusLayoutT.SpecT env (liftProg fns) Idx.Verifier.Bus.BusLayout Needs.Verifier.Bus.BusLayout :=
  BusLayoutT.total env _ _ Verifier.Bus.BusLayout.link Verifier.Bus.BusLayout.tmpl_eq Verifier.Bus.BusLayout.wf
    (by decide) (by decide) (by decide) (by decide) (Table.RuntimeT.memcpy env (Table.MemT.memcpyT env)) (by decide)
    (Table.RuntimeT.splitOffAssertFailed env) (by decide) (Table.MultilinearT5a.stackOffsets env hnext hend)
    (Table.RuntimeT.handleError env) (Table.RuntimeT.alloc env hnext hend) (Table.AllocT.reserveUsize env hnext hend)

end Rv64mc.Table.BusT6c

/-- info: 'Rv64mc.Table.BusT6c.busLayout' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rv64mc.Table.BusT6c.busLayout
