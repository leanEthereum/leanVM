/-
  Rv64mc.Table.BusT2

  `verify_bus_balance::{closure#2}`'s total contract at the image (`liftProg Gen.fns`), with the generated link, the
  stack `Gen.Needs` gives and its callees' total theorems (`RuntimeT.alloc`, `LayoutT.gpow`, `DotT2.dotOwn`
  and the panics). Left as hypotheses: the allocator's two facts (`NEXT`'s data reference and the heap's end) and
  `clmul_low`'s constant in the image's static data (`FieldT.ClmulTable`), environment facts.

  ## Main results

  * `framework`
-/

import Rv64mc.Table.LayoutT
import Rv64mc.Table.DotT2
import Rv64mc.Proof.Bus.FrameworkT
import Rv64mc.Gen.Link.Verifier.Bus

namespace Rv64mc.Table.BusT2

open MachineChecked.RiscV.Lift Rv64mc.Gen Rv64mc.Proof.Bus

variable (env : Env)

theorem framework (hnext : VerifierRv64.Bump.AsGlobalAlloc.Alloc.link.d_NEXT.addr = env.nextAddr)
    (hend : env.heapEnd = 0x78000000#64) (hd : FieldT.ClmulTable env) :
    FrameworkT.specT env (liftProg fns) Idx.Verifier.Bus.VerifyBusBalance.Closure2
      Needs.Verifier.Bus.VerifyBusBalance.Closure2 :=
  FrameworkT.total env _ _ _ Verifier.Bus.VerifyBusBalance.Closure2.tmpl_eq
    Verifier.Bus.VerifyBusBalance.Closure2.wf (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (RuntimeT.alloc env hnext hend) (LayoutT.gpow env hd) (DotT2.dotOwn env hd)
    (RuntimeT.panicNounwindFmt env) (RuntimeT.sliceIndexFail env) (RuntimeT.panicBoundsCheck env)

end Rv64mc.Table.BusT2

/-- info: 'Rv64mc.Table.BusT2.framework' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rv64mc.Table.BusT2.framework
