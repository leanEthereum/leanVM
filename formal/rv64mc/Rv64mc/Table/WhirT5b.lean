/-
  Rv64mc.Table.WhirT5b

  The WHIR functions' total contracts of wave 5b at the image (`liftProg Gen.fns`): each function's total theorem at
  its index, with the generated link, the stack `Gen.Needs` gives (its bound over each callee's by `decide`), and its
  callees' total theorems (`derive_config`: `WhirT.whirQueries`, `RuntimeT.alloc`, `AllocT.growOneUsize`,
  `RuntimeT.panicNounwindFmt`). Left as hypotheses: `WHIR_QUERIES`' tables in the image's static data
  (`DataRef.InData`, as `WhirT.whirQueries` takes them) and the allocator's two facts (`NEXT`'s data reference and the
  heap's end), environment facts.

  ## Main results

  * `deriveConfig`
-/

import Rv64mc.Table.WhirT
import Rv64mc.Table.AllocT
import Rv64mc.Table.RuntimeT
import Rv64mc.Proof.Whir.DeriveConfigT
import Rv64mc.Gen.Link.Verifier.Whir

namespace Rv64mc.Table.WhirT5b

open MachineChecked.RiscV.Lift Rv64mc.Gen Rv64mc.Proof.Whir

variable (env : Env)

/-- `derive_config`. -/
theorem deriveConfig (hdata : DataRef.InData env (Verifier.Whir.WhirQueries.tables Verifier.Whir.WhirQueries.link))
    (hnext : VerifierRv64.Bump.AsGlobalAlloc.Alloc.link.d_NEXT.addr = env.nextAddr)
    (hend : env.heapEnd = 0x78000000#64) :
    DeriveConfigT.specT env (liftProg fns) Idx.Verifier.Whir.DeriveConfig Needs.Verifier.Whir.DeriveConfig :=
  DeriveConfigT.total env _ _ _ Verifier.Whir.DeriveConfig.tmpl_eq Verifier.Whir.DeriveConfig.wf
    (needQ := Needs.Verifier.Whir.WhirQueries) (needA := Needs.VerifierRv64.Bump.AsGlobalAlloc.Alloc)
    (needG := Needs.Alloc.RawVec.RawVecUsize.GrowOne) (needP := Needs.Core.Panicking.PanicNounwindFmt)
    (by decide) (by decide) (by decide) (by decide) (WhirT.whirQueries env hdata) (RuntimeT.alloc env hnext hend)
    (AllocT.growOneUsize env hnext hend) (RuntimeT.panicNounwindFmt env)

end Rv64mc.Table.WhirT5b

/-- info: 'Rv64mc.Table.WhirT5b.deriveConfig' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rv64mc.Table.WhirT5b.deriveConfig
