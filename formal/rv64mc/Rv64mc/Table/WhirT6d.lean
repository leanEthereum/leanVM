/-
  Rv64mc.Table.WhirT6d

  The ring switch's and WHIR's total contracts of wave 6d at the image (`liftProg Gen.fns`): each function's total
  theorem at its index, with the generated link, the stack `Gen.Needs` gives (its bound over each callee's by
  `decide`), and its callees' total theorems (`ring_coefficients`: `AllocT.reserveE`, `RuntimeT.alloc`,
  `RuntimeT.handleError`, `FieldT.eMul`, `WhirT.frobenius8`, `CopyUseT.memcpy`). Left as hypotheses: `clmul_low`'s
  constant table (`FieldT.ClmulTable`, through `E::mul`) and the allocator's two facts (`NEXT`'s data reference and
  the heap's end), all environment facts.

  ## Main results

  * `ringCoefficients`
-/

import Rv64mc.Table.RuntimeT
import Rv64mc.Table.FieldT
import Rv64mc.Table.WhirT
import Rv64mc.Table.AllocT
import Rv64mc.Table.CopyUseT
import Rv64mc.Proof.Whir.RingCoefficientsT
import Rv64mc.Gen.Link.Verifier.RingSwitch

namespace Rv64mc.Table.WhirT6d

open MachineChecked.RiscV.Lift Rv64mc.Gen Rv64mc.Proof.Whir

variable (env : Env)

/-- `ring_coefficients`. -/
theorem ringCoefficients (hd : FieldT.ClmulTable env)
    (hnext : VerifierRv64.Bump.AsGlobalAlloc.Alloc.link.d_NEXT.addr = env.nextAddr)
    (hend : env.heapEnd = 0x78000000#64) :
    RingCoefficientsT.specT env (liftProg fns) Idx.Verifier.RingSwitch.RingCoefficients
      Needs.Verifier.RingSwitch.RingCoefficients :=
  RingCoefficientsT.total env _ _ _ Verifier.RingSwitch.RingCoefficients.tmpl_eq
    Verifier.RingSwitch.RingCoefficients.wf
    (needR := Needs.Alloc.Vec.VecE.Reserve) (needA := Needs.VerifierRv64.Bump.AsGlobalAlloc.Alloc)
    (needH := Needs.Alloc.RawVec.HandleError) (needU := Needs.Verifier.Field.E.AsMul.Mul)
    (needF := Needs.Verifier.RingSwitch.Frobenius8) (needM := Needs.Memcpy)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (AllocT.reserveE env hnext hend) (RuntimeT.alloc env hnext hend) (RuntimeT.handleError env)
    (FieldT.eMul env hd) (WhirT.frobenius8 env) (CopyUseT.memcpy env)

end Rv64mc.Table.WhirT6d

/-- info: 'Rv64mc.Table.WhirT6d.ringCoefficients' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rv64mc.Table.WhirT6d.ringCoefficients
