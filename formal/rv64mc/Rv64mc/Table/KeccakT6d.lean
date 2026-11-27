/-
  Rv64mc.Table.KeccakT6d

  The Keccak verifier's total contracts of wave 6d at the image (`liftProg Gen.fns`): `instance_weights`'s total
  theorem at its index, with the generated link, the stack `Gen.Needs` gives (its bound over each callee's by
  `decide`), and its callees' total theorems (`FieldT.eMul`, `RuntimeT.alloc`, `RuntimeT.handleError`,
  `AllocT.reserveE`, `SumT.eSumEmbedBits`). Left as hypotheses: the table `RMFE_EMBED` in the static data
  (`DataRef.InData`), `clmul_low`'s constant table (`FieldT.ClmulTable`, through `E::mul`) and the allocator's two
  facts (`NEXT`'s data reference and the heap's end), all environment facts.

  ## Main results

  * `instanceWeights`
-/

import Rv64mc.Table.RuntimeT
import Rv64mc.Table.FieldT
import Rv64mc.Table.AllocT
import Rv64mc.Table.SumT
import Rv64mc.Proof.Keccak.InstanceWeightsT
import Rv64mc.Gen.Link.Verifier.Keccak

namespace Rv64mc.Table.KeccakT6d

open MachineChecked.RiscV.Lift Rv64mc.Gen Rv64mc.Proof.Keccak

variable (env : Env)

/-- `instance_weights`. -/
theorem instanceWeights (hd : FieldT.ClmulTable env)
    (hemb : DataRef.InData env [(Verifier.Keccak.InstanceWeights.link.d_c64_a72ced70,
      Verifier.Keccak.InstanceWeights.d_c64_a72ced70_words)])
    (hnext : VerifierRv64.Bump.AsGlobalAlloc.Alloc.link.d_NEXT.addr = env.nextAddr)
    (hend : env.heapEnd = 0x78000000#64) :
    InstanceWeightsT.specT env (liftProg fns) Idx.Verifier.Keccak.InstanceWeights
      Needs.Verifier.Keccak.InstanceWeights :=
  InstanceWeightsT.total env _ _ _ Verifier.Keccak.InstanceWeights.tmpl_eq Verifier.Keccak.InstanceWeights.wf hemb
    (needU := Needs.Verifier.Field.E.AsMul.Mul) (needA := Needs.VerifierRv64.Bump.AsGlobalAlloc.Alloc)
    (needH := Needs.Alloc.RawVec.HandleError) (needR := Needs.Alloc.Vec.VecE.Reserve)
    (needS := Needs.Verifier.Field.E.SumMapFilterRangeUsizeInHbf23f0ea)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    (FieldT.eMul env hd) (RuntimeT.alloc env hnext hend) (RuntimeT.handleError env) (AllocT.reserveE env hnext hend)
    (SumT.eSumEmbedBits env)

end Rv64mc.Table.KeccakT6d

/-- info: 'Rv64mc.Table.KeccakT6d.instanceWeights' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rv64mc.Table.KeccakT6d.instanceWeights
