/-
  Rv64mc.Table.KeccakT

  `linear_transpose::<E>`'s total contract at the image (`liftProg Gen.fns`), at its index with the generated link,
  the stack `Gen.Needs` gives, and its callees' total theorems in `VecT` (`memset` with its bytes), `RuntimeT` and
  `AllocT`. Left as hypotheses: the environment's two facts about the image that `alloc` reads, and its three
  constant tables in the static data (`DataRef.InData`), with `KECCAK_RHO` also as `u32`s (`RhoAt`, as the partial
  `Table/Keccak.lean` has it).

  ## Main results

  * `linearTranspose`
-/

import Rv64mc.Table.VecT
import Rv64mc.Table.AllocT
import Rv64mc.Proof.Keccak.LinearTransposeT
import Rv64mc.Gen.Link.Verifier.Keccak

namespace Rv64mc.Table.KeccakT

open MachineChecked.RiscV.Lift Rv64mc.Gen Rv64mc.Proof.Runtime Rv64mc.Proof.Keccak

variable (env : Env) (hnext : VerifierRv64.Bump.AsGlobalAlloc.Alloc.link.d_NEXT.addr = env.nextAddr)
  (hend : env.heapEnd = 0x78000000#64)
include hnext hend

/-- **`linear_transpose` at the image** (function 36). -/
theorem linearTranspose
    (hpi : DataRef.InData env [(Verifier.Keccak.LinearTransposeE.link.d_c200_f4afdee4,
      Verifier.Keccak.LinearTransposeE.d_c200_f4afdee4_words)])
    (hrhoD : DataRef.InData env [(Verifier.Keccak.LinearTransposeE.link.d_c100_179d68cc,
      Verifier.Keccak.LinearTransposeE.d_c100_179d68cc_words)])
    (hrho : LinearTranspose.RhoAt env Verifier.Keccak.LinearTransposeE.link.d_c100_179d68cc)
    (hmagic : DataRef.InData env [(Verifier.Keccak.LinearTransposeE.link.d_c8_e5d50e4a,
      Verifier.Keccak.LinearTransposeE.d_c8_e5d50e4a_words)]) :
    LinearTransposeT.SpecT env (liftProg fns) Idx.Verifier.Keccak.LinearTransposeE
      Needs.Verifier.Keccak.LinearTransposeE :=
  LinearTransposeT.total env _ _ Verifier.Keccak.LinearTransposeE.link Verifier.Keccak.LinearTransposeE.tmpl_eq
    Verifier.Keccak.LinearTransposeE.wf (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (Table.VecT.memset env) (RuntimeT.alloc env hnext hend) (AllocT.reserveE env hnext hend)
    (RuntimeT.panicBoundsCheck env) (RuntimeT.assertFailedUsizeUsize env) (RuntimeT.handleError env)
    hpi hrhoD hrho hmagic

end Rv64mc.Table.KeccakT

/-- info: 'Rv64mc.Table.KeccakT.linearTranspose' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rv64mc.Table.KeccakT.linearTranspose

/-- info: 'Rv64mc.Proof.Keccak.LinearTransposeT.total' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rv64mc.Proof.Keccak.LinearTransposeT.total
