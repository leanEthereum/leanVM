/-
  Rv64mc.Table.Keccak

  The Keccak GKR family's proved contracts at the image (`liftProg Gen.fns`): each `ok` at its function's index
  (`Rv64mc/Gen/index.tsv`), with the generated link (`tmpl_eq`, `wf`), from the runtime's contracts
  (`Table.Runtime`) and, as hypotheses, what is not proved yet: `compiler_builtins`' `memset` under the C wrapper,
  `Vec<E>::reserve`, and the constant tables (`DataRef.Words`, which the image's `env.data` gives through
  `DataRef.Words.of_data`; `KECCAK_RHO` as `u32`s, `RhoAt`).

  `linear_transpose`'s stack is stated here, not read from `Gen.Needs`: its frame is `2032` bytes by `addi` and
  `28784` more by `sub sp, sp, a3`, which `Needs` does not count.
-/

import Rv64mc.Proof.Keccak.LinearTranspose
import Rv64mc.Table.Runtime
import Rv64mc.Gen.Link.Verifier.Keccak.LinearTransposeE

namespace Rv64mc.Table.Keccak

open MachineChecked.RiscV.Lift Rv64mc.Gen Rv64mc.Spec.Runtime

variable (env : Env)

/-- The stack `linear_transpose` needs: its frame and the most its callees need. -/
def linearTransposeNeed : Nat :=
  30816 + max Needs.Memset (max Needs.VerifierRv64.Bump.AsGlobalAlloc.Alloc (max Needs.Alloc.Vec.VecE.Reserve
    (max Needs.Core.Panicking.PanicBoundsCheck (max Needs.Core.Panicking.AssertFailedUsizeUsize
      Needs.Alloc.RawVec.HandleError))))

theorem linearTranspose
    (hnext : VerifierRv64.Bump.AsGlobalAlloc.Alloc.link.d_NEXT.addr = env.nextAddr)
    (hend : env.heapEnd = 0x78000000#64)
    (hms : MemsetSpec env (liftProg fns) 224 Needs.CompilerBuiltins.Mem.Memset)
    (hres : ReserveSpec env 8 16 (liftProg fns) 38 Needs.Alloc.Vec.VecE.Reserve)
    (hpi : DataRef.Words env Verifier.Keccak.LinearTransposeE.link.d_c200_f4afdee4
      Verifier.Keccak.LinearTransposeE.d_c200_f4afdee4_words)
    (hrho : Proof.Keccak.LinearTranspose.RhoAt env Verifier.Keccak.LinearTransposeE.link.d_c100_179d68cc)
    (hmagic : DataRef.Words env Verifier.Keccak.LinearTransposeE.link.d_c8_e5d50e4a
      Verifier.Keccak.LinearTransposeE.d_c8_e5d50e4a_words) :
    Spec.Keccak.LinearTranspose.spec env (liftProg fns) 36 linearTransposeNeed :=
  Proof.Keccak.LinearTranspose.ok env _ 36 _ Verifier.Keccak.LinearTransposeE.tmpl_eq
    Verifier.Keccak.LinearTransposeE.wf (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (Runtime.memset env hms) (Runtime.alloc env hnext hend) hres (Runtime.panicBoundsCheck env)
    (Runtime.assertFailedUsizeUsize env) (Runtime.handleError env) hpi hrho hmagic

end Rv64mc.Table.Keccak

/-- info: 'Rv64mc.Table.Keccak.linearTranspose' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rv64mc.Table.Keccak.linearTranspose
