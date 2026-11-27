/-
  Rv64mc.Table.CopyUseT

  The total contracts at the image that wave 1a stated over `compiler_builtins`' `memcpy` (`MemcpySpecT`), with
  that hypothesis discharged by `Table.MemT.memcpyT`.

  ## Main results

  * `memcpy`, `finishGrow`, `digestWords`
-/

import Rv64mc.Table.MemT
import Rv64mc.Table.RuntimeT
import Rv64mc.Table.DigestT

namespace Rv64mc.Table.CopyUseT

open MachineChecked.RiscV.Lift Rv64mc.Gen Rv64mc.Proof.Runtime Rv64mc.Proof.Hash

variable (env : Env)

/-- **The C `memcpy` wrapper at the image** (function 227). -/
theorem memcpy : MemcpyT.MemcpySpecT env (liftProg fns) Idx.Memcpy Needs.Memcpy :=
  RuntimeT.memcpy env (MemT.memcpyT env)

/-- **`finish_grow` at the image** (function 41), over `alloc`'s two environment facts. -/
theorem finishGrow (hnext : VerifierRv64.Bump.AsGlobalAlloc.Alloc.link.d_NEXT.addr = env.nextAddr)
    (hend : env.heapEnd = 0x78000000#64) :
    FinishGrowT.FinishGrowSpecT env (liftProg fns) Idx.Alloc.RawVec.RawVecInner.FinishGrow
      Needs.Alloc.RawVec.RawVecInner.FinishGrow :=
  RuntimeT.finishGrow env hnext hend (MemT.memcpyT env)

/-- **`Digest::words` at the image** (function 144). -/
theorem digestWords :
    DigestWordsT.specT env (liftProg fns) Idx.Verifier.Hash.Digest.Words Needs.Verifier.Hash.Digest.Words :=
  DigestT.digestWords env (MemT.memcpyT env)

/-- info: 'Rv64mc.Table.CopyUseT.memcpy' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms memcpy
/-- info: 'Rv64mc.Table.CopyUseT.finishGrow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms finishGrow
/-- info: 'Rv64mc.Table.CopyUseT.digestWords' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms digestWords

end Rv64mc.Table.CopyUseT
