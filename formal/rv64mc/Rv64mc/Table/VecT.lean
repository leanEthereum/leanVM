/-
  Rv64mc.Table.VecT

  Total contracts at the image (`liftProg Gen.fns`) that state the bytes a vector's buffer starts with:
  `compiler_builtins`' `memset` and the C wrapper with `SetPost` (`MemsetBytesT`), and the verifier's
  `try_allocate_in` with `TryAllocPost`'s zeroed bytes (`TryAllocateInZT`), each at its index with the generated
  link, the stack `Gen.Needs` gives, and its callees' total theorems. Left as hypotheses, as in `RuntimeT`: the
  environment's two facts about the image that `alloc` reads.

  ## Main results

  * `memsetBuiltin`, `memset`, `tryAllocateIn`
-/

import Rv64mc.Table.RuntimeT
import Rv64mc.Proof.Runtime.MemsetBytesT
import Rv64mc.Proof.Runtime.TryAllocateInZT

namespace Rv64mc.Table.VecT

open MachineChecked.RiscV.Lift Rv64mc.Gen Rv64mc.Proof.Runtime
open Rv64mc.Proof.Runtime.MemsetBytesT (MemsetSpecT)
open Rv64mc.Proof.Runtime.TryAllocateInZT (TryAllocSpecZT)

variable (env : Env)

theorem memsetBuiltin :
    MemsetSpecT env (liftProg fns) Idx.CompilerBuiltins.Mem.Memset Needs.CompilerBuiltins.Mem.Memset :=
  HoldsT.mono_need (MemsetBytesT.total _ _ _ CompilerBuiltins.Mem.Memset.tmpl_eq) (Nat.zero_le _)

theorem memset : MemsetSpecT env (liftProg fns) Idx.Memset Needs.Memset :=
  MemsetBytesT.memset_total Memset.link Memset.tmpl_eq Memset.wf (memsetBuiltin env)

theorem tryAllocateIn (hnext : VerifierRv64.Bump.AsGlobalAlloc.Alloc.link.d_NEXT.addr = env.nextAddr)
    (hend : env.heapEnd = 0x78000000#64) :
    TryAllocSpecZT env (liftProg fns) Idx.Alloc.RawVec.RawVecInner.TryAllocateInInVerifier
      Needs.Alloc.RawVec.RawVecInner.TryAllocateInInVerifier :=
  TryAllocateInZT.total env _ _ Alloc.RawVec.RawVecInner.TryAllocateInInVerifier.link
    Alloc.RawVec.RawVecInner.TryAllocateInInVerifier.tmpl_eq Alloc.RawVec.RawVecInner.TryAllocateInInVerifier.wf
    (by decide) (by decide) (RuntimeT.alloc env hnext hend) (memset env)

end Rv64mc.Table.VecT

/-- info: 'Rv64mc.Table.VecT.memsetBuiltin' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rv64mc.Table.VecT.memsetBuiltin

/-- info: 'Rv64mc.Table.VecT.memset' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rv64mc.Table.VecT.memset

/-- info: 'Rv64mc.Table.VecT.tryAllocateIn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rv64mc.Table.VecT.tryAllocateIn
