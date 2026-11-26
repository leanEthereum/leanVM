/-
  Rv64mc.Table.VecT

  Total contracts at the image (`liftProg Gen.fns`) that state the bytes a vector's buffer starts with:
  `compiler_builtins`' `memset` and the C wrapper with `SetPost` (`MemsetBytesT`), and the verifier's
  `try_allocate_in` with `TryAllocPost`'s zeroed bytes (`TryAllocateInZT`), each at its index with the generated
  link, the stack `Gen.Needs` gives, and its callees' total theorems. Left as hypotheses, as in `RuntimeT`: the
  environment's two facts about the image that `alloc` reads. Also the drops over a vector's elements
  (`DropSliceT`), `<Vec<T> as Clone>::clone` for `usize` and `E` (`CloneT`) and `verify_bus_balance`'s
  `ColumnClaim` builder (`Proof/Bus/ColumnClaimT`) and `Vec<ColumnClaim>::from` (`Proof/Bus/ClaimsFromT`).

  ## Main results

  * `memsetBuiltin`, `memset`, `tryAllocateIn`, `dropVecVecForm`, `dropVecBusBlock`, `cloneUsize`, `cloneE`,
    `columnClaim`, `claimsFrom`
-/

import Rv64mc.Table.RuntimeT
import Rv64mc.Table.CopyUseT
import Rv64mc.Proof.Runtime.CloneT
import Rv64mc.Proof.Bus.ColumnClaimT
import Rv64mc.Proof.Bus.ClaimsFromT
import Rv64mc.Gen.Link.Verifier.Bus
import Rv64mc.Proof.Runtime.MemsetBytesT
import Rv64mc.Proof.Runtime.TryAllocateInZT
import Rv64mc.Proof.Runtime.DropSliceT

namespace Rv64mc.Table.VecT

open MachineChecked.RiscV.Lift Rv64mc.Gen Rv64mc.Proof.Runtime
open Rv64mc.Proof.Runtime.MemsetBytesT (MemsetSpecT)
open Rv64mc.Proof.Runtime.TryAllocateInZT (TryAllocSpecZT)
open Rv64mc.Proof.Runtime.DropSliceT (DropSliceSpecT)
open Rv64mc.Proof.Runtime.CloneT (CloneSpecT)
open Rv64mc.Proof.Bus.ColumnClaimT (ClaimSpecT)
open Rv64mc.Proof.Bus.ClaimsFromT (FromSpecT)

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

theorem dropVecVecForm :
    DropSliceSpecT env 24 (liftProg fns) Idx.Core.Ptr.DropGlueVecVecForm Needs.Core.Ptr.DropGlueVecVecForm :=
  DropSliceT.vecVecForm_total env _ _ Core.Ptr.DropGlueVecVecForm.link Core.Ptr.DropGlueVecVecForm.tmpl_eq
    Core.Ptr.DropGlueVecVecForm.wf (by decide) (RuntimeT.dropVecForm env)

theorem dropVecBusBlock :
    DropSliceSpecT env 48 (liftProg fns) Idx.Core.Ptr.DropGlueVecBusBlock Needs.Core.Ptr.DropGlueVecBusBlock :=
  DropSliceT.vecBusBlock_total env _ _ Core.Ptr.DropGlueVecBusBlock.link Core.Ptr.DropGlueVecBusBlock.tmpl_eq
    Core.Ptr.DropGlueVecBusBlock.wf (by decide) (RuntimeT.dropVecForm env)

section Alloc

variable (hnext : VerifierRv64.Bump.AsGlobalAlloc.Alloc.link.d_NEXT.addr = env.nextAddr)
  (hend : env.heapEnd = 0x78000000#64)
include hnext hend

theorem cloneUsize :
    CloneSpecT env 8 (liftProg fns) Idx.Alloc.Vec.VecUsize.AsClone.Clone Needs.Alloc.Vec.VecUsize.AsClone.Clone :=
  CloneT.usize_total env _ _ Alloc.Vec.VecUsize.AsClone.Clone.link Alloc.Vec.VecUsize.AsClone.Clone.tmpl_eq
    Alloc.Vec.VecUsize.AsClone.Clone.wf (by decide) (by decide) (by decide) (RuntimeT.alloc env hnext hend)
    (CopyUseT.memcpy env) (RuntimeT.handleError env)

theorem cloneE :
    CloneSpecT env 16 (liftProg fns) Idx.Alloc.Vec.VecE.AsClone.Clone Needs.Alloc.Vec.VecE.AsClone.Clone :=
  CloneT.e_total env _ _ Alloc.Vec.VecE.AsClone.Clone.link Alloc.Vec.VecE.AsClone.Clone.tmpl_eq
    Alloc.Vec.VecE.AsClone.Clone.wf (by decide) (by decide) (by decide) (RuntimeT.alloc env hnext hend)
    (CopyUseT.memcpy env) (RuntimeT.handleError env)

theorem columnClaim :
    ClaimSpecT env (liftProg fns) Idx.Verifier.Bus.VerifyBusBalance.Closure0
      Needs.Verifier.Bus.VerifyBusBalance.Closure0 :=
  Proof.Bus.ColumnClaimT.total env _ _ Verifier.Bus.VerifyBusBalance.Closure0.link
    Verifier.Bus.VerifyBusBalance.Closure0.tmpl_eq Verifier.Bus.VerifyBusBalance.Closure0.wf (by decide) (by decide)
    (by decide) (RuntimeT.alloc env hnext hend) (CopyUseT.memcpy env) (RuntimeT.handleError env)

theorem claimsFrom :
    FromSpecT env (liftProg fns) Idx.Alloc.Vec.VecColumnClaim.AsFromArrColumnClaimN2.From
      Needs.Alloc.Vec.VecColumnClaim.AsFromArrColumnClaimN2.From :=
  Proof.Bus.ClaimsFromT.total env _ _ Alloc.Vec.VecColumnClaim.AsFromArrColumnClaimN2.From.link
    Alloc.Vec.VecColumnClaim.AsFromArrColumnClaimN2.From.tmpl_eq Alloc.Vec.VecColumnClaim.AsFromArrColumnClaimN2.From.wf
    (by decide) (by decide) (by decide) (RuntimeT.alloc env hnext hend) (CopyUseT.memcpy env)
    (RuntimeT.panicNounwindFmt env)

end Alloc

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

/-- info: 'Rv64mc.Table.VecT.dropVecVecForm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rv64mc.Table.VecT.dropVecVecForm

/-- info: 'Rv64mc.Table.VecT.dropVecBusBlock' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rv64mc.Table.VecT.dropVecBusBlock

/-- info: 'Rv64mc.Table.VecT.cloneUsize' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rv64mc.Table.VecT.cloneUsize

/-- info: 'Rv64mc.Table.VecT.cloneE' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rv64mc.Table.VecT.cloneE

/-- info: 'Rv64mc.Table.VecT.columnClaim' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rv64mc.Table.VecT.columnClaim

/-- info: 'Rv64mc.Table.VecT.claimsFrom' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rv64mc.Table.VecT.claimsFrom
