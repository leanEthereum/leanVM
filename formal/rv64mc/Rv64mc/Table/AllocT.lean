/-
  Rv64mc.Table.AllocT

  The vector-growth chain's total contracts at the image (`liftProg Gen.fns`): `finish_grow` with its block aligned,
  `grow_amortized`, the thirteen `RawVec<T>::grow_one`, `do_reserve_and_handle`, the seven `Vec<T>::reserve`,
  `Box::new_uninit` and both `try_allocate_in`, each at its index with the generated link, the stack `Gen.Needs`
  gives, and its callees' total theorems here and in `RuntimeT`. Left as hypotheses, as in `RuntimeT`: the
  environment's two facts about the image that `alloc` reads, and `compiler_builtins`' `memcpy` (`MemcpySpecT`),
  which `finish_grow` calls.

  ## Main results

  * `finishGrowA`, `growAmortized`, `growOne*`, `doReserve`, `reserve*`, `boxNewUninit`, `tryAllocateInRv64`,
    `tryAllocateIn`
-/

import Rv64mc.Table.RuntimeT
import Rv64mc.Proof.Runtime.FinishGrowAT
import Rv64mc.Proof.Runtime.GrowAmortizedT
import Rv64mc.Proof.Runtime.GrowOnesT
import Rv64mc.Proof.Runtime.DoReserveT
import Rv64mc.Proof.Runtime.ReserveT
import Rv64mc.Proof.Runtime.BoxNewUninitT
import Rv64mc.Proof.Runtime.TryAllocateInT

namespace Rv64mc.Table.AllocT

open MachineChecked.RiscV.Lift Rv64mc.Gen Rv64mc.Proof.Runtime
open Rv64mc.Proof.Runtime.MemcpyT (MemcpySpecT)
open Rv64mc.Proof.Runtime.FinishGrowAT (FinishGrowSpecAT)
open Rv64mc.Proof.Runtime.GrowAmortizedT (GrowAmortizedSpecT)
open Rv64mc.Proof.Runtime.GrowOneT (GrowOneSpecT)
open Rv64mc.Proof.Runtime.DoReserveT (DoReserveSpecT)
open Rv64mc.Proof.Runtime.ReserveT (ReserveSpecT)
open Rv64mc.Proof.Runtime.BoxNewUninitT (BoxNewUninitSpecT)
open Rv64mc.Proof.Runtime.TryAllocateInT (TryAllocRv64SpecT TryAllocSpecT)

variable (env : Env)

theorem finishGrowA (hnext : VerifierRv64.Bump.AsGlobalAlloc.Alloc.link.d_NEXT.addr = env.nextAddr)
    (hend : env.heapEnd = 0x78000000#64)
    (hm : MemcpySpecT env (liftProg fns) Idx.CompilerBuiltins.Mem.Memcpy Needs.CompilerBuiltins.Mem.Memcpy) :
    FinishGrowSpecAT env (liftProg fns) Idx.Alloc.RawVec.RawVecInner.FinishGrow
      Needs.Alloc.RawVec.RawVecInner.FinishGrow :=
  FinishGrowAT.total env _ _ Alloc.RawVec.RawVecInner.FinishGrow.link Alloc.RawVec.RawVecInner.FinishGrow.tmpl_eq
    Alloc.RawVec.RawVecInner.FinishGrow.wf (by decide) (by decide) (RuntimeT.alloc env hnext hend)
    (RuntimeT.memcpy env hm)

theorem growAmortized (hnext : VerifierRv64.Bump.AsGlobalAlloc.Alloc.link.d_NEXT.addr = env.nextAddr)
    (hend : env.heapEnd = 0x78000000#64)
    (hm : MemcpySpecT env (liftProg fns) Idx.CompilerBuiltins.Mem.Memcpy Needs.CompilerBuiltins.Mem.Memcpy) :
    GrowAmortizedSpecT env (liftProg fns) Idx.Alloc.RawVec.RawVecInner.GrowAmortized
      Needs.Alloc.RawVec.RawVecInner.GrowAmortized :=
  GrowAmortizedT.total Alloc.RawVec.RawVecInner.GrowAmortized.tmpl_eq Alloc.RawVec.RawVecInner.GrowAmortized.wf
    (finishGrowA env hnext hend hm)

theorem growOneColumnClaim (hnext : VerifierRv64.Bump.AsGlobalAlloc.Alloc.link.d_NEXT.addr = env.nextAddr)
    (hend : env.heapEnd = 0x78000000#64)
    (hm : MemcpySpecT env (liftProg fns) Idx.CompilerBuiltins.Mem.Memcpy Needs.CompilerBuiltins.Mem.Memcpy) :
    GrowOneSpecT env Layouts.ColumnClaim.byteAlign Layouts.ColumnClaim.byteSize (liftProg fns)
      Idx.Alloc.RawVec.RawVecColumnClaim.GrowOne
      Needs.Alloc.RawVec.RawVecColumnClaim.GrowOne :=
  GrowOnesT.columnClaim_total Alloc.RawVec.RawVecColumnClaim.GrowOne.link Alloc.RawVec.RawVecColumnClaim.GrowOne.tmpl_eq
    Alloc.RawVec.RawVecColumnClaim.GrowOne.wf (growAmortized env hnext hend hm)
    (HoldsT.mono_need (RuntimeT.handleError env) (by decide))

theorem growOneE (hnext : VerifierRv64.Bump.AsGlobalAlloc.Alloc.link.d_NEXT.addr = env.nextAddr)
    (hend : env.heapEnd = 0x78000000#64)
    (hm : MemcpySpecT env (liftProg fns) Idx.CompilerBuiltins.Mem.Memcpy Needs.CompilerBuiltins.Mem.Memcpy) :
    GrowOneSpecT env Layouts.E.byteAlign Layouts.E.byteSize (liftProg fns) Idx.Alloc.RawVec.RawVecE.GrowOne
      Needs.Alloc.RawVec.RawVecE.GrowOne :=
  GrowOnesT.e_total Alloc.RawVec.RawVecE.GrowOne.link Alloc.RawVec.RawVecE.GrowOne.tmpl_eq
    Alloc.RawVec.RawVecE.GrowOne.wf (growAmortized env hnext hend hm)
    (HoldsT.mono_need (RuntimeT.handleError env) (by decide))

theorem growOneFoldRound (hnext : VerifierRv64.Bump.AsGlobalAlloc.Alloc.link.d_NEXT.addr = env.nextAddr)
    (hend : env.heapEnd = 0x78000000#64)
    (hm : MemcpySpecT env (liftProg fns) Idx.CompilerBuiltins.Mem.Memcpy Needs.CompilerBuiltins.Mem.Memcpy) :
    GrowOneSpecT env Layouts.FoldRound.byteAlign Layouts.FoldRound.byteSize (liftProg fns)
      Idx.Alloc.RawVec.RawVecFoldRound.GrowOne
      Needs.Alloc.RawVec.RawVecFoldRound.GrowOne :=
  GrowOnesT.foldRound_total Alloc.RawVec.RawVecFoldRound.GrowOne.link Alloc.RawVec.RawVecFoldRound.GrowOne.tmpl_eq
    Alloc.RawVec.RawVecFoldRound.GrowOne.wf (growAmortized env hnext hend hm)
    (HoldsT.mono_need (RuntimeT.handleError env) (by decide))

theorem growOneGluedClaim (hnext : VerifierRv64.Bump.AsGlobalAlloc.Alloc.link.d_NEXT.addr = env.nextAddr)
    (hend : env.heapEnd = 0x78000000#64)
    (hm : MemcpySpecT env (liftProg fns) Idx.CompilerBuiltins.Mem.Memcpy Needs.CompilerBuiltins.Mem.Memcpy) :
    GrowOneSpecT env Layouts.GluedClaim.byteAlign Layouts.GluedClaim.byteSize (liftProg fns)
      Idx.Alloc.RawVec.RawVecGluedClaim.GrowOne
      Needs.Alloc.RawVec.RawVecGluedClaim.GrowOne :=
  GrowOnesT.gluedClaim_total Alloc.RawVec.RawVecGluedClaim.GrowOne.link Alloc.RawVec.RawVecGluedClaim.GrowOne.tmpl_eq
    Alloc.RawVec.RawVecGluedClaim.GrowOne.wf (growAmortized env hnext hend hm)
    (HoldsT.mono_need (RuntimeT.handleError env) (by decide))

theorem growOneK (hnext : VerifierRv64.Bump.AsGlobalAlloc.Alloc.link.d_NEXT.addr = env.nextAddr)
    (hend : env.heapEnd = 0x78000000#64)
    (hm : MemcpySpecT env (liftProg fns) Idx.CompilerBuiltins.Mem.Memcpy Needs.CompilerBuiltins.Mem.Memcpy) :
    GrowOneSpecT env Layouts.K.byteAlign Layouts.K.byteSize (liftProg fns) Idx.Alloc.RawVec.RawVecK.GrowOne
      Needs.Alloc.RawVec.RawVecK.GrowOne :=
  GrowOnesT.k_total Alloc.RawVec.RawVecK.GrowOne.link Alloc.RawVec.RawVecK.GrowOne.tmpl_eq
    Alloc.RawVec.RawVecK.GrowOne.wf (growAmortized env hnext hend hm)
    (HoldsT.mono_need (RuntimeT.handleError env) (by decide))

theorem growOneKVecU16 (hnext : VerifierRv64.Bump.AsGlobalAlloc.Alloc.link.d_NEXT.addr = env.nextAddr)
    (hend : env.heapEnd = 0x78000000#64)
    (hm : MemcpySpecT env (liftProg fns) Idx.CompilerBuiltins.Mem.Memcpy Needs.CompilerBuiltins.Mem.Memcpy) :
    GrowOneSpecT env Layouts.KVecU16.byteAlign Layouts.KVecU16.byteSize (liftProg fns)
      Idx.Alloc.RawVec.RawVecTKVecU16E.GrowOne
      Needs.Alloc.RawVec.RawVecTKVecU16E.GrowOne :=
  GrowOnesT.kVecU16_total Alloc.RawVec.RawVecTKVecU16E.GrowOne.link Alloc.RawVec.RawVecTKVecU16E.GrowOne.tmpl_eq
    Alloc.RawVec.RawVecTKVecU16E.GrowOne.wf (growAmortized env hnext hend hm)
    (HoldsT.mono_need (RuntimeT.handleError env) (by decide))

theorem growOneStackClaim (hnext : VerifierRv64.Bump.AsGlobalAlloc.Alloc.link.d_NEXT.addr = env.nextAddr)
    (hend : env.heapEnd = 0x78000000#64)
    (hm : MemcpySpecT env (liftProg fns) Idx.CompilerBuiltins.Mem.Memcpy Needs.CompilerBuiltins.Mem.Memcpy) :
    GrowOneSpecT env Layouts.StackClaim.byteAlign Layouts.StackClaim.byteSize (liftProg fns)
      Idx.Alloc.RawVec.RawVecTStackWeightEE.GrowOne
      Needs.Alloc.RawVec.RawVecTStackWeightEE.GrowOne :=
  GrowOnesT.stackClaim_total Alloc.RawVec.RawVecTStackWeightEE.GrowOne.link
    Alloc.RawVec.RawVecTStackWeightEE.GrowOne.tmpl_eq
    Alloc.RawVec.RawVecTStackWeightEE.GrowOne.wf (growAmortized env hnext hend hm)
    (HoldsT.mono_need (RuntimeT.handleError env) (by decide))

theorem growOneVecEVecE (hnext : VerifierRv64.Bump.AsGlobalAlloc.Alloc.link.d_NEXT.addr = env.nextAddr)
    (hend : env.heapEnd = 0x78000000#64)
    (hm : MemcpySpecT env (liftProg fns) Idx.CompilerBuiltins.Mem.Memcpy Needs.CompilerBuiltins.Mem.Memcpy) :
    GrowOneSpecT env Layouts.VecEVecE.byteAlign Layouts.VecEVecE.byteSize (liftProg fns)
      Idx.Alloc.RawVec.RawVecTVecEVecEE.GrowOne
      Needs.Alloc.RawVec.RawVecTVecEVecEE.GrowOne :=
  GrowOnesT.vecEVecE_total Alloc.RawVec.RawVecTVecEVecEE.GrowOne.link Alloc.RawVec.RawVecTVecEVecEE.GrowOne.tmpl_eq
    Alloc.RawVec.RawVecTVecEVecEE.GrowOne.wf (growAmortized env hnext hend hm)
    (HoldsT.mono_need (RuntimeT.handleError env) (by decide))

theorem growOneVecUsizeE (hnext : VerifierRv64.Bump.AsGlobalAlloc.Alloc.link.d_NEXT.addr = env.nextAddr)
    (hend : env.heapEnd = 0x78000000#64)
    (hm : MemcpySpecT env (liftProg fns) Idx.CompilerBuiltins.Mem.Memcpy Needs.CompilerBuiltins.Mem.Memcpy) :
    GrowOneSpecT env Layouts.VecUsizeE.byteAlign Layouts.VecUsizeE.byteSize (liftProg fns)
      Idx.Alloc.RawVec.RawVecTVecUsizeEE.GrowOne
      Needs.Alloc.RawVec.RawVecTVecUsizeEE.GrowOne :=
  GrowOnesT.vecUsizeE_total Alloc.RawVec.RawVecTVecUsizeEE.GrowOne.link Alloc.RawVec.RawVecTVecUsizeEE.GrowOne.tmpl_eq
    Alloc.RawVec.RawVecTVecUsizeEE.GrowOne.wf (growAmortized env hnext hend hm)
    (HoldsT.mono_need (RuntimeT.handleError env) (by decide))

theorem growOneU16 (hnext : VerifierRv64.Bump.AsGlobalAlloc.Alloc.link.d_NEXT.addr = env.nextAddr)
    (hend : env.heapEnd = 0x78000000#64)
    (hm : MemcpySpecT env (liftProg fns) Idx.CompilerBuiltins.Mem.Memcpy Needs.CompilerBuiltins.Mem.Memcpy) :
    GrowOneSpecT env 2 2 (liftProg fns) Idx.Alloc.RawVec.RawVecU16.GrowOne
      Needs.Alloc.RawVec.RawVecU16.GrowOne :=
  GrowOnesT.u16_total Alloc.RawVec.RawVecU16.GrowOne.link Alloc.RawVec.RawVecU16.GrowOne.tmpl_eq
    Alloc.RawVec.RawVecU16.GrowOne.wf (growAmortized env hnext hend hm)
    (HoldsT.mono_need (RuntimeT.handleError env) (by decide))

theorem growOneU64 (hnext : VerifierRv64.Bump.AsGlobalAlloc.Alloc.link.d_NEXT.addr = env.nextAddr)
    (hend : env.heapEnd = 0x78000000#64)
    (hm : MemcpySpecT env (liftProg fns) Idx.CompilerBuiltins.Mem.Memcpy Needs.CompilerBuiltins.Mem.Memcpy) :
    GrowOneSpecT env 8 8 (liftProg fns) Idx.Alloc.RawVec.RawVecU64.GrowOne
      Needs.Alloc.RawVec.RawVecU64.GrowOne :=
  GrowOnesT.u64_total Alloc.RawVec.RawVecU64.GrowOne.link Alloc.RawVec.RawVecU64.GrowOne.tmpl_eq
    Alloc.RawVec.RawVecU64.GrowOne.wf (growAmortized env hnext hend hm)
    (HoldsT.mono_need (RuntimeT.handleError env) (by decide))

theorem growOneUsize (hnext : VerifierRv64.Bump.AsGlobalAlloc.Alloc.link.d_NEXT.addr = env.nextAddr)
    (hend : env.heapEnd = 0x78000000#64)
    (hm : MemcpySpecT env (liftProg fns) Idx.CompilerBuiltins.Mem.Memcpy Needs.CompilerBuiltins.Mem.Memcpy) :
    GrowOneSpecT env 8 8 (liftProg fns) Idx.Alloc.RawVec.RawVecUsize.GrowOne
      Needs.Alloc.RawVec.RawVecUsize.GrowOne :=
  GrowOnesT.usize_total Alloc.RawVec.RawVecUsize.GrowOne.link Alloc.RawVec.RawVecUsize.GrowOne.tmpl_eq
    Alloc.RawVec.RawVecUsize.GrowOne.wf (growAmortized env hnext hend hm)
    (HoldsT.mono_need (RuntimeT.handleError env) (by decide))

theorem growOneVecForm (hnext : VerifierRv64.Bump.AsGlobalAlloc.Alloc.link.d_NEXT.addr = env.nextAddr)
    (hend : env.heapEnd = 0x78000000#64)
    (hm : MemcpySpecT env (liftProg fns) Idx.CompilerBuiltins.Mem.Memcpy Needs.CompilerBuiltins.Mem.Memcpy) :
    GrowOneSpecT env Layouts.Vec.byteAlign Layouts.Vec.byteSize (liftProg fns) Idx.Alloc.RawVec.RawVecVecForm.GrowOne
      Needs.Alloc.RawVec.RawVecVecForm.GrowOne :=
  GrowOnesT.vecForm_total Alloc.RawVec.RawVecVecForm.GrowOne.link Alloc.RawVec.RawVecVecForm.GrowOne.tmpl_eq
    Alloc.RawVec.RawVecVecForm.GrowOne.wf (growAmortized env hnext hend hm)
    (HoldsT.mono_need (RuntimeT.handleError env) (by decide))

theorem doReserve (hnext : VerifierRv64.Bump.AsGlobalAlloc.Alloc.link.d_NEXT.addr = env.nextAddr)
    (hend : env.heapEnd = 0x78000000#64)
    (hm : MemcpySpecT env (liftProg fns) Idx.CompilerBuiltins.Mem.Memcpy Needs.CompilerBuiltins.Mem.Memcpy) :
    DoReserveSpecT env (liftProg fns) Idx.Alloc.RawVec.RawVecInnerAny.Reserve.DoReserveAndHandleGlobal
      Needs.Alloc.RawVec.RawVecInnerAny.Reserve.DoReserveAndHandleGlobal :=
  DoReserveT.total env _ _ Alloc.RawVec.RawVecInnerAny.Reserve.DoReserveAndHandleGlobal.link
    Alloc.RawVec.RawVecInnerAny.Reserve.DoReserveAndHandleGlobal.tmpl_eq
    Alloc.RawVec.RawVecInnerAny.Reserve.DoReserveAndHandleGlobal.wf (by decide) (growAmortized env hnext hend hm)
    (HoldsT.mono_need (RuntimeT.handleError env) (by decide))

theorem reserveE (hnext : VerifierRv64.Bump.AsGlobalAlloc.Alloc.link.d_NEXT.addr = env.nextAddr)
    (hend : env.heapEnd = 0x78000000#64)
    (hm : MemcpySpecT env (liftProg fns) Idx.CompilerBuiltins.Mem.Memcpy Needs.CompilerBuiltins.Mem.Memcpy) :
    ReserveSpecT env 8 16 (liftProg fns) Idx.Alloc.Vec.VecE.Reserve Needs.Alloc.Vec.VecE.Reserve :=
  ReserveT.e_total Alloc.Vec.VecE.Reserve.link Alloc.Vec.VecE.Reserve.tmpl_eq Alloc.Vec.VecE.Reserve.wf
    (doReserve env hnext hend hm)

theorem reserveForm (hnext : VerifierRv64.Bump.AsGlobalAlloc.Alloc.link.d_NEXT.addr = env.nextAddr)
    (hend : env.heapEnd = 0x78000000#64)
    (hm : MemcpySpecT env (liftProg fns) Idx.CompilerBuiltins.Mem.Memcpy Needs.CompilerBuiltins.Mem.Memcpy) :
    ReserveSpecT env 8 24 (liftProg fns) Idx.Alloc.Vec.VecForm.Reserve Needs.Alloc.Vec.VecForm.Reserve :=
  ReserveT.form_total Alloc.Vec.VecForm.Reserve.link Alloc.Vec.VecForm.Reserve.tmpl_eq Alloc.Vec.VecForm.Reserve.wf
    (doReserve env hnext hend hm)

theorem reserveOptionE (hnext : VerifierRv64.Bump.AsGlobalAlloc.Alloc.link.d_NEXT.addr = env.nextAddr)
    (hend : env.heapEnd = 0x78000000#64)
    (hm : MemcpySpecT env (liftProg fns) Idx.CompilerBuiltins.Mem.Memcpy Needs.CompilerBuiltins.Mem.Memcpy) :
    ReserveSpecT env 8 24 (liftProg fns) Idx.Alloc.Vec.VecOptionE.Reserve Needs.Alloc.Vec.VecOptionE.Reserve :=
  ReserveT.optionE_total Alloc.Vec.VecOptionE.Reserve.link Alloc.Vec.VecOptionE.Reserve.tmpl_eq
    Alloc.Vec.VecOptionE.Reserve.wf
    (doReserve env hnext hend hm)

theorem reserveBusBlock (hnext : VerifierRv64.Bump.AsGlobalAlloc.Alloc.link.d_NEXT.addr = env.nextAddr)
    (hend : env.heapEnd = 0x78000000#64)
    (hm : MemcpySpecT env (liftProg fns) Idx.CompilerBuiltins.Mem.Memcpy Needs.CompilerBuiltins.Mem.Memcpy) :
    ReserveSpecT env 8 48 (liftProg fns) Idx.Alloc.Vec.VecBusBlock.Reserve Needs.Alloc.Vec.VecBusBlock.Reserve :=
  ReserveT.busBlock_total Alloc.Vec.VecBusBlock.Reserve.link Alloc.Vec.VecBusBlock.Reserve.tmpl_eq
    Alloc.Vec.VecBusBlock.Reserve.wf
    (doReserve env hnext hend hm)

theorem reserveK (hnext : VerifierRv64.Bump.AsGlobalAlloc.Alloc.link.d_NEXT.addr = env.nextAddr)
    (hend : env.heapEnd = 0x78000000#64)
    (hm : MemcpySpecT env (liftProg fns) Idx.CompilerBuiltins.Mem.Memcpy Needs.CompilerBuiltins.Mem.Memcpy) :
    ReserveSpecT env 8 8 (liftProg fns) Idx.Alloc.Vec.VecK.Reserve Needs.Alloc.Vec.VecK.Reserve :=
  ReserveT.k_total Alloc.Vec.VecK.Reserve.link Alloc.Vec.VecK.Reserve.tmpl_eq Alloc.Vec.VecK.Reserve.wf
    (doReserve env hnext hend hm)

theorem reserveU8 (hnext : VerifierRv64.Bump.AsGlobalAlloc.Alloc.link.d_NEXT.addr = env.nextAddr)
    (hend : env.heapEnd = 0x78000000#64)
    (hm : MemcpySpecT env (liftProg fns) Idx.CompilerBuiltins.Mem.Memcpy Needs.CompilerBuiltins.Mem.Memcpy) :
    ReserveSpecT env 1 1 (liftProg fns) Idx.Alloc.Vec.VecU8.Reserve Needs.Alloc.Vec.VecU8.Reserve :=
  ReserveT.u8_total Alloc.Vec.VecU8.Reserve.link Alloc.Vec.VecU8.Reserve.tmpl_eq Alloc.Vec.VecU8.Reserve.wf
    (doReserve env hnext hend hm)

theorem reserveUsize (hnext : VerifierRv64.Bump.AsGlobalAlloc.Alloc.link.d_NEXT.addr = env.nextAddr)
    (hend : env.heapEnd = 0x78000000#64)
    (hm : MemcpySpecT env (liftProg fns) Idx.CompilerBuiltins.Mem.Memcpy Needs.CompilerBuiltins.Mem.Memcpy) :
    ReserveSpecT env 8 8 (liftProg fns) Idx.Alloc.Vec.VecUsize.Reserve Needs.Alloc.Vec.VecUsize.Reserve :=
  ReserveT.usize_total Alloc.Vec.VecUsize.Reserve.link Alloc.Vec.VecUsize.Reserve.tmpl_eq Alloc.Vec.VecUsize.Reserve.wf
    (doReserve env hnext hend hm)

theorem boxNewUninit (hnext : VerifierRv64.Bump.AsGlobalAlloc.Alloc.link.d_NEXT.addr = env.nextAddr)
    (hend : env.heapEnd = 0x78000000#64) :
    BoxNewUninitSpecT env 80 (liftProg fns) Idx.Alloc.Boxed.BoxNewUninit Needs.Alloc.Boxed.BoxNewUninit :=
  BoxNewUninitT.total env _ _ Alloc.Boxed.BoxNewUninit.link Alloc.Boxed.BoxNewUninit.tmpl_eq
    Alloc.Boxed.BoxNewUninit.wf (by decide) (RuntimeT.alloc env hnext hend) (RuntimeT.panicNounwindFmt env)

theorem tryAllocateInRv64 (hnext : VerifierRv64.Bump.AsGlobalAlloc.Alloc.link.d_NEXT.addr = env.nextAddr)
    (hend : env.heapEnd = 0x78000000#64) :
    TryAllocRv64SpecT env (liftProg fns) Idx.Alloc.RawVec.RawVecInner.TryAllocateInInVerifierRv64
      Needs.Alloc.RawVec.RawVecInner.TryAllocateInInVerifierRv64 :=
  TryAllocateInT.rv64_total env _ _ Alloc.RawVec.RawVecInner.TryAllocateInInVerifierRv64.link
    Alloc.RawVec.RawVecInner.TryAllocateInInVerifierRv64.tmpl_eq Alloc.RawVec.RawVecInner.TryAllocateInInVerifierRv64.wf
    (by decide) (RuntimeT.alloc env hnext hend)

theorem tryAllocateIn (hnext : VerifierRv64.Bump.AsGlobalAlloc.Alloc.link.d_NEXT.addr = env.nextAddr)
    (hend : env.heapEnd = 0x78000000#64) :
    TryAllocSpecT env (liftProg fns) Idx.Alloc.RawVec.RawVecInner.TryAllocateInInVerifier
      Needs.Alloc.RawVec.RawVecInner.TryAllocateInInVerifier :=
  TryAllocateInT.total env _ _ Alloc.RawVec.RawVecInner.TryAllocateInInVerifier.link
    Alloc.RawVec.RawVecInner.TryAllocateInInVerifier.tmpl_eq Alloc.RawVec.RawVecInner.TryAllocateInInVerifier.wf
    (by decide) (by decide) (RuntimeT.alloc env hnext hend) (RuntimeT.memset env)

end Rv64mc.Table.AllocT

/-- info: 'Rv64mc.Table.AllocT.finishGrowA' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rv64mc.Table.AllocT.finishGrowA

/-- info: 'Rv64mc.Table.AllocT.growAmortized' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rv64mc.Table.AllocT.growAmortized

/-- info: 'Rv64mc.Table.AllocT.growOneColumnClaim' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rv64mc.Table.AllocT.growOneColumnClaim

/-- info: 'Rv64mc.Table.AllocT.growOneE' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rv64mc.Table.AllocT.growOneE

/-- info: 'Rv64mc.Table.AllocT.growOneFoldRound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rv64mc.Table.AllocT.growOneFoldRound

/-- info: 'Rv64mc.Table.AllocT.growOneGluedClaim' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rv64mc.Table.AllocT.growOneGluedClaim

/-- info: 'Rv64mc.Table.AllocT.growOneK' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rv64mc.Table.AllocT.growOneK

/-- info: 'Rv64mc.Table.AllocT.growOneKVecU16' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rv64mc.Table.AllocT.growOneKVecU16

/-- info: 'Rv64mc.Table.AllocT.growOneStackClaim' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rv64mc.Table.AllocT.growOneStackClaim

/-- info: 'Rv64mc.Table.AllocT.growOneVecEVecE' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rv64mc.Table.AllocT.growOneVecEVecE

/-- info: 'Rv64mc.Table.AllocT.growOneVecUsizeE' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rv64mc.Table.AllocT.growOneVecUsizeE

/-- info: 'Rv64mc.Table.AllocT.growOneU16' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rv64mc.Table.AllocT.growOneU16

/-- info: 'Rv64mc.Table.AllocT.growOneU64' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rv64mc.Table.AllocT.growOneU64

/-- info: 'Rv64mc.Table.AllocT.growOneUsize' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rv64mc.Table.AllocT.growOneUsize

/-- info: 'Rv64mc.Table.AllocT.growOneVecForm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rv64mc.Table.AllocT.growOneVecForm

/-- info: 'Rv64mc.Table.AllocT.doReserve' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rv64mc.Table.AllocT.doReserve

/-- info: 'Rv64mc.Table.AllocT.reserveE' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rv64mc.Table.AllocT.reserveE

/-- info: 'Rv64mc.Table.AllocT.reserveForm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rv64mc.Table.AllocT.reserveForm

/-- info: 'Rv64mc.Table.AllocT.reserveOptionE' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rv64mc.Table.AllocT.reserveOptionE

/-- info: 'Rv64mc.Table.AllocT.reserveBusBlock' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rv64mc.Table.AllocT.reserveBusBlock

/-- info: 'Rv64mc.Table.AllocT.reserveK' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rv64mc.Table.AllocT.reserveK

/-- info: 'Rv64mc.Table.AllocT.reserveU8' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rv64mc.Table.AllocT.reserveU8

/-- info: 'Rv64mc.Table.AllocT.reserveUsize' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rv64mc.Table.AllocT.reserveUsize

/-- info: 'Rv64mc.Table.AllocT.boxNewUninit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rv64mc.Table.AllocT.boxNewUninit

/-- info: 'Rv64mc.Table.AllocT.tryAllocateInRv64' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rv64mc.Table.AllocT.tryAllocateInRv64

/-- info: 'Rv64mc.Table.AllocT.tryAllocateIn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rv64mc.Table.AllocT.tryAllocateIn
