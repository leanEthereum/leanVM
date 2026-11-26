/-
  Rv64mc.Table.Runtime

  The runtime's proved contracts at the image (`liftProg Gen.fns`): each `ok` at its function's index
  (`Rv64mc/Gen/index.tsv`), with the generated link (`tmpl_eq`, `wf`) and stack (`Gen.Needs`). What is not proved
  yet is a hypothesis: `compiler_builtins`' `memcpy`, `memmove` and `memset` under the C wrappers, and `finish_grow`
  under `grow_amortized` and every `grow_one`. `alloc` takes the environment's two facts about the image: its data
  reference is `NEXT`, and the heap ends at the literal it compares with (`Final/End.lean`'s environment has both).
  Other tables discharge their `NoReturn` hypotheses with the panic chain here.
-/

import Rv64mc.Proof.Runtime.Halt
import Rv64mc.Proof.Runtime.Panics
import Rv64mc.Proof.Runtime.Alloc
import Rv64mc.Proof.Runtime.InputWord
import Rv64mc.Proof.Runtime.Memcmp
import Rv64mc.Proof.Runtime.MemWrappers
import Rv64mc.Proof.Runtime.GrowAmortized
import Rv64mc.Proof.Runtime.GrowOnes
import Rv64mc.Gen.Needs
import Rv64mc.Proof.Runtime.FinishGrow
import Rv64mc.Proof.Runtime.DoReserve
import Rv64mc.Proof.Runtime.BoxNewUninit
import Rv64mc.Proof.Runtime.Drop
import Rv64mc.Gen.Link.Alloc.RawVec
import Rv64mc.Gen.Link.Alloc
import Rv64mc.Gen.Link.Core
import Rv64mc.Gen.Link.Misc
import Rv64mc.Gen.Link.Alloc.Vec

namespace Rv64mc.Table.Runtime

open MachineChecked.RiscV.Lift Rv64mc.Gen Rv64mc.Spec.Runtime

variable (env : Env)

theorem halt :
    NoReturn env (liftProg fns) Idx.VerifierRv64.Halt Needs.VerifierRv64.Halt :=
  Proof.Runtime.Halt.ok env _ Idx.VerifierRv64.Halt _ VerifierRv64.Halt.tmpl_eq

theorem rustBeginUnwind :
    NoReturn env (liftProg fns) Idx.Rustc.RustBeginUnwind Needs.Rustc.RustBeginUnwind :=
  Proof.Runtime.Panics.rustBeginUnwind_ok Rustc.RustBeginUnwind.link Rustc.RustBeginUnwind.tmpl_eq
      Rustc.RustBeginUnwind.wf (halt env)

theorem panicFmt :
    NoReturn env (liftProg fns) Idx.Core.Panicking.PanicFmt Needs.Core.Panicking.PanicFmt :=
  Proof.Runtime.Panics.panicFmt_ok Core.Panicking.PanicFmt.link Core.Panicking.PanicFmt.tmpl_eq
      Core.Panicking.PanicFmt.wf (rustBeginUnwind env)

theorem panicNounwindFmt :
    NoReturn env (liftProg fns) Idx.Core.Panicking.PanicNounwindFmt Needs.Core.Panicking.PanicNounwindFmt :=
  Proof.Runtime.Panics.panicNounwindFmt_ok Core.Panicking.PanicNounwindFmt.link
      Core.Panicking.PanicNounwindFmt.tmpl_eq Core.Panicking.PanicNounwindFmt.wf (rustBeginUnwind env)

theorem panicBoundsCheck :
    NoReturn env (liftProg fns) Idx.Core.Panicking.PanicBoundsCheck Needs.Core.Panicking.PanicBoundsCheck :=
  Proof.Runtime.Panics.panicBoundsCheck_ok Core.Panicking.PanicBoundsCheck.link
      Core.Panicking.PanicBoundsCheck.tmpl_eq Core.Panicking.PanicBoundsCheck.wf (panicFmt env)

theorem assertFailedInner :
    NoReturn env (liftProg fns) Idx.Core.Panicking.AssertFailedInner Needs.Core.Panicking.AssertFailedInner :=
  Proof.Runtime.Panics.assertFailedInner_ok Core.Panicking.AssertFailedInner.link
      Core.Panicking.AssertFailedInner.tmpl_eq Core.Panicking.AssertFailedInner.wf (panicFmt env)

theorem sliceIndexFail :
    NoReturn env (liftProg fns) Idx.Core.Slice.Index.SliceIndexFail Needs.Core.Slice.Index.SliceIndexFail :=
  Proof.Runtime.Panics.sliceIndexFail_ok Core.Slice.Index.SliceIndexFail.link Core.Slice.Index.SliceIndexFail.tmpl_eq
      Core.Slice.Index.SliceIndexFail.wf (panicFmt env)

theorem removeAssertFailed :
    NoReturn env (liftProg fns) Idx.Alloc.Vec.VecAnyAny.Remove.AssertFailed Needs.Alloc.Vec.VecAnyAny.Remove.AssertFailed :=
  Proof.Runtime.Panics.removeAssertFailed_ok Alloc.Vec.VecAnyAny.Remove.AssertFailed.link
      Alloc.Vec.VecAnyAny.Remove.AssertFailed.tmpl_eq Alloc.Vec.VecAnyAny.Remove.AssertFailed.wf (panicFmt env)

theorem splitOffAssertFailed :
    NoReturn env (liftProg fns) Idx.Alloc.Vec.VecAnyAny.SplitOff.AssertFailed Needs.Alloc.Vec.VecAnyAny.SplitOff.AssertFailed :=
  Proof.Runtime.Panics.splitOffAssertFailed_ok Alloc.Vec.VecAnyAny.SplitOff.AssertFailed.link
      Alloc.Vec.VecAnyAny.SplitOff.AssertFailed.tmpl_eq Alloc.Vec.VecAnyAny.SplitOff.AssertFailed.wf (panicFmt env)

theorem capacityOverflow :
    NoReturn env (liftProg fns) Idx.Alloc.RawVec.CapacityOverflow Needs.Alloc.RawVec.CapacityOverflow :=
  Proof.Runtime.Panics.capacityOverflow_ok Alloc.RawVec.CapacityOverflow.link Alloc.RawVec.CapacityOverflow.tmpl_eq
      Alloc.RawVec.CapacityOverflow.wf (panicFmt env)

theorem assertFailedUsizeUsize :
    NoReturn env (liftProg fns) Idx.Core.Panicking.AssertFailedUsizeUsize Needs.Core.Panicking.AssertFailedUsizeUsize :=
  Proof.Runtime.Panics.assertFailedUsizeUsize_ok Core.Panicking.AssertFailedUsizeUsize.link
      Core.Panicking.AssertFailedUsizeUsize.tmpl_eq Core.Panicking.AssertFailedUsizeUsize.wf (assertFailedInner env)

theorem handleError :
    NoReturn env (liftProg fns) Idx.Alloc.RawVec.HandleError Needs.Alloc.RawVec.HandleError :=
  Proof.Runtime.Panics.handleError_ok Alloc.RawVec.HandleError.link Alloc.RawVec.HandleError.tmpl_eq
      Alloc.RawVec.HandleError.wf (capacityOverflow env)
    (panicNounwindFmt env)

theorem alloc
    (hnext : VerifierRv64.Bump.AsGlobalAlloc.Alloc.link.d_NEXT.addr = env.nextAddr) (hend : env.heapEnd =
      0x78000000#64) :
    AllocSpec env (liftProg fns) Idx.VerifierRv64.Bump.AsGlobalAlloc.Alloc Needs.VerifierRv64.Bump.AsGlobalAlloc.Alloc :=
  Proof.Runtime.Alloc.ok _ Idx.VerifierRv64.Bump.AsGlobalAlloc.Alloc VerifierRv64.Bump.AsGlobalAlloc.Alloc.link VerifierRv64.Bump.AsGlobalAlloc.Alloc.tmpl_eq
      VerifierRv64.Bump.AsGlobalAlloc.Alloc.wf hnext hend (halt env)

theorem inputWord :
    InputWordSpec env (liftProg fns) Idx.VerifierRv64.Input.Word Needs.VerifierRv64.Input.Word :=
  Proof.Runtime.InputWord.ok VerifierRv64.Input.Word.link VerifierRv64.Input.Word.tmpl_eq VerifierRv64.Input.Word.wf
      (halt env)

theorem memcmp :
    MemcmpSpec env (liftProg fns) Idx.Memcmp Needs.Memcmp :=
  Proof.Runtime.Memcmp.ok Memcmp.tmpl_eq

theorem memcpy
    (h : MemcpySpec env (liftProg fns) Idx.CompilerBuiltins.Mem.Memcpy Needs.CompilerBuiltins.Mem.Memcpy) :
    MemcpySpec env (liftProg fns) Idx.Memcpy Needs.Memcpy :=
  Proof.Runtime.MemWrappers.memcpy_ok Memcpy.link Memcpy.tmpl_eq Memcpy.wf h

theorem memmove
    (h : MemmoveSpec env (liftProg fns) Idx.CompilerBuiltins.Mem.Memmove Needs.CompilerBuiltins.Mem.Memmove) :
    MemmoveSpec env (liftProg fns) Idx.Memmove Needs.Memmove :=
  Proof.Runtime.MemWrappers.memmove_ok Memmove.link Memmove.tmpl_eq Memmove.wf h

theorem memset
    (h : MemsetSpec env (liftProg fns) Idx.CompilerBuiltins.Mem.Memset Needs.CompilerBuiltins.Mem.Memset) :
    MemsetSpec env (liftProg fns) Idx.Memset Needs.Memset :=
  Proof.Runtime.MemWrappers.memset_ok Memset.link Memset.tmpl_eq Memset.wf h

theorem growAmortized
    (hfg : FinishGrowSpec env (liftProg fns) Idx.Alloc.RawVec.RawVecInner.FinishGrow Needs.Alloc.RawVec.RawVecInner.FinishGrow) :
    GrowAmortizedSpec env (liftProg fns) Idx.Alloc.RawVec.RawVecInner.GrowAmortized Needs.Alloc.RawVec.RawVecInner.GrowAmortized :=
  Proof.Runtime.GrowAmortized.ok Alloc.RawVec.RawVecInner.GrowAmortized.tmpl_eq
      Alloc.RawVec.RawVecInner.GrowAmortized.wf hfg

theorem growOne_columnClaim
    (hfg : FinishGrowSpec env (liftProg fns) Idx.Alloc.RawVec.RawVecInner.FinishGrow Needs.Alloc.RawVec.RawVecInner.FinishGrow) :
    GrowOneSpec env Layouts.ColumnClaim.byteAlign Layouts.ColumnClaim.byteSize (liftProg fns) Idx.Alloc.RawVec.RawVecColumnClaim.GrowOne
      Needs.Alloc.RawVec.RawVecColumnClaim.GrowOne :=
  Proof.Runtime.GrowOnes.columnClaim_ok Alloc.RawVec.RawVecColumnClaim.GrowOne.link
      Alloc.RawVec.RawVecColumnClaim.GrowOne.tmpl_eq Alloc.RawVec.RawVecColumnClaim.GrowOne.wf (growAmortized env hfg)
    ((handleError env).mono_need (by decide))

theorem growOne_e
    (hfg : FinishGrowSpec env (liftProg fns) Idx.Alloc.RawVec.RawVecInner.FinishGrow Needs.Alloc.RawVec.RawVecInner.FinishGrow) :
    GrowOneSpec env Layouts.E.byteAlign Layouts.E.byteSize (liftProg fns) Idx.Alloc.RawVec.RawVecE.GrowOne Needs.Alloc.RawVec.RawVecE.GrowOne :=
  Proof.Runtime.GrowOnes.e_ok Alloc.RawVec.RawVecE.GrowOne.link Alloc.RawVec.RawVecE.GrowOne.tmpl_eq
      Alloc.RawVec.RawVecE.GrowOne.wf (growAmortized env hfg)
    ((handleError env).mono_need (by decide))

theorem growOne_foldRound
    (hfg : FinishGrowSpec env (liftProg fns) Idx.Alloc.RawVec.RawVecInner.FinishGrow Needs.Alloc.RawVec.RawVecInner.FinishGrow) :
    GrowOneSpec env Layouts.FoldRound.byteAlign Layouts.FoldRound.byteSize (liftProg fns) Idx.Alloc.RawVec.RawVecFoldRound.GrowOne
      Needs.Alloc.RawVec.RawVecFoldRound.GrowOne :=
  Proof.Runtime.GrowOnes.foldRound_ok Alloc.RawVec.RawVecFoldRound.GrowOne.link
      Alloc.RawVec.RawVecFoldRound.GrowOne.tmpl_eq Alloc.RawVec.RawVecFoldRound.GrowOne.wf (growAmortized env hfg)
    ((handleError env).mono_need (by decide))

theorem growOne_gluedClaim
    (hfg : FinishGrowSpec env (liftProg fns) Idx.Alloc.RawVec.RawVecInner.FinishGrow Needs.Alloc.RawVec.RawVecInner.FinishGrow) :
    GrowOneSpec env Layouts.GluedClaim.byteAlign Layouts.GluedClaim.byteSize (liftProg fns) Idx.Alloc.RawVec.RawVecGluedClaim.GrowOne
      Needs.Alloc.RawVec.RawVecGluedClaim.GrowOne :=
  Proof.Runtime.GrowOnes.gluedClaim_ok Alloc.RawVec.RawVecGluedClaim.GrowOne.link
      Alloc.RawVec.RawVecGluedClaim.GrowOne.tmpl_eq Alloc.RawVec.RawVecGluedClaim.GrowOne.wf (growAmortized env hfg)
    ((handleError env).mono_need (by decide))

theorem growOne_k
    (hfg : FinishGrowSpec env (liftProg fns) Idx.Alloc.RawVec.RawVecInner.FinishGrow Needs.Alloc.RawVec.RawVecInner.FinishGrow) :
    GrowOneSpec env Layouts.K.byteAlign Layouts.K.byteSize (liftProg fns) Idx.Alloc.RawVec.RawVecK.GrowOne Needs.Alloc.RawVec.RawVecK.GrowOne :=
  Proof.Runtime.GrowOnes.k_ok Alloc.RawVec.RawVecK.GrowOne.link Alloc.RawVec.RawVecK.GrowOne.tmpl_eq
      Alloc.RawVec.RawVecK.GrowOne.wf (growAmortized env hfg)
    ((handleError env).mono_need (by decide))

theorem growOne_kVecU16
    (hfg : FinishGrowSpec env (liftProg fns) Idx.Alloc.RawVec.RawVecInner.FinishGrow Needs.Alloc.RawVec.RawVecInner.FinishGrow) :
    GrowOneSpec env Layouts.KVecU16.byteAlign Layouts.KVecU16.byteSize (liftProg fns) Idx.Alloc.RawVec.RawVecTKVecU16E.GrowOne
      Needs.Alloc.RawVec.RawVecTKVecU16E.GrowOne :=
  Proof.Runtime.GrowOnes.kVecU16_ok Alloc.RawVec.RawVecTKVecU16E.GrowOne.link
      Alloc.RawVec.RawVecTKVecU16E.GrowOne.tmpl_eq Alloc.RawVec.RawVecTKVecU16E.GrowOne.wf (growAmortized env hfg)
    ((handleError env).mono_need (by decide))

theorem growOne_stackClaim
    (hfg : FinishGrowSpec env (liftProg fns) Idx.Alloc.RawVec.RawVecInner.FinishGrow Needs.Alloc.RawVec.RawVecInner.FinishGrow) :
    GrowOneSpec env Layouts.StackClaim.byteAlign Layouts.StackClaim.byteSize (liftProg fns) Idx.Alloc.RawVec.RawVecTStackWeightEE.GrowOne
      Needs.Alloc.RawVec.RawVecTStackWeightEE.GrowOne :=
  Proof.Runtime.GrowOnes.stackClaim_ok Alloc.RawVec.RawVecTStackWeightEE.GrowOne.link
      Alloc.RawVec.RawVecTStackWeightEE.GrowOne.tmpl_eq Alloc.RawVec.RawVecTStackWeightEE.GrowOne.wf (growAmortized
        env hfg)
    ((handleError env).mono_need (by decide))

theorem growOne_vecEVecE
    (hfg : FinishGrowSpec env (liftProg fns) Idx.Alloc.RawVec.RawVecInner.FinishGrow Needs.Alloc.RawVec.RawVecInner.FinishGrow) :
    GrowOneSpec env Layouts.VecEVecE.byteAlign Layouts.VecEVecE.byteSize (liftProg fns) Idx.Alloc.RawVec.RawVecTVecEVecEE.GrowOne
      Needs.Alloc.RawVec.RawVecTVecEVecEE.GrowOne :=
  Proof.Runtime.GrowOnes.vecEVecE_ok Alloc.RawVec.RawVecTVecEVecEE.GrowOne.link
      Alloc.RawVec.RawVecTVecEVecEE.GrowOne.tmpl_eq Alloc.RawVec.RawVecTVecEVecEE.GrowOne.wf (growAmortized env hfg)
    ((handleError env).mono_need (by decide))

theorem growOne_vecUsizeE
    (hfg : FinishGrowSpec env (liftProg fns) Idx.Alloc.RawVec.RawVecInner.FinishGrow Needs.Alloc.RawVec.RawVecInner.FinishGrow) :
    GrowOneSpec env Layouts.VecUsizeE.byteAlign Layouts.VecUsizeE.byteSize (liftProg fns) Idx.Alloc.RawVec.RawVecTVecUsizeEE.GrowOne
      Needs.Alloc.RawVec.RawVecTVecUsizeEE.GrowOne :=
  Proof.Runtime.GrowOnes.vecUsizeE_ok Alloc.RawVec.RawVecTVecUsizeEE.GrowOne.link
      Alloc.RawVec.RawVecTVecUsizeEE.GrowOne.tmpl_eq Alloc.RawVec.RawVecTVecUsizeEE.GrowOne.wf (growAmortized env hfg)
    ((handleError env).mono_need (by decide))

theorem growOne_u16
    (hfg : FinishGrowSpec env (liftProg fns) Idx.Alloc.RawVec.RawVecInner.FinishGrow Needs.Alloc.RawVec.RawVecInner.FinishGrow) :
    GrowOneSpec env 2 2 (liftProg fns) Idx.Alloc.RawVec.RawVecU16.GrowOne Needs.Alloc.RawVec.RawVecU16.GrowOne :=
  Proof.Runtime.GrowOnes.u16_ok Alloc.RawVec.RawVecU16.GrowOne.link Alloc.RawVec.RawVecU16.GrowOne.tmpl_eq
      Alloc.RawVec.RawVecU16.GrowOne.wf (growAmortized env hfg)
    ((handleError env).mono_need (by decide))

theorem growOne_u64
    (hfg : FinishGrowSpec env (liftProg fns) Idx.Alloc.RawVec.RawVecInner.FinishGrow Needs.Alloc.RawVec.RawVecInner.FinishGrow) :
    GrowOneSpec env 8 8 (liftProg fns) Idx.Alloc.RawVec.RawVecU64.GrowOne Needs.Alloc.RawVec.RawVecU64.GrowOne :=
  Proof.Runtime.GrowOnes.u64_ok Alloc.RawVec.RawVecU64.GrowOne.link Alloc.RawVec.RawVecU64.GrowOne.tmpl_eq
      Alloc.RawVec.RawVecU64.GrowOne.wf (growAmortized env hfg)
    ((handleError env).mono_need (by decide))

theorem growOne_usize
    (hfg : FinishGrowSpec env (liftProg fns) Idx.Alloc.RawVec.RawVecInner.FinishGrow Needs.Alloc.RawVec.RawVecInner.FinishGrow) :
    GrowOneSpec env 8 8 (liftProg fns) Idx.Alloc.RawVec.RawVecUsize.GrowOne Needs.Alloc.RawVec.RawVecUsize.GrowOne :=
  Proof.Runtime.GrowOnes.usize_ok Alloc.RawVec.RawVecUsize.GrowOne.link Alloc.RawVec.RawVecUsize.GrowOne.tmpl_eq
      Alloc.RawVec.RawVecUsize.GrowOne.wf (growAmortized env hfg)
    ((handleError env).mono_need (by decide))

theorem growOne_vecForm
    (hfg : FinishGrowSpec env (liftProg fns) Idx.Alloc.RawVec.RawVecInner.FinishGrow Needs.Alloc.RawVec.RawVecInner.FinishGrow) :
    GrowOneSpec env Layouts.Vec.byteAlign Layouts.Vec.byteSize (liftProg fns) Idx.Alloc.RawVec.RawVecVecForm.GrowOne
      Needs.Alloc.RawVec.RawVecVecForm.GrowOne :=
  Proof.Runtime.GrowOnes.vecForm_ok Alloc.RawVec.RawVecVecForm.GrowOne.link
      Alloc.RawVec.RawVecVecForm.GrowOne.tmpl_eq Alloc.RawVec.RawVecVecForm.GrowOne.wf (growAmortized env hfg)
    ((handleError env).mono_need (by decide))

theorem finishGrow
    (hnext : VerifierRv64.Bump.AsGlobalAlloc.Alloc.link.d_NEXT.addr = env.nextAddr)
    (hend : env.heapEnd = 0x78000000#64)
    (hm : MemcpySpec env (liftProg fns) Idx.CompilerBuiltins.Mem.Memcpy Needs.CompilerBuiltins.Mem.Memcpy) :
    FinishGrowSpec env (liftProg fns) Idx.Alloc.RawVec.RawVecInner.FinishGrow Needs.Alloc.RawVec.RawVecInner.FinishGrow :=
  Proof.Runtime.FinishGrow.ok env _ _ Alloc.RawVec.RawVecInner.FinishGrow.link Alloc.RawVec.RawVecInner.FinishGrow.tmpl_eq Alloc.RawVec.RawVecInner.FinishGrow.wf (by decide) (by decide)
    (alloc env hnext hend) (memcpy env hm)

theorem doReserve
    (hfg : FinishGrowSpec env (liftProg fns) Idx.Alloc.RawVec.RawVecInner.FinishGrow Needs.Alloc.RawVec.RawVecInner.FinishGrow) :
    DoReserveSpec env (liftProg fns) Idx.Alloc.RawVec.RawVecInnerAny.Reserve.DoReserveAndHandleGlobal Needs.Alloc.RawVec.RawVecInnerAny.Reserve.DoReserveAndHandleGlobal :=
  Proof.Runtime.DoReserve.ok env _ _ Alloc.RawVec.RawVecInnerAny.Reserve.DoReserveAndHandleGlobal.link Alloc.RawVec.RawVecInnerAny.Reserve.DoReserveAndHandleGlobal.tmpl_eq Alloc.RawVec.RawVecInnerAny.Reserve.DoReserveAndHandleGlobal.wf (by decide) (growAmortized env hfg)
    ((handleError env).mono_need (by decide))

theorem boxNewUninit
    (hnext : VerifierRv64.Bump.AsGlobalAlloc.Alloc.link.d_NEXT.addr = env.nextAddr)
    (hend : env.heapEnd = 0x78000000#64) :
    BoxNewUninitSpec env 80 (liftProg fns) Idx.Alloc.Boxed.BoxNewUninit Needs.Alloc.Boxed.BoxNewUninit :=
  Proof.Runtime.BoxNewUninit.ok env _ _ Alloc.Boxed.BoxNewUninit.link Alloc.Boxed.BoxNewUninit.tmpl_eq Alloc.Boxed.BoxNewUninit.wf (by decide) (alloc env hnext hend)
    (panicNounwindFmt env)

theorem dropVecForm : DropSpec env (liftProg fns) Idx.Core.Ptr.DropGlueVecForm Needs.Core.Ptr.DropGlueVecForm :=
  Proof.Runtime.Drop.vecForm_ok env _ _ _ Core.Ptr.DropGlueVecForm.tmpl_eq

theorem dropVecStackClaim :
    DropSpec env (liftProg fns) Idx.Core.Ptr.DropGlueVecTStackWeightEE Needs.Core.Ptr.DropGlueVecTStackWeightEE :=
  Proof.Runtime.Drop.vecStackClaim_ok env _ _ _ Core.Ptr.DropGlueVecTStackWeightEE.tmpl_eq

theorem dropLayout
    (ht : DropSpec env (liftProg fns) Idx.Core.Ptr.DropGlueVecTable Needs.Core.Ptr.DropGlueVecTable)
    (hb : DropSpec env (liftProg fns) Idx.Core.Ptr.DropGlueVecBusBlock Needs.Core.Ptr.DropGlueVecBusBlock) :
    DropSpec env (liftProg fns) Idx.Core.Ptr.DropGlueLayout Needs.Core.Ptr.DropGlueLayout :=
  Proof.Runtime.Drop.layout_ok env _ _ _ Core.Ptr.DropGlueLayout.tmpl_eq Core.Ptr.DropGlueLayout.wf
    (needC := 64) (by decide) ht (hb.mono_need (by decide))

end Rv64mc.Table.Runtime
