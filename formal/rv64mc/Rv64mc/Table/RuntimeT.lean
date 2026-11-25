/-
  Rv64mc.Table.RuntimeT

  The runtime's total contracts at the image (`liftProg Gen.fns`), the total counterpart of `Runtime.lean`: each
  function's total theorem at its index (`Rv64mc/Gen/index.tsv`), with the generated link (`tmpl_eq`, `wf`), the
  stack `Gen.Needs` gives, and its callees' total theorems here. Left as hypotheses: the environment's two facts
  about the image that `alloc` reads (its data reference is `NEXT`, the heap ends at the literal it compares with),
  and `compiler_builtins`' `memcpy` and `memmove` (`MemcpySpecT`, `MemmoveSpecT`), whose proofs are wave 1b's.

  ## Main results

  * `halt`, the panic chain, `alloc`, `inputWord`, `memset`, `memcmp`, `memcpy`, `memmove`, `finishGrow`, the drops
    that return at once
-/

import Rv64mc.Proof.Runtime.PanicsT
import Rv64mc.Proof.Runtime.AllocT
import Rv64mc.Proof.Runtime.InputWordT
import Rv64mc.Proof.Runtime.MemsetT
import Rv64mc.Proof.Runtime.MemcmpT
import Rv64mc.Proof.Runtime.MemWrappersT
import Rv64mc.Proof.Runtime.FinishGrowT
import Rv64mc.Proof.Runtime.DropT
import Rv64mc.Gen.Needs
import Rv64mc.Gen.Link.Alloc.RawVec
import Rv64mc.Gen.Link.Alloc
import Rv64mc.Gen.Link.Core
import Rv64mc.Gen.Link.Misc
import Rv64mc.Gen.Link.Alloc.Vec

namespace Rv64mc.Table.RuntimeT

open MachineChecked.RiscV.Lift Rv64mc.Gen Rv64mc.Proof.Runtime
open Rv64mc.Proof.Runtime.AllocT (AllocSpecT)
open Rv64mc.Proof.Runtime.InputWordT (InputWordSpecT)
open Rv64mc.Proof.Runtime.MemsetT (MemsetSafeT)
open Rv64mc.Proof.Runtime.MemcmpT (MemcmpSpecT)
open Rv64mc.Proof.Runtime.MemcpyT (MemcpySpecT)
open Rv64mc.Proof.Runtime.MemmoveT (MemmoveSpecT)
open Rv64mc.Proof.Runtime.FinishGrowT (FinishGrowSpecT)
open Rv64mc.Proof.Runtime.DropT (DropSpecT)

variable (env : Env)

theorem halt : Aborts env (liftProg fns) Idx.VerifierRv64.Halt Needs.VerifierRv64.Halt :=
  halt_aborts env _ Idx.VerifierRv64.Halt VerifierRv64.Halt.link VerifierRv64.Halt.tmpl_eq

theorem rustBeginUnwind : Aborts env (liftProg fns) Idx.Rustc.RustBeginUnwind Needs.Rustc.RustBeginUnwind :=
  PanicsT.rustBeginUnwind_aborts Rustc.RustBeginUnwind.link Rustc.RustBeginUnwind.tmpl_eq Rustc.RustBeginUnwind.wf
    (halt env)

theorem panicFmt : Aborts env (liftProg fns) Idx.Core.Panicking.PanicFmt Needs.Core.Panicking.PanicFmt :=
  PanicsT.panicFmt_aborts Core.Panicking.PanicFmt.link Core.Panicking.PanicFmt.tmpl_eq Core.Panicking.PanicFmt.wf
    (rustBeginUnwind env)

theorem panicNounwindFmt :
    Aborts env (liftProg fns) Idx.Core.Panicking.PanicNounwindFmt Needs.Core.Panicking.PanicNounwindFmt :=
  PanicsT.panicNounwindFmt_aborts Core.Panicking.PanicNounwindFmt.link Core.Panicking.PanicNounwindFmt.tmpl_eq
    Core.Panicking.PanicNounwindFmt.wf (rustBeginUnwind env)

theorem panicBoundsCheck :
    Aborts env (liftProg fns) Idx.Core.Panicking.PanicBoundsCheck Needs.Core.Panicking.PanicBoundsCheck :=
  PanicsT.panicBoundsCheck_aborts Core.Panicking.PanicBoundsCheck.link Core.Panicking.PanicBoundsCheck.tmpl_eq
    Core.Panicking.PanicBoundsCheck.wf (panicFmt env)

theorem assertFailedInner :
    Aborts env (liftProg fns) Idx.Core.Panicking.AssertFailedInner Needs.Core.Panicking.AssertFailedInner :=
  PanicsT.assertFailedInner_aborts Core.Panicking.AssertFailedInner.link Core.Panicking.AssertFailedInner.tmpl_eq
    Core.Panicking.AssertFailedInner.wf (panicFmt env)

theorem sliceIndexFail :
    Aborts env (liftProg fns) Idx.Core.Slice.Index.SliceIndexFail Needs.Core.Slice.Index.SliceIndexFail :=
  PanicsT.sliceIndexFail_aborts Core.Slice.Index.SliceIndexFail.link Core.Slice.Index.SliceIndexFail.tmpl_eq
    Core.Slice.Index.SliceIndexFail.wf (panicFmt env)

theorem removeAssertFailed :
    Aborts env (liftProg fns) Idx.Alloc.Vec.VecAnyAny.Remove.AssertFailed
      Needs.Alloc.Vec.VecAnyAny.Remove.AssertFailed :=
  PanicsT.removeAssertFailed_aborts Alloc.Vec.VecAnyAny.Remove.AssertFailed.link
    Alloc.Vec.VecAnyAny.Remove.AssertFailed.tmpl_eq Alloc.Vec.VecAnyAny.Remove.AssertFailed.wf (panicFmt env)

theorem splitOffAssertFailed :
    Aborts env (liftProg fns) Idx.Alloc.Vec.VecAnyAny.SplitOff.AssertFailed
      Needs.Alloc.Vec.VecAnyAny.SplitOff.AssertFailed :=
  PanicsT.splitOffAssertFailed_aborts Alloc.Vec.VecAnyAny.SplitOff.AssertFailed.link
    Alloc.Vec.VecAnyAny.SplitOff.AssertFailed.tmpl_eq Alloc.Vec.VecAnyAny.SplitOff.AssertFailed.wf (panicFmt env)

theorem capacityOverflow :
    Aborts env (liftProg fns) Idx.Alloc.RawVec.CapacityOverflow Needs.Alloc.RawVec.CapacityOverflow :=
  PanicsT.capacityOverflow_aborts Alloc.RawVec.CapacityOverflow.link Alloc.RawVec.CapacityOverflow.tmpl_eq
    Alloc.RawVec.CapacityOverflow.wf (panicFmt env)

theorem assertFailedUsizeUsize :
    Aborts env (liftProg fns) Idx.Core.Panicking.AssertFailedUsizeUsize Needs.Core.Panicking.AssertFailedUsizeUsize :=
  PanicsT.assertFailedUsizeUsize_aborts Core.Panicking.AssertFailedUsizeUsize.link
    Core.Panicking.AssertFailedUsizeUsize.tmpl_eq Core.Panicking.AssertFailedUsizeUsize.wf (assertFailedInner env)

theorem handleError : Aborts env (liftProg fns) Idx.Alloc.RawVec.HandleError Needs.Alloc.RawVec.HandleError :=
  PanicsT.handleError_aborts Alloc.RawVec.HandleError.link Alloc.RawVec.HandleError.tmpl_eq
    Alloc.RawVec.HandleError.wf (capacityOverflow env) (panicNounwindFmt env)

theorem alloc (hnext : VerifierRv64.Bump.AsGlobalAlloc.Alloc.link.d_NEXT.addr = env.nextAddr)
    (hend : env.heapEnd = 0x78000000#64) :
    AllocSpecT env (liftProg fns) Idx.VerifierRv64.Bump.AsGlobalAlloc.Alloc
      Needs.VerifierRv64.Bump.AsGlobalAlloc.Alloc :=
  AllocT.total _ Idx.VerifierRv64.Bump.AsGlobalAlloc.Alloc VerifierRv64.Bump.AsGlobalAlloc.Alloc.link
    VerifierRv64.Bump.AsGlobalAlloc.Alloc.tmpl_eq VerifierRv64.Bump.AsGlobalAlloc.Alloc.wf hnext hend (halt env)

theorem inputWord : InputWordSpecT env (liftProg fns) Idx.VerifierRv64.Input.Word Needs.VerifierRv64.Input.Word :=
  InputWordT.total VerifierRv64.Input.Word.link VerifierRv64.Input.Word.tmpl_eq VerifierRv64.Input.Word.wf
    (halt env)

theorem memsetBuiltin :
    MemsetSafeT env (liftProg fns) Idx.CompilerBuiltins.Mem.Memset Needs.CompilerBuiltins.Mem.Memset :=
  MemsetT.total _ Idx.CompilerBuiltins.Mem.Memset CompilerBuiltins.Mem.Memset.link
    CompilerBuiltins.Mem.Memset.tmpl_eq

theorem memset : MemsetSafeT env (liftProg fns) Idx.Memset Needs.Memset :=
  MemsetT.memset_total Memset.link Memset.tmpl_eq Memset.wf (memsetBuiltin env)

theorem memcmp : MemcmpSpecT env (liftProg fns) Idx.Memcmp Needs.Memcmp :=
  MemcmpT.total Memcmp.tmpl_eq

theorem memcpy
    (h : MemcpySpecT env (liftProg fns) Idx.CompilerBuiltins.Mem.Memcpy Needs.CompilerBuiltins.Mem.Memcpy) :
    MemcpySpecT env (liftProg fns) Idx.Memcpy Needs.Memcpy :=
  MemWrappersT.memcpy_total Memcpy.link Memcpy.tmpl_eq Memcpy.wf h

theorem memmove
    (h : MemmoveSpecT env (liftProg fns) Idx.CompilerBuiltins.Mem.Memmove Needs.CompilerBuiltins.Mem.Memmove) :
    MemmoveSpecT env (liftProg fns) Idx.Memmove Needs.Memmove :=
  MemWrappersT.memmove_total Memmove.link Memmove.tmpl_eq Memmove.wf h

theorem finishGrow (hnext : VerifierRv64.Bump.AsGlobalAlloc.Alloc.link.d_NEXT.addr = env.nextAddr)
    (hend : env.heapEnd = 0x78000000#64)
    (hm : MemcpySpecT env (liftProg fns) Idx.CompilerBuiltins.Mem.Memcpy Needs.CompilerBuiltins.Mem.Memcpy) :
    FinishGrowSpecT env (liftProg fns) Idx.Alloc.RawVec.RawVecInner.FinishGrow
      Needs.Alloc.RawVec.RawVecInner.FinishGrow :=
  FinishGrowT.total env _ _ Alloc.RawVec.RawVecInner.FinishGrow.link Alloc.RawVec.RawVecInner.FinishGrow.tmpl_eq
    Alloc.RawVec.RawVecInner.FinishGrow.wf (by decide) (by decide) (alloc env hnext hend) (memcpy env hm)

theorem dropVecForm : DropSpecT env (liftProg fns) Idx.Core.Ptr.DropGlueVecForm Needs.Core.Ptr.DropGlueVecForm :=
  DropT.vecForm_total env _ _ _ Core.Ptr.DropGlueVecForm.tmpl_eq _

theorem dropVecStackClaim :
    DropSpecT env (liftProg fns) Idx.Core.Ptr.DropGlueVecTStackWeightEE Needs.Core.Ptr.DropGlueVecTStackWeightEE :=
  DropT.vecStackClaim_total env _ _ _ Core.Ptr.DropGlueVecTStackWeightEE.tmpl_eq _

theorem partialDropForm :
    DropSpecT env (liftProg fns) Idx.Core.Array.Iter.IterInner.SliceMaybeUninitForm.AsPartialDrop.PartialDrop
      Needs.Core.Array.Iter.IterInner.SliceMaybeUninitForm.AsPartialDrop.PartialDrop :=
  DropT.partialDropForm_total env _ _ _
    Core.Array.Iter.IterInner.SliceMaybeUninitForm.AsPartialDrop.PartialDrop.tmpl_eq _

end Rv64mc.Table.RuntimeT

/-- info: 'Rv64mc.Table.RuntimeT.halt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rv64mc.Table.RuntimeT.halt

/-- info: 'Rv64mc.Table.RuntimeT.rustBeginUnwind' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rv64mc.Table.RuntimeT.rustBeginUnwind

/-- info: 'Rv64mc.Table.RuntimeT.panicFmt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rv64mc.Table.RuntimeT.panicFmt

/-- info: 'Rv64mc.Table.RuntimeT.panicNounwindFmt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rv64mc.Table.RuntimeT.panicNounwindFmt

/-- info: 'Rv64mc.Table.RuntimeT.panicBoundsCheck' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rv64mc.Table.RuntimeT.panicBoundsCheck

/-- info: 'Rv64mc.Table.RuntimeT.assertFailedInner' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rv64mc.Table.RuntimeT.assertFailedInner

/-- info: 'Rv64mc.Table.RuntimeT.sliceIndexFail' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rv64mc.Table.RuntimeT.sliceIndexFail

/-- info: 'Rv64mc.Table.RuntimeT.removeAssertFailed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rv64mc.Table.RuntimeT.removeAssertFailed

/-- info: 'Rv64mc.Table.RuntimeT.splitOffAssertFailed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rv64mc.Table.RuntimeT.splitOffAssertFailed

/-- info: 'Rv64mc.Table.RuntimeT.capacityOverflow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rv64mc.Table.RuntimeT.capacityOverflow

/-- info: 'Rv64mc.Table.RuntimeT.assertFailedUsizeUsize' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rv64mc.Table.RuntimeT.assertFailedUsizeUsize

/-- info: 'Rv64mc.Table.RuntimeT.handleError' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rv64mc.Table.RuntimeT.handleError

/-- info: 'Rv64mc.Table.RuntimeT.alloc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rv64mc.Table.RuntimeT.alloc

/-- info: 'Rv64mc.Table.RuntimeT.inputWord' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rv64mc.Table.RuntimeT.inputWord

/-- info: 'Rv64mc.Table.RuntimeT.memsetBuiltin' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rv64mc.Table.RuntimeT.memsetBuiltin

/-- info: 'Rv64mc.Table.RuntimeT.memset' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rv64mc.Table.RuntimeT.memset

/-- info: 'Rv64mc.Table.RuntimeT.memcmp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rv64mc.Table.RuntimeT.memcmp

/-- info: 'Rv64mc.Table.RuntimeT.memcpy' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rv64mc.Table.RuntimeT.memcpy

/-- info: 'Rv64mc.Table.RuntimeT.memmove' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rv64mc.Table.RuntimeT.memmove

/-- info: 'Rv64mc.Table.RuntimeT.finishGrow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rv64mc.Table.RuntimeT.finishGrow

/-- info: 'Rv64mc.Table.RuntimeT.dropVecForm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rv64mc.Table.RuntimeT.dropVecForm

/-- info: 'Rv64mc.Table.RuntimeT.dropVecStackClaim' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rv64mc.Table.RuntimeT.dropVecStackClaim

/-- info: 'Rv64mc.Table.RuntimeT.partialDropForm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rv64mc.Table.RuntimeT.partialDropForm
