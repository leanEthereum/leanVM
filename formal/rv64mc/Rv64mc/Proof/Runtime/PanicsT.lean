/-
  Rv64mc.Proof.Runtime.PanicsT

  The panic chain ends the run with the guest's abort (`Aborts`), the total counterpart of
  `Panics.lean`: `rust_begin_unwind` calls `halt`, `panic_fmt` and `panic_nounwind_fmt` call
  `rust_begin_unwind`, and the other entries call `panic_fmt` (`assert_failed` through
  `assert_failed_inner`, `handle_error` through `capacity_overflow` or `panic_nounwind_fmt`). Each
  from its callees' `Aborts`, with their stack. The forwarders are `forward_aborts` at their
  template's body, by `rfl`.
-/

import Rv64mc.Proof.Runtime.HaltT
import Rv64mc.Gen.Tmpl.Rustc.RustBeginUnwind
import Rv64mc.Gen.Tmpl.Core.Panicking.PanicFmt
import Rv64mc.Gen.Tmpl.Core.Panicking.PanicNounwindFmt
import Rv64mc.Gen.Tmpl.Core.Panicking.PanicBoundsCheck
import Rv64mc.Gen.Tmpl.Core.Panicking.AssertFailedInner
import Rv64mc.Gen.Tmpl.Core.Panicking.AssertFailedUsizeUsize
import Rv64mc.Gen.Tmpl.Core.Slice.Index.SliceIndexFail
import Rv64mc.Gen.Tmpl.Alloc.Vec.VecAnyAny.Remove.AssertFailed
import Rv64mc.Gen.Tmpl.Alloc.Vec.VecAnyAny.SplitOff.AssertFailed
import Rv64mc.Gen.Tmpl.Alloc.RawVec.CapacityOverflow
import Rv64mc.Gen.Tmpl.Alloc.RawVec.HandleError

namespace Rv64mc.Proof.Runtime.PanicsT

open RiscvZkvm.Rv64 Lprog Lprog.RiscV Rv64mc.Proof.Runtime
open Rv64mc.Gen

variable {env : Env} {p : Lprog (Op Reg) Reg} {i need : Nat}

theorem rustBeginUnwind_aborts (L : Rustc.RustBeginUnwind.Link)
    (hp : p[i]? = some (Rustc.RustBeginUnwind.tmpl L)) (hL : L.WF p) (h : Aborts env p L.halt.idx need) :
    Aborts env p i need :=
  forward_aborts hp rfl hL.halt hL.s0 h

theorem panicFmt_aborts (L : Core.Panicking.PanicFmt.Link) (hp : p[i]? = some (Core.Panicking.PanicFmt.tmpl L))
    (hL : L.WF p) (h : Aborts env p L.rustBeginUnwind.idx need) : Aborts env p i need :=
  forward_aborts hp rfl hL.rustBeginUnwind hL.s0 h

theorem panicNounwindFmt_aborts (L : Core.Panicking.PanicNounwindFmt.Link)
    (hp : p[i]? = some (Core.Panicking.PanicNounwindFmt.tmpl L)) (hL : L.WF p)
    (h : Aborts env p L.rustBeginUnwind.idx need) : Aborts env p i need :=
  forward_aborts hp rfl hL.rustBeginUnwind hL.s0 h

theorem panicBoundsCheck_aborts (L : Core.Panicking.PanicBoundsCheck.Link)
    (hp : p[i]? = some (Core.Panicking.PanicBoundsCheck.tmpl L)) (hL : L.WF p)
    (h : Aborts env p L.panicFmt.idx need) : Aborts env p i need :=
  forward_aborts hp rfl hL.panicFmt hL.s0 h

theorem assertFailedInner_aborts (L : Core.Panicking.AssertFailedInner.Link)
    (hp : p[i]? = some (Core.Panicking.AssertFailedInner.tmpl L)) (hL : L.WF p)
    (h : Aborts env p L.panicFmt.idx need) : Aborts env p i need :=
  forward_aborts hp rfl hL.panicFmt hL.s0 h

theorem sliceIndexFail_aborts (L : Core.Slice.Index.SliceIndexFail.Link)
    (hp : p[i]? = some (Core.Slice.Index.SliceIndexFail.tmpl L)) (hL : L.WF p)
    (h : Aborts env p L.panicFmt.idx need) : Aborts env p i need :=
  forward_aborts hp rfl hL.panicFmt hL.s0 h

theorem removeAssertFailed_aborts (L : Alloc.Vec.VecAnyAny.Remove.AssertFailed.Link)
    (hp : p[i]? = some (Alloc.Vec.VecAnyAny.Remove.AssertFailed.tmpl L)) (hL : L.WF p)
    (h : Aborts env p L.panicFmt.idx need) : Aborts env p i need :=
  forward_aborts hp rfl hL.panicFmt hL.s0 h

theorem splitOffAssertFailed_aborts (L : Alloc.Vec.VecAnyAny.SplitOff.AssertFailed.Link)
    (hp : p[i]? = some (Alloc.Vec.VecAnyAny.SplitOff.AssertFailed.tmpl L)) (hL : L.WF p)
    (h : Aborts env p L.panicFmt.idx need) : Aborts env p i need :=
  forward_aborts hp rfl hL.panicFmt hL.s0 h

theorem capacityOverflow_aborts (L : Alloc.RawVec.CapacityOverflow.Link)
    (hp : p[i]? = some (Alloc.RawVec.CapacityOverflow.tmpl L)) (hL : L.WF p)
    (h : Aborts env p L.panicFmt.idx need) : Aborts env p i need :=
  forward_aborts hp rfl hL.panicFmt hL.s0 h

/-- `assert_failed::<usize, usize>`: `mv a0, a2`, then `assert_failed_inner`. -/
theorem assertFailedUsizeUsize_aborts (L : Core.Panicking.AssertFailedUsizeUsize.Link)
    (hp : p[i]? = some (Core.Panicking.AssertFailedUsizeUsize.tmpl L)) (hL : L.WF p)
    (h : Aborts env p L.assertFailedInner.idx need) : Aborts env p i need := by
  intro Q ret top rest regs m hpre hstop _
  refine Total.label hp rfl (WinOk.of_ne hp rfl nofun) ?_
  refine Total.set hp rfl (WinOk.of_set hp rfl) ?_
  refine Total.label hp rfl (WinOk.of_ne hp rfl nofun) ?_
  refine Total.set hp rfl (WinOk.of_set hp rfl) ?_
  refine Total.label hp rfl (WinOk.of_ne hp rfl nofun) ?_
  exact h.call hpre hp rfl (callee_site hL.assertFailedInner hL.s0 (by simp [updReg_apply, Expr.eval]))
    (by simp [updReg_apply, hpre.1.1.2]) hstop

/-- `handle_error`: `capacity_overflow` for a zero argument, else `panic_nounwind_fmt`. -/
theorem handleError_aborts (L : Alloc.RawVec.HandleError.Link)
    (hp : p[i]? = some (Alloc.RawVec.HandleError.tmpl L)) (hL : L.WF p)
    (h1 : Aborts env p L.capacityOverflow.idx need) (h2 : Aborts env p L.panicNounwindFmt.idx need) :
    Aborts env p i need := by
  intro Q ret top rest regs m hpre hstop _
  refine Total.label hp rfl (WinOk.of_ne hp rfl nofun) ?_
  refine Total.cond hp rfl (b := regs .x10 != BitVec.ofInt 64 0) (by simp [condEval, operandVal, cmpEval]) rfl
    (WinOk.of_ne hp rfl nofun) (fun _ => ?_) (fun _ => ?_)
  · refine Total.label hp rfl (WinOk.of_ne hp rfl nofun) ?_
    refine Total.set hp rfl (WinOk.of_set hp rfl) ?_
    refine Total.label hp rfl (WinOk.of_ne hp rfl nofun) ?_
    exact h2.call hpre hp rfl (callee_site hL.panicNounwindFmt hL.s1 (by simp [updReg_apply, Expr.eval]))
      (by simp [updReg_apply, hpre.1.1.2]) hstop
  · refine Total.label hp rfl (WinOk.of_ne hp rfl nofun) ?_
    refine Total.set hp rfl (WinOk.of_set hp rfl) ?_
    refine Total.label hp rfl (WinOk.of_ne hp rfl nofun) ?_
    exact h1.call hpre hp rfl (callee_site hL.capacityOverflow hL.s0 (by simp [updReg_apply, Expr.eval]))
      (by simp [updReg_apply, hpre.1.1.2]) hstop

end Rv64mc.Proof.Runtime.PanicsT
