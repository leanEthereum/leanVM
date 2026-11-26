/-
  Rv64mc.Proof.Runtime.Panics

  The panic chain never returns: `rust_begin_unwind` calls `halt`, `panic_fmt` and `panic_nounwind_fmt` call
  `rust_begin_unwind`, and the other entries call `panic_fmt` (`assert_failed` through `assert_failed_inner`,
  `handle_error` through `capacity_overflow` or `panic_nounwind_fmt`). Each from its callees' `NoReturn`, with their
  stack (none of them has a frame). The forwarders are `forward_ok` at their template's body, by `rfl`.
-/

import Rv64mc.Proof.Runtime.Forward
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

namespace Rv64mc.Proof.Runtime.Panics

open RiscvZkvm.Rv64 Lprog Lprog.RiscV Rv64mc.Spec.Runtime
open Rv64mc.Gen

variable {env : Env} {p : Lprog (Op Reg) Reg} {i need : Nat}

theorem rustBeginUnwind_ok (L : Rustc.RustBeginUnwind.Link) (hp : p[i]? = some (Rustc.RustBeginUnwind.tmpl L))
    (hL : L.WF p) (h : NoReturn env p L.halt.idx need) : NoReturn env p i need :=
  forward_ok hp rfl hL.halt hL.s0 h

theorem panicFmt_ok (L : Core.Panicking.PanicFmt.Link) (hp : p[i]? = some (Core.Panicking.PanicFmt.tmpl L))
    (hL : L.WF p) (h : NoReturn env p L.rustBeginUnwind.idx need) : NoReturn env p i need :=
  forward_ok hp rfl hL.rustBeginUnwind hL.s0 h

theorem panicNounwindFmt_ok (L : Core.Panicking.PanicNounwindFmt.Link)
    (hp : p[i]? = some (Core.Panicking.PanicNounwindFmt.tmpl L)) (hL : L.WF p)
    (h : NoReturn env p L.rustBeginUnwind.idx need) : NoReturn env p i need :=
  forward_ok hp rfl hL.rustBeginUnwind hL.s0 h

theorem panicBoundsCheck_ok (L : Core.Panicking.PanicBoundsCheck.Link)
    (hp : p[i]? = some (Core.Panicking.PanicBoundsCheck.tmpl L)) (hL : L.WF p)
    (h : NoReturn env p L.panicFmt.idx need) : NoReturn env p i need :=
  forward_ok hp rfl hL.panicFmt hL.s0 h

theorem assertFailedInner_ok (L : Core.Panicking.AssertFailedInner.Link)
    (hp : p[i]? = some (Core.Panicking.AssertFailedInner.tmpl L)) (hL : L.WF p)
    (h : NoReturn env p L.panicFmt.idx need) : NoReturn env p i need :=
  forward_ok hp rfl hL.panicFmt hL.s0 h

theorem sliceIndexFail_ok (L : Core.Slice.Index.SliceIndexFail.Link)
    (hp : p[i]? = some (Core.Slice.Index.SliceIndexFail.tmpl L)) (hL : L.WF p)
    (h : NoReturn env p L.panicFmt.idx need) : NoReturn env p i need :=
  forward_ok hp rfl hL.panicFmt hL.s0 h

theorem removeAssertFailed_ok (L : Alloc.Vec.VecAnyAny.Remove.AssertFailed.Link)
    (hp : p[i]? = some (Alloc.Vec.VecAnyAny.Remove.AssertFailed.tmpl L)) (hL : L.WF p)
    (h : NoReturn env p L.panicFmt.idx need) : NoReturn env p i need :=
  forward_ok hp rfl hL.panicFmt hL.s0 h

theorem splitOffAssertFailed_ok (L : Alloc.Vec.VecAnyAny.SplitOff.AssertFailed.Link)
    (hp : p[i]? = some (Alloc.Vec.VecAnyAny.SplitOff.AssertFailed.tmpl L)) (hL : L.WF p)
    (h : NoReturn env p L.panicFmt.idx need) : NoReturn env p i need :=
  forward_ok hp rfl hL.panicFmt hL.s0 h

theorem capacityOverflow_ok (L : Alloc.RawVec.CapacityOverflow.Link)
    (hp : p[i]? = some (Alloc.RawVec.CapacityOverflow.tmpl L)) (hL : L.WF p)
    (h : NoReturn env p L.panicFmt.idx need) : NoReturn env p i need :=
  forward_ok hp rfl hL.panicFmt hL.s0 h

/-- `assert_failed::<usize, usize>`: `mv a0, a2`, then `assert_failed_inner`. -/
theorem assertFailedUsizeUsize_ok (L : Core.Panicking.AssertFailedUsizeUsize.Link)
    (hp : p[i]? = some (Core.Panicking.AssertFailedUsizeUsize.tmpl L)) (hL : L.WF p)
    (h : NoReturn env p L.assertFailedInner.idx need) : NoReturn env p i need := by
  intro G n Q ret top rest regs m ⟨⟨hra, hsp⟩, hstk, hst, hnx, _, hal⟩ _
  lsym hp with [hra, hsp, Lprog.Isa.addrAt, hL.assertFailedInner, hL.s0, Holds.post] using [h.contract]
  exact ⟨⟨by simp [updReg_apply], by simp [updReg_apply]⟩, by simpa [updReg_apply, hsp] using hstk, hst, hnx,
    trivial, by simpa [updReg_apply, hsp] using hal⟩

/-- `handle_error`: `capacity_overflow` for a zero argument, else `panic_nounwind_fmt`. -/
theorem handleError_ok (L : Alloc.RawVec.HandleError.Link) (hp : p[i]? = some (Alloc.RawVec.HandleError.tmpl L))
    (hL : L.WF p) (h1 : NoReturn env p L.capacityOverflow.idx need)
    (h2 : NoReturn env p L.panicNounwindFmt.idx need) : NoReturn env p i need := by
  intro G n Q ret top rest regs m ⟨⟨hra, hsp⟩, hstk, hst, hnx, _, hal⟩ _
  lsym hp with [hra, hsp, Lprog.Isa.addrAt, hL.capacityOverflow, hL.panicNounwindFmt, hL.s0, hL.s1, Holds.post]
    using [h1.contract, h2.contract]
  all_goals exact ⟨⟨by simp [updReg_apply], by simp [updReg_apply]⟩, by simpa [updReg_apply, hsp] using hstk, hst,
    hnx, trivial, by simpa [updReg_apply, hsp] using hal⟩

end Rv64mc.Proof.Runtime.Panics
