/-
  LeanVM.Guest.EndExecAExtra

  The reference holds each hint-only cell's value: `ExtraRef` on the deployed alignment.
-/

module

public import LeanVM.Guest.EndExecC
public import LeanVM.Guest.Bridge.ProgAlDefs

/-!
# The hint-only cells on the reference

The deployed alignment's hint-only cells are `Memory.refExtra`'s (`Bridge.extraOf` by index), and
the reference holds each value only hints read at its cell (`Ref.Ok.extra`), so `ExtraRef` holds.
-/

namespace LeanVM.Guest.EndExec

open LeanVM.Guest LeanVM.Guest.Memory LeanVM.Prover.Exec

public section

/-- **The reference holds each hint-only cell's value**, on the deployed alignment. -/
theorem extraRef_alignA : ExtraRef Bridge.alignA := by
  intro r hr I hI f σ bufs kids hIt v hv c hc
  have hκ : r.κ ≤ 28 := logMemorySize_le_28 (e := r.exec) hr.size
  obtain ⟨hlt, hrd⟩ := hr.extra I hI f σ bufs kids hIt v hv c hc
  exact (refRd_img hκ r.img (I.fp + c) (σ v) (by omega) hrd).2

end

end LeanVM.Guest.EndExec
