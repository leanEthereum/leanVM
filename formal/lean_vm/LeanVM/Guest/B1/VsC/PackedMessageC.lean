/-
  LeanVM.Guest.B1.VsC.PackedMessageC

  `packed_message__L144` completes, layout-free.
-/

module

public import LeanVM.Guest.B1.VsC.Fwd
public import LeanVM.Guest.B1.Link.PackedMessage
import LeanVM.Guest.CoreRef

/-!
# `packed_message`, complete

`packed_message(fs0..fs4, msg, 144)` loads the `144` words at `msg` and permutes, asserting and
hinting nothing. `packed_message_complete`: on every memory holding `xs` at `msg`, the call returns
the challenge and capacity of the soundness stream's meaning (`MeaningPM`), popping nothing, exact.
-/

namespace LeanVM.Guest.B1.VsC

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.B1
open LeanVM.Guest.B1.Link LeanVM.Guest.Complete LeanVM.Guest.B1.Fwd LeanVM.Protocol.Verifier

@[expose] public section

theorem pm_checks : pureChecks 6 [(5, 144)] (fn% «packed_message__L144»).body = true := by decide +kernel

/-- **`packed_message__L144` completes** on the `144` words `xs` at `msg`. -/
theorem packed_message_complete (kd : ℕ) (f0 f1 f2 f3 f4 msg : E) (xs : List E) (hxs : xs.length = 144) :
    CallCompletes0 kd "packed_message__L144" [f0, f1, f2, f3, f4, msg]
      ((Fs.squeeze ⟨pkAbsorb 18 xs [f0, f1, f2, f3, f4], []⟩).1 ::
        (Fs.squeeze ⟨pkAbsorb 18 xs [f0, f1, f2, f3, f4], []⟩).2.cap)
      (fun rd ↦ ReadsAt rd msg xs) PostQuiet := by
  refine callCompletes0_pure [(5, 144)] (coreProgram_find?_at (j := idx% «packed_message__L144») rfl) rfl
    pm_checks (by simp) (fun rd _ h q hq ↦ ?_) ?_
  · simp only [List.mem_singleton] at hq
    subst hq
    exact ⟨xs, by omega, h⟩
  · rintro rd - h rets' hR
    obtain ⟨xs', hl, hr, rfl⟩ := packed_message_sound rd _ _ hR
    rw [readsAt_eq hr h (by omega)]

end
end LeanVM.Guest.B1.VsC
