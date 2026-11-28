module

public import NativeRustcVmArm.Whir.GlueLevel.Mem

/-!
# WHIR's state across changes

`WhirStateAt.agree`: the state at `p` kept by a change agreeing on its bytes. `WhirStateAt.fold`:
`fold_round`'s writes, the claim, the `α`s' count and the new `α`, give the folded state.
-/

namespace NativeRustcVmArm.Whir

open NativeVm.Model NativeRustcVm.Whir
open NativeRustcVm (WordAt EWAt EWsAt BufEWAt)
open NativeRustcVm.Transcript (off off_off off_zero Agree)

public section

variable {d d' : Mem 64} {p : BitVec 64} {w : WhirStateW}

/-- **The state kept.** -/
theorem _root_.NativeRustcVm.Whir.WhirStateAt.agree (h : WhirStateAt d p w)
    (hA : Agree d d' p stateBytes (fun _ ↦ False)) : WhirStateAt d' p w where
  claim := ewAt_of_agree hA (by decide) h.claim
  alphas := bufEWAt_of_agree (agree_sub hA (o := 16) (k := 488) (by decide) fun _ _ ↦ id)
    (by decide) h.alphas
  glued_le := h.glued_le
  glued_len := wordAt_of_agree (agree_sub hA (o := 504) (k := 8) (by decide) fun _ _ ↦ id)
    le_rfl h.glued_len
  glued i hi := gluedAt_of_agree (agree_sub hA (o := 504 + 8 + 6064 * i) (k := 6064) (by
    have := h.glued_le
    have hi' : i < w.glued.size := hi
    show 504 + 8 + 6064 * i + 6064 ≤ 61152
    unfold gluedCap at this
    omega) fun _ _ ↦ id) (h.glued i hi)

/-- **A fold round's writes**: the claim `c`, the `α`s' count, the new `α` `x`. -/
theorem _root_.NativeRustcVm.Whir.WhirStateAt.fold (h : WhirStateAt d p w)
    (hlt : w.alphas.size < stackCap) {c x : EW}
    (hA : Agree d d' p stateBytes fun j ↦ j < 24 ∨
      (24 + 16 * w.alphas.size ≤ j ∧ j < 40 + 16 * w.alphas.size))
    (hc : EWAt d' p c) (hn : WordAt d' (off p 16) (w.alphas.size + 1).toUInt64)
    (hx : EWAt d' (off p (24 + 16 * w.alphas.size)) x) :
    WhirStateAt d' p { w with claim := c, alphas := w.alphas.push x } := by
  have hl : w.alphas.size ≤ 29 := by unfold stackCap at hlt; omega
  obtain ⟨-, -, hxs⟩ := h.alphas
  refine ⟨hc, ⟨by simp [stackCap]; omega, by simpa [alphasOff] using hn, ?_⟩, h.glued_le, ?_,
    fun i hi ↦ ?_⟩
  · simp only [Array.toList_push]
    rw [NativeRustcVm.ewsAt_append_iff, NativeRustcVm.ewsAt_singleton_iff]
    refine ⟨?_, ?_⟩
    · have hxs' : EWsAt d (off p 24) w.alphas.toList := by
        have := hxs
        rwa [show off p alphasOff + 8#64 = off p 24 from off_off p 16 8] at this
      rw [show off p alphasOff + 8#64 = off p 24 from off_off p 16 8]
      refine bytesAt_of_agree (agree_sub hA (o := 24) (k := 16 * w.alphas.size) (by
        show 24 + 16 * w.alphas.size ≤ 61152; omega) fun j hj hw ↦ by omega) ?_ hxs'
      rw [NativeRustcVm.length_ewsBytes]; simp
    · rw [show off p alphasOff + 8#64 = off p 24 from off_off p 16 8,
        NativeRustcVm.Transcript.off_add,
        show 24 + 16 * w.alphas.toList.length = 24 + 16 * w.alphas.size by simp]
      exact hx
  · exact wordAt_of_agree (agree_sub hA (o := 504) (k := 8) (by decide) fun j hj hw ↦ by omega)
      le_rfl h.glued_len
  · have := h.glued_le
    have hi' : i < w.glued.size := hi
    exact gluedAt_of_agree (agree_sub hA (o := 504 + 8 + 6064 * i) (k := 6064) (by
      show 504 + 8 + 6064 * i + 6064 ≤ 61152
      unfold gluedCap at this
      omega) fun j hj hw ↦ by omega) (h.glued i hi)

end

end NativeRustcVmArm.Whir
