module

public import NativeVm.Code.Phase7.RingPure
public import NativeVm.Code.Phase2.Kit

/-!
# Ring switching in the phase's frame

What `ringSwitchC`'s proof needs of the machine state beside the arithmetic: the model's state
survives a piece that writes only the working area from `ringR` on (`codeRel_high`), and a piece
that writes only `ringPure`'s words keeps the frame of the regions `[ringR, scratchR]`
(`Base.ringPure`).
-/

@[expose] public section

namespace NativeVm.Code.Ring

open Native NativeVm.Field NativeVm.Model LeanVM.Parameters
open NativeVm.Transcript (wd Fits Disj Env Foot ctxEnd scratchW wd_inj wd_ne_of_disj)

variable {env : Env} {inp : Input} {t : TState} {s₁ s₂ s0 : QState}

/-- The regions phase 7's ring part writes. -/
abbrev ringRegs : List Region := [ringR, scratchR]

/-- A word of the working area from `ringR` on. -/
def High (env : Env) (a : UInt64) : Prop := ∃ k, ringR.off ≤ k ∧ k < dataEnd ∧ a = wd env.work k

/-- **`CodeRel` through a piece writing only the working area from `ringR` on.** -/
theorem codeRel_high (h : CodeRel env t s₁) (hi : Inputs env inp s₁.mem)
    (hrdi : s₂.reg .rdi = s₁.reg .rdi) (hdom : ∀ a, (s₂.mem a).isSome = (s₁.mem a).isSome)
    (hm : ∀ a, ¬ High env a → s₂.mem a = s₁.mem a) : CodeRel env t s₂ := by
  obtain ⟨st, hr, hs, hstream, hop⟩ := h
  have hw : 85438 ≤ workWords inp.bytecode.size := by
    have := dataEnd_le inp.bytecode.size; rwa [dataEnd_val] at this
  have hfw := hi.fitWork
  have hro : ringR.off = 27931 := by decide
  have notH_ctx : ∀ k < ctxEnd, ¬ High env (wd env.ctx k) := fun k hk ⟨j, h1, h2, e⟩ ↦
    hi.ctx_ne_work hk (by rw [dataEnd_val] at h2; omega) e
  refine ⟨st, hr, hs.congrW (hrdi.trans hs.rdi) hdom (fun k hk ↦ hm _ (notH_ctx k ?_))
    (fun k hk ↦ hm _ ?_) (fun k hk ↦ hm _ ?_), hstream, hop⟩
  · rcases hk with hk | ⟨-, hk⟩
    · rw [Transcript.scratchW_val] at hk; rw [Transcript.ctxEnd_val]; omega
    · rw [Transcript.groundW_val] at hk; rw [Transcript.ctxEnd_val]; omega
  · rintro ⟨j, h1, h2, e⟩
    exact wd_ne_of_disj hs.layout.fitDec hfw hi.disjDec hk
      (by rw [dataEnd_val] at h2; omega) e
  · rintro ⟨j, h1, h2, e⟩
    rw [Transcript.workWords_val] at hk; rw [dataEnd_val] at h2
    have := (wd_inj (by omega) (by omega)).mp e
    omega

/-- **`ringPure`'s words keep the frame** of the regions `[ringR, scratchR]`. -/
theorem Base.ringPure (hb : Base env ringRegs s0 s₁) (hrdi : s₂.reg .rdi = s₁.reg .rdi)
    (hdom : ∀ a, (s₂.mem a).isSome = (s₁.mem a).isSome)
    (hm : ∀ a, (∀ k < 130, a ≠ ew env.work (tgO + k)) → (∀ k < 130, a ≠ ew env.work (imgO + k)) →
      s₂.mem a = s₁.mem a) : Base env ringRegs s0 s₂ := by
  obtain ⟨-, -, -, -, h5, -⟩ := offs_eq
  have h2 : imgO = scratchR.off + 32 := offs_eq.2.1
  have hs : ringR.size = 130 ∧ 32 + 130 ≤ scratchR.size := by decide
  refine ⟨⟨hrdi.trans hb.1.1, fun a hf hr ↦ ?_⟩, fun a ↦ (hdom a).trans (hb.2 a)⟩
  rw [hm a (fun k hk e ↦ hr ringR (by simp) ⟨k, by omega, by rw [e, ← h5]; rfl⟩)
    (fun k hk e ↦ hr scratchR (by simp) ⟨32 + k, by omega, by
      rw [e, h2, Nat.add_assoc]; rfl⟩)]
  exact hb.1.2 a hf hr

/-- **`CodeRel` through `ringPure`'s words.** -/
theorem codeRel_ringPure (h : CodeRel env t s₁) (hi : Inputs env inp s₁.mem)
    (hrdi : s₂.reg .rdi = s₁.reg .rdi) (hdom : ∀ a, (s₂.mem a).isSome = (s₁.mem a).isSome)
    (hm : ∀ a, (∀ k < 130, a ≠ ew env.work (tgO + k)) → (∀ k < 130, a ≠ ew env.work (imgO + k)) →
      s₂.mem a = s₁.mem a) : CodeRel env t s₂ := by
  refine codeRel_high h hi hrdi hdom fun a ha ↦ hm a (fun k hk e ↦ ha ⟨tgO + k, ?_, ?_, e⟩)
    (fun k hk e ↦ ha ⟨imgO + k, ?_, ?_, e⟩)
  all_goals
    have : ringR.off = 27931 := by decide
    have : tgO = 27931 := rfl
    have : imgO = 52702 := rfl
    have : dataEnd = 85438 := dataEnd_val
    omega

end NativeVm.Code.Ring
