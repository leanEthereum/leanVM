module

public import NativeVm.Model.Bus
public import NativeRustcVm.Sumcheck.Model
public import NativeRustcVm.Sumcheck.RoundPoly

/-!
# `bytecodeShare`'s model, as `bytecode_share` runs it

- `sumcheckFn_size`, `sumcheckPlain_size`: `n` rounds of the sumcheck return `n` challenges.
- `bytecodeShare_run`: `bytecodeShare` step by step.
-/

namespace NativeRustcVmX64.Bus.BytecodeShare

open NativeVm.Model NativeRustcVm.Sumcheck
open LeanVM.Protocol.Verifier (busBits)

public section

/-- `n` rounds of the sumcheck return `n` challenges. -/
theorem sumcheckFn_size (claim : EW) (count : Nat) (E : Nat → Option EW) :
    ∀ (n : Nat) {s s' : TState} {xs : Array EW} {c : EW},
      sumcheckFn claim count E n s = some ((xs, c), s') → xs.size = n
  | 0, s, s', xs, c, h => by
    rw [sumcheckFn_zero] at h
    cases h
    rfl
  | n + 1, s, s', xs, c, h => by
    rw [sumcheckFn_succ_apply] at h
    cases h0 : sumcheckFn claim count E n s with
    | none => rw [h0] at h; cases h
    | some p =>
      obtain ⟨⟨xs0, c0⟩, s0⟩ := p
      rw [h0, Option.bind_some] at h
      have ih := sumcheckFn_size claim count E n h0
      simp only [sumcheckRound, bind, StateT.bind, pure, StateT.pure] at h
      cases h1 : sumcheckRoundPoly count c0 (E n) s0 with
      | none => rw [h1] at h; cases h
      | some q =>
        rw [h1] at h
        simp only [Option.bind_some] at h
        cases h2 : sampleChallenge q.2 with
        | none => rw [h2] at h; cases h
        | some r =>
          rw [h2] at h
          simp only [Option.bind_some, Option.some.injEq, Prod.mk.injEq] at h
          rw [← h.1.1, Array.size_push, ih]

/-- The plain sumcheck of `n` rounds returns `n` challenges. -/
theorem sumcheckPlain_size {claim : EW} {count n : Nat} {s s' : TState} {xs : Array EW} {c : EW}
    (h : (sumcheckPlain claim count n).run s = some ((xs, c), s')) : xs.size = n := by
  rw [← sumcheckFn_none] at h
  exact sumcheckFn_size _ _ _ n h

/-- **`bytecodeShare` step by step.** -/
theorem bytecodeShare_run (w bl : Array EW) (s : TState) :
    (bytecodeShare w bl).run s =
      (readScalar.run s).bind fun x ↦ ((sumcheckPlain x.1 3 busBits).run x.2).bind fun y ↦
        (readScalar.run y.2).bind fun z ↦
          if (y.1.2 == dot (eqKernel y.1.1) w * z.1) = true then
            some ((x.1, bl ++ y.1.1, z.1), z.2)
          else none := by
  simp only [bytecodeShare, StateT.run, bind, StateT.bind, pure, StateT.pure, require]
  cases readScalar s with
  | none => rfl
  | some x =>
    simp only [Option.bind_some]
    cases sumcheckPlain x.1 3 busBits x.2 with
    | none => rfl
    | some y =>
      simp only [Option.bind_some]
      cases readScalar y.2 with
      | none => rfl
      | some z =>
        simp only [Option.bind_some]
        by_cases hc : (y.1.2 == dot (eqKernel y.1.1) w * z.1) = true <;>
          simp [hc, StateT.pure, reject]

end

end NativeRustcVmX64.Bus.BytecodeShare
