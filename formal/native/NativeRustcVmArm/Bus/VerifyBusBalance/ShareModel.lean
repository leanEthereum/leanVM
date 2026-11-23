module

public import NativeRustcVmArm.Bus.VerifyBusBalance.Model
public import NativeRustcVmArm.Bus.BytecodeShare.Common
public import NativeRustcVm.Sumcheck.Model

/-!
# The bytecode share's point, the bytecode's value: model facts

- `sumcheckFn_size`: `n` rounds give `n` challenges.
- `bytecodeShare_size`: the bytecode point is `bytecode_low` and the four slot coordinates.
- `cbv_run`: `computedBytecodeValue` accepts or rejects, the transcript as it was.
-/

namespace NativeRustcVmArm.Bus.VerifyBusBalance

open NativeVm.Model NativeRustcVm.Sumcheck
open LeanVM.Protocol.Verifier (busBits)

public section

/-- **`n` rounds give `n` challenges.** -/
theorem sumcheckFn_size {claim : EW} {count : Nat} {E : Nat → Option EW} :
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
      have ih := sumcheckFn_size n h0
      rw [h0, Option.bind_some] at h
      simp only [sumcheckRound, bind, StateT.bind, pure, StateT.pure] at h
      cases h1 : sumcheckRoundPoly count c0 (E n) s0 with
      | none => simp [h1] at h
      | some q =>
        cases h2 : sampleChallenge q.2 with
        | none => simp [h1, h2] at h
        | some r =>
          simp [h1, h2] at h
          obtain ⟨⟨rfl, -⟩, -⟩ := h
          simp [ih]

/-- **The bytecode point**: `bytecode_low` and the slot's four coordinates. -/
theorem bytecodeShare_size {w bl : Array EW} {s s' : TState} {x : EW × Array EW × EW}
    (h : (bytecodeShare w bl).run s = some (x, s')) : x.2.1.size = bl.size + 4 := by
  rw [BytecodeShare.bytecodeShare_run] at h
  cases h1 : readScalar.run s with
  | none => rw [h1] at h; cases h
  | some a =>
    rw [h1, Option.bind_some] at h
    cases h2 : (sumcheckPlain a.1 3 busBits).run a.2 with
    | none => rw [h2] at h; cases h
    | some y =>
      rw [h2, Option.bind_some] at h
      cases h3 : readScalar.run y.2 with
      | none => rw [h3] at h; cases h
      | some z =>
        rw [h3, Option.bind_some] at h
        split at h
        · cases h
          obtain ⟨⟨pt, c⟩, s2⟩ := y
          have := sumcheckFn_size (E := fun _ ↦ none) (claim := a.1) (count := 3) busBits
            (s := a.2) (by rw [sumcheckFn_none]; exact h2)
          simp only [Array.size_append]
          rw [this]
          rfl
        · cases h

/-- **`computedBytecodeValue`** accepts or rejects. -/
theorem cbv_run (words : Array UInt64) (p : Array EW) (v : EW) (s : TState) :
    (computedBytecodeValue words p v).run s =
      if (multilinearEval (words.map EW.ofK) p == v) = true then some ((), s) else none := by
  unfold computedBytecodeValue require
  split <;> rfl

end

end NativeRustcVmArm.Bus.VerifyBusBalance
