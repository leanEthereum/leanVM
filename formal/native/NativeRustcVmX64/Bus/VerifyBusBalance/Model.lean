module

public import NativeVm.Model.Bus
public import NativeRustcVm.Sumcheck.Model

/-!
# `verifyBusBalance` as `verify_bus_balance` runs it

- `fwRows`, `pushL`, `pullL`, `countL`: the framework sizes and the three sides' layouts.
- `resultOf`: the bus's result from the values the transcript gave.
- `tailRun`: the run from the memory's scalars on.
- `vbb_run`: `verifyBusBalance` step by step.
- `busGrindingBits_eq`, `bitLength_mask`: the grind's bit count, as the Rust computes it.
- `bytecodeShare_run`, `bytecodeShare_size`: the share step by step, its point `bytecode_low` and
  four slot coordinates; `cbv_run`: `computedBytecodeValue` accepts or rejects.
-/

namespace NativeRustcVmX64.Bus.VerifyBusBalance

open NativeVm.Model NativeRustcVm.Sumcheck
open LeanVM.Protocol.Verifier (busGrindingBits bitLength memory0 memory1 memoryFinalCounters
  bytecodeFinalCounters busBits)

@[expose] public section

/-- `[0, log_memory, log_bytecode]`. -/
def fwRows (L : LayoutW) : Array Nat := #[0, L.logMemory, L.logBytecode]

/-- The push side's layout. -/
abbrev pushL (L : LayoutW) : BusLayoutW := busLayout (fwRows L) L.push
/-- The pull side's layout. -/
abbrev pullL (L : LayoutW) : BusLayoutW := busLayout (fwRows L) L.pull
/-- The count side's layout. -/
abbrev countL (L : LayoutW) : BusLayoutW := busLayout #[] L.count

/-- The four framework column claims. -/
def claimsOf (L : LayoutW) (pt mem : Array EW) (mf bf : EW) : Array ColumnClaimW :=
  #[⟨memory0, pt.extract 0 L.logMemory, mem.getD 0 0⟩,
    ⟨memory1, pt.extract 0 L.logMemory, mem.getD 1 0⟩,
    ⟨memoryFinalCounters, pt.extract 0 L.logMemory, mf⟩,
    ⟨bytecodeFinalCounters, pt.extract 0 L.logBytecode, bf⟩]

/-- The empty forms. -/
def forms0 : Array (Array FormW) := tablesW.map fun _ ↦ #[#[], #[], #[]]

/-- The push side's forms and total. -/
def acc0 (L : LayoutW) (w : Array EW) (beta : EW) (pt tv mem : Array EW) (share : EW) :
    Array (Array FormW) × EW :=
  accumulateSide forms0 0 L.push (pushL L)
    (fingerprints w mem (pt.extract 0 L.logMemory) (pt.extract 0 L.logBytecode) share (gpow 0) 1 1)
    w beta pt (tv.getD 0 0)

/-- The pull side's forms and total. -/
def acc1 (L : LayoutW) (w : Array EW) (beta : EW) (pt tv mem : Array EW) (mf bf share : EW) :
    Array (Array FormW) × EW :=
  accumulateSide (acc0 L w beta pt tv mem share).1 1 L.pull (pullL L)
    (fingerprints w mem (pt.extract 0 L.logMemory) (pt.extract 0 L.logBytecode) share
      (gpow (2 ^ L.logBytecode - 1)) mf bf)
    w beta pt (tv.getD 1 0)

/-- The count side's forms and total. -/
def acc2 (L : LayoutW) (w : Array EW) (beta : EW) (pt tv mem : Array EW) (mf bf share : EW) :
    Array (Array FormW) × EW :=
  accumulateSide (acc1 L w beta pt tv mem mf bf share).1 2 L.count (countL L) #[] #[1] 0 pt
    (tv.getD 2 0)

/-- **The bus's result.** -/
def resultOf (L : LayoutW) (w : Array EW) (beta : EW) (pt tv mem : Array EW) (mf bf share : EW)
    (bp : Array EW) : BusResultW :=
  ⟨claimsOf L pt mem mf bf, bp, pt, (acc2 L w beta pt tv mem mf bf share).1,
    #[(acc0 L w beta pt tv mem share).2, (acc1 L w beta pt tv mem mf bf share).2,
      (acc2 L w beta pt tv mem mf bf share).2]⟩

/-- **The run from the memory's scalars on.** -/
def tailRun (L : LayoutW) (w : Array EW) (beta : EW) (pt tv : Array EW) (s : TState) :
    Option (BusResultW × TState) :=
  ((readScalars 2).run s).bind fun y1 ↦ (readScalar.run y1.2).bind fun y2 ↦
    (readScalar.run y2.2).bind fun y3 ↦
      ((bytecodeShare w (pt.extract 0 L.logBytecode)).run y3.2).bind fun y4 ↦
        ((computedBytecodeValue L.bytecode y4.1.2.1 y4.1.2.2).run y4.2).bind fun y5 ↦
          some (resultOf L w beta pt tv y1.1 y2.1 y3.1 y4.1.1 y4.1.2.1, y5.2)

/-- **`verifyBusBalance` step by step.** -/
theorem vbb_run (L : LayoutW) (s0 : TState) :
    (verifyBusBalance L).run s0 =
      if (pushL L).depth < 64 then
        ((grind (busGrindingBits (pushL L).depth)).run s0).bind fun x1 ↦
          ((sampleChallenges 16).run x1.2).bind fun x2 ↦
            (sampleChallenge.run x2.2).bind fun x3 ↦
              ((verifyGkrGrandProducts (pushL L).depth).run x3.2).bind fun x4 ↦
                ((require (x4.1.1 != 0)).run x4.2).bind fun x5 ↦
                  tailRun L x2.1 x3.1 x4.1.2.1 x4.1.2.2 x5.2
      else none := by
  by_cases h : (busLayout #[0, L.logMemory, L.logBytecode] L.push).depth < 64
  · simp only [show (pushL L).depth < 64 from h, ↓reduceIte]
    unfold verifyBusBalance
    dsimp only
    rw [show require (decide ((busLayout #[0, L.logMemory, L.logBytecode] L.push).depth < 64)) =
        pure () from by simp only [require, h, decide_true, ↓reduceIte]]
    simp only [StateT.run_bind, pure_bind, Option.bind_eq_bind]
    rfl
  · simp only [show ¬(pushL L).depth < 64 from h, ↓reduceIte]
    unfold verifyBusBalance
    dsimp only
    rw [show require (decide ((busLayout #[0, L.logMemory, L.logBytecode] L.push).depth < 64)) =
        reject from by simp only [require, h, decide_false, Bool.false_eq_true, ↓reduceIte]]
    rfl

/-- The grind's bit count. -/
theorem busGrindingBits_eq (d : Nat) : busGrindingBits d = d - 3 := by
  unfold busGrindingBits LeanVM.Protocol.Compile.grindingBits LeanVM.Protocol.Compile.securityBits
  rcases d with _ | d
  · rfl
  · have h1 : ¬ 2 ^ (d + 1) ≤ 1 := by
      have := Nat.one_lt_two_pow (n := d + 1) (by omega); omega
    have h2 : (2 ^ (d + 1) - 1).log2 = d :=
      (Nat.log2_eq_iff (by have := Nat.one_lt_two_pow (n := d + 1) (by omega); omega)).mpr
        ⟨by have := Nat.one_le_two_pow (n := d); rw [Nat.pow_succ]; omega, by omega⟩
    simp only [h1, ↓reduceIte, h2]

/-- The bit length of `2^d - 1` is `d`. -/
theorem bitLength_mask (d : Nat) : bitLength (2 ^ d - 1) = d := by
  unfold bitLength
  rcases d with _ | d
  · rfl
  · have h1 : 2 ^ (d + 1) - 1 ≠ 0 := by
      have := Nat.one_lt_two_pow (n := d + 1) (by omega); omega
    have h2 : (2 ^ (d + 1) - 1).log2 = d :=
      (Nat.log2_eq_iff h1).mpr
        ⟨by have := Nat.one_le_two_pow (n := d); rw [Nat.pow_succ]; omega, by omega⟩
    simp only [h1, ↓reduceIte, h2]

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
  rw [bytecodeShare_run] at h
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

end NativeRustcVmX64.Bus.VerifyBusBalance
