module

public import LeanVM.Cost.Bounds.Runner
public import LeanVM.Cost.Decoder.Replay
public import LeanVM.Cost.Prices

/-!
# Bound: the guest decoder's replay of the run, compiled

The price of the replay `Cost/Decoder/Replay.lean` compiles, **the decoder's big runtime term:
the run's steps times the step's price**. The step is the extractor's `stepVec` (`stepVec.c258`,
priced in `Bounds/Step.lean`'s `stepVec_cost`), not compiled again.

* **`statesVec_cost`**: one round per state replayed, each at most the step's price `S` and `46`
  (the comparison with the final registers, the fuel's decrement, a cons, the step's `match`; the
  fuel at most `2^128`, three limbs): `(S + 46)·|states|`;
* **`replayStatesOf_cost`**: on the address tables `powTable κ`, `powTable ℓ` (`κ ≤ 62`, `ℓ` the
  bytecode's `logSize`), at most `(runnerStepPrice κ ℓ + 46)·|states| + 2456`, `runnerStepPrice κ
  ℓ = 366000 + 36ℓ + 936κ` (`Cost/Prices.lean`) and `2456` the final registers (a
  power of `g`), the fuel and the initial registers, once. On a valid execution of `T` steps
  `|states| = T + 1` (the replay stops at the final state, `T < replayFuel`,
  `Located.steps_lt_replayFuel`).
-/

namespace LeanVM.Cost.Bounds

open LeanVM.Cost LeanVM.Cost.Decoder LeanVM.Parameters LeanVM.Semantics LeanVM.Extraction.Fast
open LeanVM.Guest.Located

public section

variable (P : LeanVM.Cost.MachineProgram)

/-- Numbers below `2^192` have at most three limbs. -/
theorem limbs_le_three {x : ℕ} (h : x < 2 ^ 192) : limbCount x ≤ 3 := by
  have := log2_lt_of (by norm_num) h
  unfold limbCount
  omega

/-- **The replay's rounds** (`statesVecC`): each state replayed at most the step's price `S` and
`48`, on a fuel of at most `2^128`. -/
theorem statesVec_cost (hP : Includes P statesVecC.costDeps)
    (memT codeT : Array (ℕ × ℕ)) (prog : Semantics.LeanIsaProgram) {κ : ℕ} (mem : Vector E (2 ^ κ))
    (fin : Registers K) (S : ℕ)
    (hS : ∀ r : Registers K, machineCost P Auto.LeanVM.Extraction.Fast.stepVec.c258.costIdx
      [encodeValue memT, encodeValue codeT, encodeValue prog, encodeValue κ, encodeValue mem,
        encodeValue r] ≤ S) :
    ∀ (n : ℕ) (r : Registers K), n ≤ 2 ^ 128 →
      machineCost P statesVecC.costIdx
        [encodeValue memT, encodeValue codeT, encodeValue prog, encodeValue κ, encodeValue mem,
          encodeValue fin, encodeValue n, encodeValue r] ≤
        (S + 46) * (statesVec memT codeT prog mem fin n r).length := by
  intro n
  induction n with
  | zero =>
    intro r _
    rw [statesVecC.costEq_zero P hP, statesVec]
    simp only [List.length_singleton]
    omega
  | succ n ih =>
    intro r hn
    rw [statesVecC.costEq_succ P hP, statesVec]
    have hl := limbs_le_three (by omega : n + 1 < 2 ^ 192)
    have hs := hS r
    by_cases hf : r = fin
    · simp only [ite_eq_left hf, List.length_singleton]
      split_ifs <;> omega
    · simp only [ite_eq_right hf]
      generalize hst : stepVec memT codeT prog mem r = o
      cases o with
      | none =>
        simp only [List.length_singleton]
        split_ifs <;> omega
      | some r' =>
        have := ih r' (by omega)
        simp only [List.length_cons]
        split_ifs <;> nlinarith

/-- **The replay of the run** (`replayStatesOfC`) on the address tables of the memory (`2^κ`
words) and the bytecode: `|states|` rounds, each at most one step's price
`runnerStepPrice κ ℓ` and `46`, and `2456` once. -/
theorem replayStatesOf_cost (hP : Includes P replayStatesOfC.costDeps) (prog :
    Semantics.LeanIsaProgram)
    {κ : ℕ} (hκ : κ ≤ 62) (mem : Vector E (2 ^ κ)) :
    machineCost P replayStatesOfC.costIdx
        [encodeValue (powTable κ), encodeValue (powTable prog.logSize), encodeValue prog,
          encodeValue κ, encodeValue mem] ≤
      (runnerStepPrice κ prog.logSize + 46) *
          (replayStatesOf (powTable κ) (powTable prog.logSize) prog mem).length + 2456 := by
  have hls : prog.logSize ≤ 32 := prog.logSize_le
  rw [replayStatesOfC.costEq P hP, Auto.LeanVM.Semantics.LeanIsaProgram.pcFinal.c242.costEq P (by includes),
    replayFuelC.costEq P (by includes)]
  have h1 := statesVec_cost P (by includes) (powTable κ) (powTable prog.logSize) prog mem
    (Registers.final prog) (runnerStepPrice κ prog.logSize) (fun r ↦ by
      have := stepVec_cost P (by includes) (powTable κ) (powTable prog.logSize)
        (wordTable_powTable hκ) (wordTable_powTable (by omega)) prog (by omega) mem r
      rw [powTable_size, powTable_size, Nat.log2_two_pow, Nat.log2_two_pow] at this
      unfold runnerStepPrice
      omega) replayFuel ⟨addressOfIndex 0, 1⟩ (le_of_eq rfl)
  have hp : 2 ^ prog.logSize ≤ 2 ^ 32 := Nat.pow_le_pow_right (by norm_num) hls
  have hp0 : 0 < 2 ^ prog.logSize := Nat.two_pow_pos _
  have h2 := powSq_cost P (by includes) g (2 ^ prog.logSize - 1) (by omega)
  have h3 := log2_lt_of (k := 32) (n := 2 ^ prog.logSize - 1) (by norm_num) (by omega)
  have h4 := powSq_cost P (by includes) g 0 (by norm_num)
  have h5 : limbCount (1 <<< 128) ≤ 3 := limbs_le_three (by rw [Nat.one_shiftLeft]; norm_num)
  rw [limbs_shift (by omega : prog.logSize < 64), limbs_of_lt (by omega : prog.logSize < 2 ^ 64),
    limbs_two_pow (by omega : prog.logSize < 64)]
  unfold replayStatesOf
  simp only [Nat.log2_zero] at h4
  omega

end

end LeanVM.Cost.Bounds
