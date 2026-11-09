module

public import LeanVM.Cost.Decoder.Equations

/-!
# Bound: the replay's length

The replay (`replayStatesOf`, `Cost/Decoder/Replay.lean`) lists the states of the run from
`(g^0, 1)` up to the final state: on a valid execution of `T` steps, **`T + 1` of them at most**
(`replayStatesOf_length`). Through `replayStatesOf_eq` and `Located.statesTable_eq`, it is
`Located.statesIn`, whose states the run reaches one step each (`statesIn_length_le`: a run
halting after `T` steps lists at most `T + 1` states, whatever the fuel). The decoder's entry
table files each of them once (`Bounds/Decoder/EntryTable.lean`).
-/

namespace LeanVM.Cost.Bounds

open LeanVM.Cost LeanVM.Cost.Decoder LeanVM.Parameters LeanVM.Semantics LeanVM.Extraction
open LeanVM.Extraction.Fast LeanVM.Guest.Located LeanVM.Protocol.Halting

public section

/-- **A run halting after `T` steps lists at most `T + 1` states**, whatever the fuel. -/
theorem statesIn_length_le {memIdx codeIdx : Std.HashMap UInt64 ℕ} {prog : LeanIsaProgram} {κ : ℕ}
    {L : MemoryImage κ} (hS : ∀ r, stepIn memIdx codeIdx prog L r = step prog L r) :
    ∀ (T fuel : ℕ) (r : Registers K),
      LeanVM.Semantics.run prog L T r = some (Registers.final prog) →
      (statesIn memIdx codeIdx prog L fuel r).length ≤ T + 1
  | 0, fuel, r, h => by
    obtain rfl : r = Registers.final prog := Option.some.inj h
    cases fuel <;> simp [statesIn]
  | T + 1, 0, r, _ => by simp [statesIn]
  | T + 1, fuel + 1, r, h => by
    rw [statesIn]
    by_cases hf : r = Registers.final prog
    · simp [hf]
    · rw [run_succ_of_ne_final hf] at h
      obtain ⟨r', hr', h'⟩ := Option.bind_eq_some_iff.1 h
      rw [ite_eq_right hf, hS, hr']
      have := statesIn_length_le hS T fuel r' h'
      simp only [List.length_cons]
      omega

/-- **The replay's length**: on a valid execution of the guest, at most its steps and one. -/
theorem replayStatesOf_length {input : PublicInput} {t : Execution LeanVM.Guest.guestProgram}
    (hv : ValidExecution LeanVM.Guest.guestProgram input t) :
    (replayStatesOf (powTable t.logMemorySize) (powTable LeanVM.Guest.guestProgram.logSize)
      LeanVM.Guest.guestProgram (memoryVector t.memory)).length ≤ t.stepCount + 1 := by
  obtain ⟨κ, L, T⟩ := t
  have h32 : κ ≤ maxLogMem := hv.1.2.1
  have hκ : κ < 64 := by unfold maxLogMem at h32; omega
  have hT : LeanVM.Semantics.run LeanVM.Guest.guestProgram L T ⟨addressOfIndex 0, 1⟩ =
      some (Registers.final LeanVM.Guest.guestProgram) :=
    LeanVM.Guest.safe_of_validExecution hv
  show (replayStatesOf (powTable κ) (powTable LeanVM.Guest.guestProgram.logSize) LeanVM.Guest.guestProgram
    (memoryVector L)).length ≤ T + 1
  rw [replayStatesOf_eq, memoryVector_get, statesTable_eq hκ]
  exact statesIn_length_le (stepIn_powIndex hκ L) T replayFuel _ hT


/-- **A valid execution of the guest takes fewer than `2^128` steps** (`Located.steps_lt_replayFuel`:
a halting run repeats no state). -/
theorem steps_lt_of_valid {input : PublicInput} {t : Execution LeanVM.Guest.guestProgram}
    (hv : ValidExecution LeanVM.Guest.guestProgram input t) : t.stepCount < 2 ^ 128 := by
  obtain ⟨κ, L, T⟩ := t
  have hT : LeanVM.Semantics.run LeanVM.Guest.guestProgram L T ⟨addressOfIndex 0, 1⟩ =
      some (Registers.final LeanVM.Guest.guestProgram) :=
    LeanVM.Guest.safe_of_validExecution hv
  exact LeanVM.Guest.Located.steps_lt_replayFuel hT

end

end LeanVM.Cost.Bounds
