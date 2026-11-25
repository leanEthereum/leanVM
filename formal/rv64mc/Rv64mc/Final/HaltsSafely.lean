/-
  Rv64mc.Final.HaltsSafely

  What `HaltsSafely` (`EndStatement.lean`) says of the runs of the statement's machine. `step` is
  a function and stops at every `ECALL`, so a halting run is the only run: `Halts` is
  deterministic (`Halts.unique`), every run that stops stops at the halting `ECALL`, which is
  `TrapFree` for the inputs `HaltsSafely` covers (`stops_at_halt`), and no run goes on past it
  (`steps_eq_none`). That its loader is satisfiable is `loaded_bounded` (`Final/EndT.lean`).

  ## Main results

  * `Halts.unique`, `stops_at_halt`, `steps_eq_none`
-/

import Rv64mc.EndStatement

namespace Rv64mc

open RiscvZkvm.Rv64

theorem steps_add (a b : Nat) (s : MachineState) : steps (a + b) s = (steps a s).bind (steps b) := by
  induction a generalizing s with
  | zero => simp [steps]
  | succ a ih =>
    rw [Nat.succ_add]
    simp only [steps]
    cases step s with
    | none => rfl
    | some s' => exact ih s'

/-- A stopped machine takes no step. -/
theorem steps_stuck {t : MachineState} (h : step t = none) (k : Nat) : steps (k + 1) t = none := by
  simp [steps, h]

/-- The machine stops at every `ECALL`. -/
theorem step_ecall {t : MachineState} (h : t.code t.pc = some .ECALL) : step t = none := by
  simp [step, h]

/-- Two runs from `s` that stop are the same run. -/
theorem steps_stop_unique {s t t' : MachineState} {n n' : Nat} (h : steps n s = some t) (hs : step t = none)
    (h' : steps n' s = some t') (hs' : step t' = none) : n = n' ∧ t = t' := by
  rcases Nat.lt_trichotomy n n' with hlt | rfl | hgt
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_lt hlt
    rw [Nat.add_assoc, steps_add, h, Option.bind_some, steps_stuck hs] at h'
    cases h'
  · rw [h] at h'
    exact ⟨rfl, Option.some.inj h'⟩
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_lt hgt
    rw [Nat.add_assoc, steps_add, h', Option.bind_some, steps_stuck hs'] at h
    cases h

/-- **`Halts` is deterministic**: the number of steps and the verdict. -/
theorem Halts.unique {s : MachineState} {n n' : Nat} {v v' : Word} (h : Halts s n v) (h' : Halts s n' v') :
    n = n' ∧ v = v' := by
  obtain ⟨t, ht, hc, -, hv⟩ := h
  obtain ⟨t', ht', hc', -, hv'⟩ := h'
  obtain ⟨rfl, rfl⟩ := steps_stop_unique ht (step_ecall hc) ht' (step_ecall hc')
  exact ⟨rfl, hv.symm.trans hv'⟩

/-- **`TrapFree`, for the inputs `HaltsSafely` covers**: every run of the loaded image that stops, stops at the
    halting `ECALL`. -/
theorem stops_at_halt {img : Image} (h : HaltsSafely img) {words : List Word} {s t : MachineState} {n : Nat}
    (hw : words.length < maxInputWords) (hl : Loaded img words s) (hn : steps n s = some t) (hs : step t = none) :
    t.code t.pc = some .ECALL ∧ t.getReg .x5 = 0 := by
  obtain ⟨n₀, v, ⟨t₀, h₀, hc, h5, -⟩, -⟩ := h words s hw hl
  obtain ⟨-, rfl⟩ := steps_stop_unique hn hs h₀ (step_ecall hc)
  exact ⟨hc, h5⟩

/-- **No run goes on past the halt**: from a halting run of `n` steps, every run of more steps is none. -/
theorem steps_eq_none {s : MachineState} {n : Nat} {v : Word} (h : Halts s n v) {k : Nat} (hk : n < k) :
    steps k s = none := by
  obtain ⟨t, ht, hc, -⟩ := h
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_lt hk
  rw [Nat.add_assoc, steps_add, ht, Option.bind_some, steps_stuck (step_ecall hc)]

end Rv64mc
