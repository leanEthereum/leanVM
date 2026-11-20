/-
  Rv64mc.StepMeet

  The statement's machine (`EndStatement.step`) as the meet of riscv-zkvm's two: a step of it is a step of SP1's
  `stepSp1` (`step_stepSp1`), the machine machine-checked's `SafeN` is about, and of the generic
  `RiscvZkvm.Rv64.step` (`step_step`). `notes/step-meet.md` says why.
-/

import Rv64mc.EndStatement

namespace Rv64mc

open RiscvZkvm.Rv64

/-- A step of `step` is one of SP1's. -/
theorem step_stepSp1 {s t : MachineState} (h : step s = some t) : stepSp1 s = some t := by
  unfold step at h
  unfold stepSp1
  cases hc : s.code s.pc with
  | none => simp [hc] at h
  | some i =>
    rw [hc] at h
    cases i <;> simp_all [memOk, Instr.isMemAccess]

/-- A step of `step` is one of riscv-zkvm's generic `step`. -/
theorem step_step {s t : MachineState} (h : step s = some t) : RiscvZkvm.Rv64.step s = some t := by
  unfold step at h
  unfold RiscvZkvm.Rv64.step
  cases hc : s.code s.pc with
  | none => simp [hc] at h
  | some i =>
    rw [hc] at h
    cases i <;> simp_all [memOk, memOkSp1, memAccess, inWindow, alignedFor, isValidByteAccess,
      isValidHalfwordAccess, MEM_START, MEM_END, RAM_MEM_START, RAM_MEM_END, INPUT_MEM_START, INPUT_MEM_END] <;>
      omega

end Rv64mc
