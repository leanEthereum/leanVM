/-
  Rv64mc.Probe.StepMeet

  The statement's machine as the meet of riscv-zkvm's two: a step of `step` is a step of SP1's `stepSp1`
  (`step_stepSp1`) and of the generic `RiscvZkvm.Rv64.step` (`step_step`). Its memory check `memOk` is SP1's
  (`memOkSp1`, which asks a store not to hit code) and the guest's windows (`link.x`), each access wholly inside
  one; `ECALL` is no step of it, so a run of it stops at the halting `ECALL`. `notes/step-meet.md` says why.
-/

import RiscvZkvm.Rv64.StepOn

namespace Rv64mc.Probe

open RiscvZkvm.Rv64

/-- The guest's data windows (`guest/link.x`, `guest/src/main.rs`): the input and the heap,
    `0x10000000..0x78000000`; `.rodata`, `.data`, `.bss` and the stack, `0xa0000000..0xc0000000`. -/
def inWindow (a : Word) (w : Nat) : Bool :=
  (decide (0x10000000 ≤ a.toNat) && decide (a.toNat + w ≤ 0x78000000)) ||
    (decide (0xa0000000 ≤ a.toNat) && decide (a.toNat + w ≤ 0xc0000000))

/-- A memory access is in a window, wholly, and passes SP1's check. -/
def memOk (s : MachineState) (i : Instr) : Bool :=
  memOkSp1 s i && match memAccess s i with
    | none => true
    | some (a, w, _) => inWindow a w

/-- **One step of the statement's machine**: no step at `ECALL`, `EBREAK`, ZisK's `CSRS` or where there is no
    code; a memory access only where `memOk` holds. -/
def step (s : MachineState) : Option MachineState :=
  match s.code s.pc with
  | none | some .ECALL | some .EBREAK | some (.CSRS ..) => none
  | some i => if memOk s i then some (execInstrBr s i) else none

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

end Rv64mc.Probe
