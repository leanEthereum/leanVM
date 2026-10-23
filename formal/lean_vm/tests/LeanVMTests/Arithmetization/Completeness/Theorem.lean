import LeanVM.Arithmetization.Completeness.Theorem
import LeanVMTests.Arithmetization.Completeness.Fixture

/-!
# Tests: constraint completeness

`constraintCompleteness` is inhabited. The trace of `Fixture` is a valid execution, one `JUMP` to
the sentinel on an image where no `XOR` executes at all. The theorem gives it a witness that
satisfies the statement and represents the trace itself, and whose tables hold the run's rows: one
`JUMP` row, and an empty `XOR` table, which the image could not give a row anyway
(`badImage_no_xor`). A table of any number of rows, zero included, is within the caps: the protocol
pads it with public padding rows that are not on the bus.
-/

namespace LeanVMTests.Arithmetization.Completeness.Theorem

open LeanVM.Parameters LeanVM.Semantics LeanVM.Arithmetization
open LeanVMTests.Arithmetization.Completeness.Fixture

/-- **Completeness at an instance.** The witness exists and represents the trace. -/
theorem bad_trace_complete :
    ∃ w, SatisfiedBy jumpProg badInput w ∧ AssignmentRepresents w badTrace :=
  constraintCompleteness badTrace_valid (by decide)

/-- The run has one row, a `JUMP`, and none of any other opcode. -/
theorem badTrace_runRows (op : Opcode) :
    badTrace.runRows op = if op = .jump then 1 else 0 := by
  have h1 : stateAt badTrace 1 = Regs.final jumpProg := by
    have := run_stateAt badTrace_valid.2 (k := badTrace.steps) le_rfl
    rw [badTrace_valid.2] at this
    exact (Option.some.inj this).symm
  have hregs : badTrace.regs = [Regs.initial, Regs.final jumpProg] := by
    rw [regs_eq_map badTrace_valid.2]
    show [stateAt badTrace 0, stateAt badTrace 1] = _
    rw [h1]
    rfl
  unfold Trace.runRows
  rw [hregs]
  cases op <;> simp [jumpProg_fetch_one, Regs.initial, Instr.opcode]

/-- The witness's `XOR` table is empty and its `JUMP` table has the one row of the run. -/
theorem bad_trace_witness_rows :
    ∃ w, SatisfiedBy jumpProg badInput w ∧ AssignmentRepresents w badTrace ∧
      (tableAt w 0).table.length = 0 ∧ (tableAt w 4).table.length = 1 := by
  obtain ⟨w, hs, hr, hlen⟩ := constraintCompleteness_rows badTrace_valid
    fun op ↦ (badTrace_runRows op).trans_le (by split_ifs <;> decide)
  refine ⟨w, hs, hr, ?_, ?_⟩
  · have h := (hlen 0).trans (badTrace_runRows _)
    simp only [tableOpcode, tableOpcodes] at h
    exact h
  · have h := (hlen 4).trans (badTrace_runRows _)
    simp only [tableOpcode, tableOpcodes] at h
    exact h

end LeanVMTests.Arithmetization.Completeness.Theorem
