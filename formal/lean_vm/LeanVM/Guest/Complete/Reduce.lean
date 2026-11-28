module

public import LeanVM.Prover.ExecuteWindows
public import Statement.LeanVmGuestCompleteness

/-!
# The guest's execution completeness, reduced to its run within bounds

`GuestExecutionComplete` asks of the executor's run of the guest on a node's advice a valid
execution, of committed size at most `2^30`, pointer width at most `24` and its `KECCAK` blocks in
windows. The executor gives validity (`execute_sound`) and the windows
(`execute_keccakBlocksInWindows`) of any execution it returns; the pointer width,
`max(bitLength cycles, logMemory, logBytecode, 1)` with the guest's `logBytecode = 19`, is at most
`24` once the memory has at most `2^24` words and the run fewer than `2^24` steps, its cycles being
its steps (`tableRows_sum`). So `GuestExecutionComplete` follows from `GuestRunsWithin`: on every
node it covers, the executor returns an execution of at most `2^24` words, fewer than `2^24` steps
and committed size at most `2^30`, or some child's openings collide
(`guestExecutionComplete_of_runsWithin`).
-/

namespace LeanVM.Guest.Complete

open LeanVM.Parameters LeanVM.Semantics LeanVM.Node LeanVM.Protocol
open LeanVM.Guest.Completeness

@[expose] public section

/-- A run's instructions, counted by opcode, are its steps. -/
theorem opcodeCounts_sum {κ : ℕ} {prog : LeanIsaProgram} {M : MemoryImage κ} :
    ∀ (n : ℕ) (r : Registers K), run prog M n r = some (Registers.final prog) →
      opcodeCountInRun prog M .xor n r + opcodeCountInRun prog M .mulNative n r +
        opcodeCountInRun prog M .setConstant n r + opcodeCountInRun prog M .deref n r +
        opcodeCountInRun prog M .jump n r + opcodeCountInRun prog M .keccak n r = n
  | 0, _, _ => rfl
  | n + 1, r, h => by
    rw [run_succ] at h
    split_ifs at h
    cases hs : step prog M r with
    | none => rw [hs] at h; simp at h
    | some r1 =>
      rw [hs] at h
      have ih := opcodeCounts_sum n r1 h
      cases hf : prog.fetch r.pc with
      | none => rw [step, hf] at hs; simp at hs
      | some ins =>
        simp only [opcodeCountInRun, hf, hs]
        cases ins <;> simp only [LeanIsaInstruction.opcode] <;> simp <;> omega

/-- **A valid execution's table rows are its steps.** -/
theorem tableRows_sum {prog : LeanIsaProgram} {input : PublicInput} {t : Execution prog}
    (hv : ValidExecution prog input t) : t.tableRows.sum = t.stepCount := by
  have h := opcodeCounts_sum t.stepCount Registers.initial hv.2
  simp only [Execution.tableRows, Execution.opcodeCount, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil]
  omega

theorem bitLength_le {n k : ℕ} (h : n < 2 ^ k) : Protocol.Verifier.bitLength n ≤ k := by
  unfold Protocol.Verifier.bitLength
  split_ifs with h0
  · exact Nat.zero_le _
  · have := (Nat.log2_lt h0).mpr h
    omega

/-- **The guest's pointer width is at most `24`** on an execution of at most `2^24` words and fewer
than `2^24` steps. -/
theorem pointerWidth_le {input : PublicInput} {t : Execution guestProgram}
    (hv : ValidExecution guestProgram input t) (hmem : t.logMemorySize ≤ 24)
    (hsteps : t.stepCount < 2 ^ 24) : t.pointerWidth ≤ Protocol.Verifier.maxPointerWidth := by
  have hb : Protocol.Verifier.bitLength t.tableRows.sum ≤ 24 :=
    bitLength_le (by rw [tableRows_sum hv]; exact hsteps)
  have hl : guestProgram.logSize = 19 := rfl
  simp only [Execution.pointerWidth, Protocol.Verifier.pointerWidth, Protocol.Verifier.maxPointerWidth,
    hl]
  omega

/-- **The guest's run within its bounds**: on every node `GuestExecutionComplete` covers, the
executor's run of the guest on the node's advice returns an execution of at most `2^24` words, fewer
than `2^24` steps and committed size at most `2^30`, or some child's openings collide. -/
def GuestRunsWithin : Prop :=
  ∀ (statement : NodeStatement) (witness : NodeWitness),
    NodeRelation (bytecodeWords guestProgram) (deployedSeed guestProgram) statement witness →
    DeployedLimits statement witness →
    (∃ execution, guestExecution guestProgram statement witness = .ok execution ∧
      execution.logMemorySize ≤ 24 ∧ execution.stepCount < 2 ^ 24 ∧
        execution.committedSize ≤ 2 ^ 30) ∨
    ∃ child ∈ witness.children, OpeningsCollide child.proof

/-- **`GuestExecutionComplete` from the guest's run within its bounds.** -/
theorem guestExecutionComplete_of_runsWithin (h : GuestRunsWithin) : GuestExecutionComplete := by
  intro s w hrel hlim
  refine (h s w hrel hlim).imp_left fun ⟨t, he, hmem, hsteps, hsz⟩ ↦ ?_
  have hv := Prover.Exec.execute_sound he
  exact ⟨t, he, hv, hsz, pointerWidth_le hv hmem hsteps,
    Prover.Exec.execute_keccakBlocksInWindows he⟩

end

end LeanVM.Guest.Complete
