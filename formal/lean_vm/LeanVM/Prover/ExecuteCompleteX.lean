module

public import LeanVM.Prover.ExecuteComplete
public import Statement.LeanVm

/-!
# The executor's execution commits no more than the reference

`execute_completeX`: under `execute_complete`'s hypotheses, and an invariant that keeps the cells
the executor touches below `2^κ`, the executor's execution is valid, runs the reference's
instructions, has a memory of at most `2^κ` words, and so commits no more cells than the reference
(`committedSize_mono`).
-/

namespace LeanVM.Prover.Exec

open LeanVM.Parameters LeanVM.Semantics

@[expose] public section

/-- The committed size grows with the memory, the counts equal. -/
theorem committedSize_mono {prog : LeanIsaProgram} {e e' : Execution prog}
    (hκ : e.logMemorySize ≤ e'.logMemorySize) (hc : ∀ op, e.opcodeCount op = e'.opcodeCount op) :
    e.committedSize ≤ e'.committedSize := by
  unfold Execution.committedSize
  simp only [hc]
  have := Nat.pow_le_pow_right (by norm_num : 0 < 2) hκ
  omega

/-- **The executor is complete, within the reference's committed size**: under
`execute_complete`'s hypotheses, and an invariant keeping `used` within `2^κ`, the executor returns
a valid execution of the reference's steps and instruction counts, its memory the reference's
wherever it is not zero, of at most `2^κ` words, committing no more cells than the reference. -/
theorem execute_completeX {prog : LeanIsaProgram} {input : PublicInput} {adv : Advice} {κ n : ℕ}
    {img : MemoryImage κ} {Inv : St → Prop} (hκ : κ ≤ 28) (hn : n ≤ maxSteps)
    (hval : ValidExecution prog input ⟨κ, img, n⟩) (hdec : ∀ i, Decodable (prog.instructions i))
    (hmain : adv.mainFrame < maxCells)
    (hinit : ∀ C m, Ctx.of prog adv = .ok C → initMem adv input = .ok m → Inv (initSt C adv m))
    (hrule : ∀ C, Ctx.of prog adv = .ok C → InvRule prog img n C (refMem img) Inv)
    (hused : ∀ s, Inv s → s.mem.used ≤ 2 ^ κ) :
    ∃ t, execute prog input adv = .ok t ∧ ValidExecution prog input t ∧ t.stepCount = n ∧
      (∀ i, t.memory i = 0 ∨ t.memory i = refMem img i.val) ∧
      (∀ op, t.opcodeCount op = (⟨κ, img, n⟩ : Execution prog).opcodeCount op) ∧
      t.logMemorySize ≤ κ ∧ t.committedSize ≤ (⟨κ, img, n⟩ : Execution prog).committedSize := by
  obtain ⟨t, he, hn', hm, hc, s, hs, hlog⟩ := execute_complete_inv hκ hn hval hdec hmain hinit hrule
  have hle : t.logMemorySize ≤ κ := hlog ▸ log2_nextPowerOfTwo_le (hused s hs)
  exact ⟨t, he, execute_sound he, hn', hm, hc, hle, committedSize_mono hle hc⟩

end

end LeanVM.Prover.Exec
