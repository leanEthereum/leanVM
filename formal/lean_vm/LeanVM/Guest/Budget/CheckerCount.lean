/-
  LeanVM.Guest.Budget.CheckerCount

  The checker's counts together: at coefficients above the words' (`Coefs.checker`, or
  `Coefs.checkerZero` with the zero-challenge sum absent), which are above the instructions'
  (`checker_aboveRows`, `checkerZero_aboveRows`), a node within a budget of `2^24` has its memory
  within `2^24` words, fewer than `2^24` steps and a committed size of at most `2^30`
  (`checker_bounds`, `checkerZero_bounds`).
-/

module

public import LeanVM.Guest.Budget.CycleCount
public import LeanVM.Guest.Budget.HandCount

namespace LeanVM.Guest.Budget

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest

@[expose] public section

theorem Coefs.Above.trans {A B C : Coefs} (h1 : A.Above B) (h2 : B.Above C) : A.Above C :=
  ⟨h1.claim.trans h2.claim, h1.child.trans h2.child, h1.xmss.trans h2.xmss, h1.sphincs.trans h2.sphincs,
    h1.matrix.trans h2.matrix, h1.row.trans h2.row, h1.fixed.trans h2.fixed⟩

/-- **The words' coefficients are above the instructions'**, the zero-challenge sum counted. -/
theorem checker_aboveRows : Coefs.Above (Coefs.rowsC iterSumV) Coefs.checker := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

/-- **The words' coefficients are above the instructions'**, the zero-challenge sum absent. -/
theorem checkerZero_aboveRows : Coefs.Above (Coefs.rowsC iterZeroV) Coefs.checkerZero := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

variable {C : Coefs} {it : NodeItems} {fs : String → ℕ} {lp al : String → Bool} {T : Memory.Tree}
  {input : PublicInput} {t : Execution guestProgram}

/-- **Memory, steps and committed size from the budget at the checker's coefficients**, the
zero-challenge sum counted: `main`'s tree within the words' count, the run's memory at most its aligned
words', its instructions of each opcode within the instructions' count. -/
theorem checker_bounds (hC : Coefs.Above Coefs.checker C) (hd : it.DeclaredFit) (hrows : ∀ n ∈ it.rows, n ≤ 32)
    (hB : C.budget it ≤ 2 ^ 24) (hfs : ∀ g, fs g ≤ fsW g) (hal : ∀ g, al g = true → alW g = true)
    (htl : ∀ f, fs (tailKey f) ≤ fs f) (hb : T.BufsOk coreProgram)
    (hc : T.cost coreProgram true (fsPad fsW alW) ≤ nodeWordsC iterSum it)
    (hv : ValidExecution guestProgram input t) (hlog : t.logMemorySize ≤ logMem (T.wordsA fs lp al))
    (hcnt : ∀ op, t.opcodeCount op ≤ cntJ iterSumV op it) :
    t.logMemorySize ≤ 24 ∧ t.stepCount < 2 ^ 24 ∧ t.committedSize ≤ 2 ^ 30 := by
  have hm := logMem_le_of_count (K := iterSum) (lp := lp) hC hd hrows hB hfs hal htl hb hc
  exact ⟨hlog.trans hm, cycles_committed_of_count (checker_aboveRows.trans hC) iterSum_weighted hd hrows hB hv
    (hlog.trans hm) hcnt⟩

/-- **Memory, steps and committed size from the budget at the checker's coefficients**, the
zero-challenge sum absent. -/
theorem checkerZero_bounds (hC : Coefs.Above Coefs.checkerZero C) (hd : it.DeclaredFit)
    (hrows : ∀ n ∈ it.rows, n ≤ 32) (hB : C.budget it ≤ 2 ^ 24) (hfs : ∀ g, fs g ≤ fsW g)
    (hal : ∀ g, al g = true → alW g = true) (htl : ∀ f, fs (tailKey f) ≤ fs f) (hb : T.BufsOk coreProgram)
    (hc : T.cost coreProgram true (fsPad fsW alW) ≤ nodeWordsC iterZero it)
    (hv : ValidExecution guestProgram input t) (hlog : t.logMemorySize ≤ logMem (T.wordsA fs lp al))
    (hcnt : ∀ op, t.opcodeCount op ≤ cntJ iterZeroV op it) :
    t.logMemorySize ≤ 24 ∧ t.stepCount < 2 ^ 24 ∧ t.committedSize ≤ 2 ^ 30 := by
  have hm := logMem_le_of_count (K := iterZero) (lp := lp) hC hd hrows hB hfs hal htl hb hc
  exact ⟨hlog.trans hm, cycles_committed_of_count (checkerZero_aboveRows.trans hC) iterZero_weighted hd hrows hB
    hv (hlog.trans hm) hcnt⟩

end

end LeanVM.Guest.Budget
