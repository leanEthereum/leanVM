/-
  LeanVM.Facts.Stack

  The stack's cap: the honest prover's check is the statement's committed size at most `2^30`.
-/

module

public import Statement.LeanVm

/-!
# The stack's cap is the committed size's

The honest prover refuses a stack over `2^MAX_STACKED_LOG` words as the Rust's `prove` does
(`witness?`, `Statement/Prover/Columns.lean`: `layout.stackLog ≤ Whir.maxLogStack`); the
completeness statements bound `Execution.committedSize` instead (`Statement/LeanVm.lean`). They are
one condition: `stack_snd_le_iff` at any column log-sizes, and
`committedSize_le_iff_stackLog_le` at an execution's.
-/

@[expose] public section

namespace LeanVM.Protocol.Verifier

open LeanVM.Parameters LeanVM.Semantics

/-- `log2_ceil(n) ≤ k` exactly when `n ≤ 2^k`. -/
theorem log2Ceil_le_iff (n k : ℕ) : log2Ceil n ≤ k ↔ n ≤ 2 ^ k := by
  unfold log2Ceil bitLength
  by_cases h : n - 1 = 0
  · simp only [h, ite_true, Nat.zero_le, true_iff]
    have : 1 ≤ 2 ^ k := Nat.one_le_two_pow
    omega
  · simp only [h, ite_false]
    have hl := Nat.log2_lt (n := n - 1) (k := k) h
    omega

/-- A list's entries read by index over its length are the list. -/
theorem range_map_getD {α β : Type} (l : List α) (d : α) (f : α → β) :
    (List.range l.length).map (fun i ↦ f (l.getD i d)) = l.map f := by
  apply List.ext_getElem (by simp)
  intro i h₁ h₂
  simp only [List.length_map, List.length_range] at h₁
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h₁]

/-- `stack_offsets`' total is every block's words, in any order. -/
theorem stackOffsets_snd (sizes : List ℕ) :
    (stackOffsets sizes).2 = log2Ceil (sizes.map fun k ↦ 2 ^ k).sum := by
  have hfold : ∀ (l : List ℕ) (acc : List ℕ × ℕ),
      (l.foldl (fun (acc : List ℕ × ℕ) i ↦ (acc.1.set i acc.2, acc.2 + 2 ^ sizes.getD i 0)) acc).2 =
        acc.2 + (l.map fun i ↦ 2 ^ sizes.getD i 0).sum := by
    intro l
    induction l with
    | nil => intro acc; simp
    | cons x l ih => intro acc; simp only [List.foldl_cons, ih, List.map_cons, List.sum_cons]; omega
  simp only [stackOffsets]
  rw [hfold, ((List.mergeSort_perm _ _).map _).sum_eq, range_map_getD sizes 0 (fun k ↦ 2 ^ k)]
  simp

/-- **The stack fits `2^30` words exactly when its blocks do**: the stack's log-size
(`stack(kappas)`) is at most `MAX_STACKED_LOG` exactly when the blocks add up to at most `2^30`. -/
theorem stack_snd_le_iff (kappas : List ℕ) :
    (stack kappas).2 ≤ Whir.maxLogStack ↔
      (stackBlocks.map fun b ↦ 2 ^ kappas.getD b.column 0).sum ≤ 2 ^ 30 := by
  simp only [stack, stackOffsets_snd, List.map_map]
  rw [Nat.max_le, log2Ceil_le_iff]
  simp [Whir.maxLogStack, Whir.minLogStack, Function.comp_def]

end LeanVM.Protocol.Verifier

namespace LeanVM.Semantics

open LeanVM.Parameters LeanVM.Protocol.Verifier

/-- **The committed size is the stack's cap**: `Execution.committedSize ≤ 2^30` exactly when the
stack at the execution's column log-sizes has log-size at most `MAX_STACKED_LOG`, the check the
honest prover makes (`witness?`) on the layout `buildLayout` gives at the execution's row counts. -/
theorem Execution.committedSize_le_iff_stackLog_le {program : LeanIsaProgram}
    (execution : Execution program) :
    execution.committedSize ≤ 2 ^ 30 ↔
      (stack (columnKappas tables execution.logMemorySize execution.tableLogHeights)).2 ≤
        Whir.maxLogStack :=
  (stack_snd_le_iff _).symm

end LeanVM.Semantics
