/-
  LeanVM.Semantics.RunTrace

  Relational views and finite ordered traces of the reference semantics.
-/

module

public import LeanVM.Semantics.Lemmas

/-!
# Relational steps and finite traces

These relations expose the existing fixed-image semantics at leanVM
`127510d14c98ade4e8a97646c44fa7f1ff5e752d` without introducing a second instruction model.
Failed reads or checks have no successor. `RunTrace` includes the pre-fetch halting rule;
its equivalence to exact `run` provides the finite-trace interface for state extraction
and application proofs. No constraint-system or cryptographic soundness result is assumed.
-/

namespace LeanVM.Semantics

open LeanVM.Parameters

@[expose] public section

/-- A relational view of instruction fetch followed by execution. This does not itself
exclude the sentinel; the whole-run relation does. -/
def ProgramStep {κ : ℕ} (prog : Program) (image : MemImage κ)
    (before after : Regs K) : Prop := step prog image before = some after

/-- An ordered trace with `n` transitions and `n+1` states. Every transition starts away
from the sentinel and is a reference program step; the last state need not be terminal. -/
def RunTrace {κ : ℕ} (prog : Program) (image : MemImage κ) (n : ℕ)
    (states : Fin (n + 1) → Regs K) : Prop :=
  ∀ i : Fin n, (states i.castSucc).pc ≠ prog.finalPc ∧
    ProgramStep prog image (states i.castSucc) (states i.succ)

/-- Fixed program and memory determine at most one successor. -/
theorem ProgramStep.functional {κ : ℕ} {prog : Program} {image : MemImage κ}
    {r next₁ next₂ : Regs K} (h₁ : ProgramStep prog image r next₁)
    (h₂ : ProgramStep prog image r next₂) : next₁ = next₂ :=
  Option.some.inj (h₁.symm.trans h₂)

/-- A failed step admits no successor, rather than an unconstrained one. -/
theorem ProgramStep.not_of_failure {κ : ℕ} {prog : Program} {image : MemImage κ}
    {r next : Regs K} (h : step prog image r = none) : ¬ ProgramStep prog image r next := by
  intro hs
  rw [ProgramStep, h] at hs
  cases hs

/-- An ordered relational trace composes into the exact reference run. -/
theorem RunTrace.run {κ : ℕ} {prog : Program} {image : MemImage κ} {n : ℕ}
    {states : Fin (n + 1) → Regs K} (h : RunTrace prog image n states) :
    run prog image n (states 0) = some (states (Fin.last n)) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have h₀ := h 0
    simp only [Fin.castSucc_zero] at h₀
    have ht : RunTrace prog image n (fun i ↦ states i.succ) := fun i ↦ h i.succ
    rw [run_succ_of_ne h₀.1]
    change step prog image (states 0) >>= LeanVM.Semantics.run prog image n = _
    rw [h₀.2]
    exact ih ht

/-- Every successful exact run has a finite ordered trace with the stated endpoints.
The zero-step case has one state and no transitions. -/
theorem run_eq_some_iff_trace {κ : ℕ} (prog : Program) (image : MemImage κ)
    (n : ℕ) (initial final : Regs K) :
    run prog image n initial = some final ↔
      ∃ states : Fin (n + 1) → Regs K,
        states 0 = initial ∧ states (Fin.last n) = final ∧ RunTrace prog image n states := by
  constructor
  · intro h
    have hp : ∀ i : Fin (n + 1), ∃ r, run prog image i initial = some r := by
      intro i
      have hi : (i : ℕ) ≤ n := by have := i.isLt; omega
      obtain ⟨r, hr, _⟩ := run_prefix (m := i) (n := n - i)
        (by simpa only [Nat.add_sub_of_le hi] using h)
      exact ⟨r, hr⟩
    choose states hs using hp
    refine ⟨states, ?_, ?_, ?_⟩
    · exact (Option.some.inj (hs 0)).symm
    · exact Option.some.inj ((hs (Fin.last n)).symm.trans h)
    · intro i
      have hnext := hs i.succ
      change run prog image ((i : ℕ) + 1) initial = some (states i.succ) at hnext
      have hprev := hs i.castSucc
      simp only [Fin.val_castSucc] at hprev
      rw [run_add, hprev] at hnext
      change run prog image 1 (states i.castSucc) = some (states i.succ) at hnext
      have hpc := pc_ne_finalPc_of_run_succ hnext
      refine ⟨hpc, ?_⟩
      rw [run_succ_of_ne hpc] at hnext
      change (step prog image (states i.castSucc)).bind some = some (states i.succ) at hnext
      change step prog image (states i.castSucc) = some (states i.succ)
      generalize step prog image (states i.castSucc) = result at hnext ⊢
      cases result with
      | none => cases hnext
      | some next => exact hnext
  · rintro ⟨states, hfirst, hlast, ht⟩
    simpa only [hfirst, hlast] using ht.run

/-- Reference validity is a public boundary together with an ordered terminating trace. -/
theorem validExecution_iff_trace (prog : Program) (input : PublicInput) (t : Trace prog) :
    ValidExecution prog input t ↔ HasPublicBoundary input t ∧
      ∃ states : Fin (t.steps + 1) → Regs K,
        states 0 = Regs.initial ∧ states (Fin.last t.steps) = Regs.final prog ∧
          RunTrace prog t.image t.steps states := by
  rw [ValidExecution, run_eq_some_iff_trace]

end
end LeanVM.Semantics
