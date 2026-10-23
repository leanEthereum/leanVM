/-
  LeanVM.Arithmetization.Soundness.Walk

  The walk decomposition of a balanced state channel: edges that are steps, whose pushed and
  pulled states balance against a start and the final registers, contain a run from the start to
  the final registers, each of whose steps is an edge.
-/

module

public import LeanVM.Semantics.Lemmas

@[expose] public section

/-!
# The walk decomposition of the state channel

At leanVM pin `127510d14c98ade4e8a97646c44fa7f1ff5e752d`. Specification Proposition 6.1
(`doc/leanvm/body/06-bus-interactions.tex`, §6.1), stated over an abstract list of edges so that
`Soundness.StateWalk` applies it to the rows of the six tables. It uses only the semantics'
`run`, nothing about the witness.

**The statement** (`exists_run_of_perm`). Each edge `e` of a list `E` is a step of the machine,
`step prog L (src e) = some (dst e)`, taken away from the sentinel. If the start `s` together with
the edges' targets is a permutation of the final registers together with the edges' sources (the
state pair balances, the verifier pushing `s = (1, 1)` and pulling `(g^(N_prog - 1), 1)`), then
`run` reaches the final registers from `s`, and each of its steps is an edge.

**The proof** follows the walk from `s` and cuts it at its first arrival at the final registers:
if `s` is final the run is empty; otherwise `s` must be pulled by an edge `e`, whose removal leaves
the same balance with start `dst e` and one edge fewer. The edges never used are the closed walks
of specification §8.3, about which nothing is claimed.

## Wrong readings excluded

* The run stops at the first arrival at the final registers: a walk that passes through
  `(g^(N_prog - 1), 1)` and continues is not a `run`, which halts there;
  the hypothesis that no edge leaves the sentinel is what lets the walk be a `run`.
* Arrival at the sentinel counter with another frame pointer is not arrival.
-/

namespace LeanVM.Arithmetization

open LeanVM.Parameters LeanVM.Semantics

/-- **Specification Proposition 6.1, the walk decomposition.** Edges that are steps away from the
sentinel, balanced against a start `s` and the final registers, contain a run from `s` to the final
registers; each step of the run is an edge. -/
theorem exists_run_of_perm {α : Type*} {prog : Program} {κ : ℕ} {L : MemImage κ}
    (src dst : α → Regs K) (E : List α)
    (hE : ∀ e ∈ E, (src e).pc ≠ prog.finalPc ∧ step prog L (src e) = some (dst e))
    (s : Regs K) (hbal : (s :: E.map dst).Perm (Regs.final prog :: E.map src)) :
    ∃ n, run prog L n s = some (Regs.final prog) ∧
      ∀ k < n, ∃ e ∈ E, run prog L k s = some (src e) ∧ run prog L (k + 1) s = some (dst e) := by
  induction hlen : E.length using Nat.strong_induction_on generalizing E s with
  | _ len ih =>
    by_cases hs : s = Regs.final prog
    · exact ⟨0, by rw [hs]; rfl, fun k hk ↦ absurd hk (Nat.not_lt_zero k)⟩
    have hmem : s ∈ E.map src := by
      have := hbal.subset List.mem_cons_self
      rcases List.mem_cons.mp this with h | h
      · exact absurd h hs
      · exact h
    obtain ⟨e, he, hse⟩ := List.mem_map.mp hmem
    obtain ⟨l₁, l₂, rfl⟩ := List.append_of_mem he
    have hbal' : (dst e :: (l₁ ++ l₂).map dst).Perm (Regs.final prog :: (l₁ ++ l₂).map src) := by
      have h1 : (s :: (l₁ ++ e :: l₂).map dst).Perm (s :: dst e :: (l₁ ++ l₂).map dst) := by
        refine List.Perm.cons _ ?_
        rw [List.map_append, List.map_cons, List.map_append]
        exact List.perm_middle
      have h2 : (Regs.final prog :: (l₁ ++ e :: l₂).map src).Perm
          (s :: Regs.final prog :: (l₁ ++ l₂).map src) := by
        rw [List.map_append, List.map_cons, hse, List.map_append]
        exact (List.Perm.cons _ List.perm_middle).trans (List.Perm.swap _ _ _)
      exact (h1.symm.trans (hbal.trans h2)).cons_inv
    have hE' : ∀ e' ∈ l₁ ++ l₂, (src e').pc ≠ prog.finalPc ∧ step prog L (src e') = some (dst e') :=
      fun e' he' ↦ hE e' (by
        rcases List.mem_append.mp he' with h | h
        · exact List.mem_append_left _ h
        · exact List.mem_append_right _ (List.mem_cons_of_mem _ h))
    obtain ⟨n, hn, hsteps⟩ := ih (l₁ ++ l₂).length (by simp at hlen ⊢; omega) (l₁ ++ l₂) hE'
      (dst e) hbal' rfl
    obtain ⟨hpc, hstep⟩ := hE e he
    rw [hse] at hpc hstep
    have hrun : ∀ k, run prog L (k + 1) s = run prog L k (dst e) := fun k ↦ by
      rw [run_succ_of_ne hpc, hstep]; rfl
    refine ⟨n + 1, by rw [hrun]; exact hn, fun k hk ↦ ?_⟩
    rcases k with _ | k
    · exact ⟨e, he, by rw [hse]; rfl, by rw [hrun]; rfl⟩
    · obtain ⟨e', he', h1, h2⟩ := hsteps k (by omega)
      refine ⟨e', ?_, by rw [hrun]; exact h1, by rw [hrun]; exact h2⟩
      rcases List.mem_append.mp he' with h | h
      · exact List.mem_append_left _ h
      · exact List.mem_append_right _ (List.mem_cons_of_mem _ h)

end LeanVM.Arithmetization
