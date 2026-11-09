/-
  LeanVM.Arithmetization.Soundness.Walk

  The walk decomposition of a balanced state channel: edges that are steps, whose pushed and
  pulled states balance against a start and the final registers, contain a run from the start to
  the final registers, each of whose steps is an edge.
-/

module

public import LeanVM.Semantics.Lemmas
public import Statement.LeanIsa
public import LeanVM.Facts.IsaWith
public import Statement.Fast.CubicExt
public import Statement.Fast.FieldWords

@[expose] public section

/-!
# The walk decomposition of the state channel

At leanVM main `40f877dc2c858f013c5974ab71ca594b31a7aec9`. Specification Proposition 6.1
(`doc/leanvm/body/06-bus-interactions.tex`, §6.1), stated over an abstract list of edges so that
`Soundness.StateWalk` applies it to the rows of the six tables. It uses only the semantics'
`run`, nothing about the witness.

**The statement** (`exists_run_of_perm`). Each edge `e` of a list `E` is a step of the machine,
`step prog L (src e) = some (dst e)`. If the start `s` together with
the edges' targets is a permutation of the final registers together with the edges' sources (the
state pair balances, the verifier pushing `s = (1, 1)` and pulling `(g^(N_prog - 1), 1)`), then
`run` reaches the final registers from `s`, and each of its steps is an edge.

**The proof** follows the walk from `s` and cuts it at its first visit of the final registers
(the Proposition's `push(r_i) ≠ final` for `i < L`): if `s` is final the run is empty; otherwise
`s` must be pulled by an edge `e`, whose removal leaves the same balance with start `dst e` and
one edge fewer, and `run` steps from `s`, which is not the final state, along `e`. The edges never
used are closed walks, about which nothing is claimed; what follows the first visit of the final
registers is one of them.

**Under any semantics of `KECCAK`** (`exists_runB_of_perm`): the same, for the steps and runs
of a semantics `S` (`Statement.LeanIsa`: `stepB S`, `runB S`); `exists_run_of_perm` is it at the
deployed one, the reduction-blind verifier's walk at `keccakFree`.

## Wrong readings excluded

* The run stops at the first visit of the final registers: a walk that passes through
  `(g^(N_prog - 1), 1)` and continues is not a `run`, which halts there; the cut makes it one.
* A visit of the last slot with another frame pointer is not a visit of the final registers: the
  run steps from there like from any other slot, and so may an edge.
-/

namespace LeanVM.Arithmetization

open LeanVM.Parameters LeanVM.Semantics

/-- Away from the final state, a run under the semantics `S` takes a step. -/
theorem runB_succ_of_ne (S : KeccakSem) {prog : LeanIsaProgram} {κ : ℕ} {L : MemoryImage κ} {r : Registers K}
    (h : r ≠ Registers.final prog) (n : ℕ) :
    runB S prog L (n + 1) r = stepB S prog L r >>= runB S prog L n := by
  rw [runB, ite_eq_right h]

/-- **Specification Proposition 6.1, the walk decomposition**, under any semantics `S` of
`KECCAK`: edges that are steps, balanced against a start `s` and the final registers, contain a
run from `s` to the final registers, the walk from `s` cut at its first visit of them; each step
of the run is an edge. -/
theorem exists_runB_of_perm (S : KeccakSem) {α : Type*} {prog : LeanIsaProgram} {κ : ℕ} {L :
    MemoryImage κ}
    (src dst : α → Registers K) (E : List α)
    (hE : ∀ e ∈ E, stepB S prog L (src e) = some (dst e))
    (s : Registers K) (hbal : (s :: E.map dst).Perm (Registers.final prog :: E.map src)) :
    ∃ n, runB S prog L n s = some (Registers.final prog) ∧
      ∀ k < n, ∃ e ∈ E, runB S prog L k s = some (src e) ∧
        runB S prog L (k + 1) s = some (dst e) := by
  induction hlen : E.length using Nat.strong_induction_on generalizing E s with
  | _ len ih =>
    by_cases hs : s = Registers.final prog
    · exact ⟨0, by rw [hs]; rfl, fun k hk ↦ absurd hk (Nat.not_lt_zero k)⟩
    have hmem : s ∈ E.map src := by
      have := hbal.subset List.mem_cons_self
      rcases List.mem_cons.mp this with h | h
      · exact absurd h hs
      · exact h
    obtain ⟨e, he, hse⟩ := List.mem_map.mp hmem
    obtain ⟨l₁, l₂, rfl⟩ := List.append_of_mem he
    have hbal' : (dst e :: (l₁ ++ l₂).map dst).Perm (Registers.final prog :: (l₁ ++ l₂).map src) := by
      have h1 : (s :: (l₁ ++ e :: l₂).map dst).Perm (s :: dst e :: (l₁ ++ l₂).map dst) := by
        refine List.Perm.cons _ ?_
        rw [List.map_append, List.map_cons, List.map_append]
        exact List.perm_middle
      have h2 : (Registers.final prog :: (l₁ ++ e :: l₂).map src).Perm
          (s :: Registers.final prog :: (l₁ ++ l₂).map src) := by
        rw [List.map_append, List.map_cons, hse, List.map_append]
        exact (List.Perm.cons _ List.perm_middle).trans (List.Perm.swap _ _ _)
      exact (h1.symm.trans (hbal.trans h2)).cons_inv
    have hE' : ∀ e' ∈ l₁ ++ l₂, stepB S prog L (src e') = some (dst e') :=
      fun e' he' ↦ hE e' (by
        rcases List.mem_append.mp he' with h | h
        · exact List.mem_append_left _ h
        · exact List.mem_append_right _ (List.mem_cons_of_mem _ h))
    obtain ⟨n, hn, hsteps⟩ := ih (l₁ ++ l₂).length (by simp at hlen ⊢; omega) (l₁ ++ l₂) hE'
      (dst e) hbal' rfl
    have hstep := hE e he
    rw [hse] at hstep
    have hrun : ∀ k, runB S prog L (k + 1) s = runB S prog L k (dst e) := fun k ↦ by
      rw [runB_succ_of_ne S hs, hstep]; rfl
    refine ⟨n + 1, by rw [hrun]; exact hn, fun k hk ↦ ?_⟩
    rcases k with _ | k
    · exact ⟨e, he, by rw [hse]; rfl, by rw [hrun]; rfl⟩
    · obtain ⟨e', he', h1, h2⟩ := hsteps k (by omega)
      refine ⟨e', ?_, by rw [hrun]; exact h1, by rw [hrun]; exact h2⟩
      rcases List.mem_append.mp he' with h | h
      · exact List.mem_append_left _ h
      · exact List.mem_append_right _ (List.mem_cons_of_mem _ h)

end LeanVM.Arithmetization
