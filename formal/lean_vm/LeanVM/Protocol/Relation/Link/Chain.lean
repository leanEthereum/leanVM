/-
  LeanVM.Protocol.Relation.Link.Chain

  A chain of states whose every row takes one leanISA step runs, from the initial state, to the
  final one at its first visit.
-/

module

public import LeanVM.Protocol.Hotwire.StateLink
public import Statement.LeanIsa
import LeanVM.Semantics.Lemmas

/-!
# From a chain of rows to a run

`Hotwire/StateLink.lean`'s `ValidChain` says the rows are the cycles `0 … T − 1`, once each, the
first holds the initial state, each row's successor is the next cycle's state, and the last row's
successor is the final state. If each row's state and successor are registers (`regs`, `regs'`)
and the row takes one leanISA step from one to the other, the states by cycle (`chain_states`) run
(`run_of_states`): from the initial state, at the first cycle `n` in the final state, `run n` is the
final state, as `run` halts at the first visit (`run_first_final`).
-/

namespace LeanVM.Protocol.Relation

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol.Hotwire

@[expose] public section

/-- **States that step run**: if the states `S 0, …, S n` each step to the next and none before
`n` is the final state, `run n` from `S 0` is `S n`. -/
theorem run_of_states {κ : ℕ} (program : LeanIsaProgram) (mem : MemoryImage κ)
    (S : ℕ → Registers K) (n : ℕ) (hstep : ∀ t < n, step program mem (S t) = some (S (t + 1)))
    (hne : ∀ t < n, S t ≠ Registers.final program) :
    run program mem n (S 0) = some (S n) := by
  suffices h : ∀ m k, k + m = n → run program mem m (S k) = some (S n) by
    simpa using h n 0 (by simp)
  intro m
  induction m with
  | zero => intro k hk; simp only [Nat.add_zero] at hk; subst hk; rfl
  | succ m ih =>
    intro k hk
    rw [run_succ_of_ne_final (hne k (by omega)), hstep k (by omega), Option.bind_eq_bind,
      Option.bind_some]
    exact ih (k + 1) (by omega)

variable {R : Type} {T W : ℕ} {σ : R → Fin (2 ^ W)} {s s' : R → Fin 2 → E}
  {sInit sFin : Fin 2 → E}

open Classical in
/-- **The states by cycle**: the registers of the row at each cycle below `T`, the final ones at
`T`. Each cycle's row steps to the next cycle's state. -/
theorem chain_states (hc : ValidChain T σ s s' sInit sFin)
    (regs regs' : R → Registers K) (rInit rFin : Registers K)
    (hinit : ∀ u, s u = sInit → regs u = rInit)
    (hnext : ∀ u v, s' u = s v → regs' u = regs v) (hfin : ∀ u, s' u = sFin → regs' u = rFin)
    (hrInit : T = 0 → rInit = rFin) :
    ∃ S : ℕ → Registers K, S 0 = rInit ∧ S T = rFin ∧
      ∀ t < T, ∃ u, (σ u : ℕ) = t ∧ S t = regs u ∧ S (t + 1) = regs' u := by
  have hrow : ∀ t < T, ∃ u, (σ u : ℕ) = t := fun t ht ↦ (hc.existsUnique t ht).exists
  let S : ℕ → Registers K := fun t ↦ if h : t < T then regs (hrow t h).choose else rFin
  have hS : ∀ t (h : t < T), S t = regs (hrow t h).choose := fun t h ↦ by simp only [S, h, ↓reduceDIte]
  have hσ : ∀ t (h : t < T), (σ (hrow t h).choose : ℕ) = t := fun t h ↦ (hrow t h).choose_spec
  refine ⟨S, ?_, ?_, fun t ht ↦ ⟨(hrow t ht).choose, hσ t ht, hS t ht, ?_⟩⟩
  · by_cases hT : 0 < T
    · rw [hS 0 hT]
      exact hinit _ (hc.init _ (hσ 0 hT))
    · have h0 : ¬ 0 < T := hT
      simp only [S, h0, ↓reduceDIte]
      exact (hrInit (by omega)).symm
  · simp [S]
  · by_cases ht' : t + 1 < T
    · rw [hS _ ht']
      exact (hnext _ _ (hc.step _ _ (by rw [hσ _ ht', hσ _ ht]))).symm
    · simp only [S, ht', ↓reduceDIte]
      exact (hfin _ (hc.fin _ (by rw [hσ _ ht]; omega))).symm

/-- **The run halts at the first visit**: states that step, from the initial state to the final
one at `T`, run in `n` steps to the final state for `n` the first cycle in the final state. -/
theorem run_first_final {κ : ℕ} (program : LeanIsaProgram) (mem : MemoryImage κ)
    (S : ℕ → Registers K) (T n : ℕ)
    (hstep : ∀ t < T, step program mem (S t) = some (S (t + 1))) (hn : n ≤ T)
    (hnF : S n = Registers.final program) (hfirst : ∀ t < n, S t ≠ Registers.final program) :
    run program mem n (S 0) = some (Registers.final program) := by
  rw [run_of_states program mem S n (fun t ht ↦ hstep t (by omega)) hfirst, hnF]

end

end LeanVM.Protocol.Relation
