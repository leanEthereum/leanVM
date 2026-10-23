import LeanVM.Arithmetization.Soundness.Theorem
import LeanVMTests.Arithmetization.Completeness.Fixture

/-!
# Tests: constraint soundness

`constraintSoundness` is inhabited at an instance and its trust base is the kernel's three axioms.
The instance is a round trip through completeness and soundness: the valid execution `badTrace` of
`Completeness.Fixture` (one `JUMP` to the sentinel) has, by `constraintCompleteness`, a witness
satisfying the statement; `constraintSoundness` extracts from that witness a trace that is a valid
execution on the witness's image, and its step count is the run's, `1` (runs are deterministic and
halt at the sentinel, `run_steps_unique`).

**`no_row_at_sentinel` is false over `w.interactions`** (`verifier_pulls_sentinel`), which
includes the verifier's own pull of the final registers
`(g^(N_prog - 1), 1)`, which is an interaction of every witness of every program; the round-trip
witness shows its hypotheses are satisfiable, so the statement is not vacuous either. The proved
statement quantifies over the rows of `w.tables`.

**The hypotheses of Lemma 6.3 are load-bearing.** A zero count is closed under multiplication by
`g` (`zero_closed`), and so are the `2^64 - 1` powers of `g` (`powers_closed`): neither the nonzero
count product nor the read bound can be dropped from the lookup argument. Soundness's one program
condition, `SentinelSafe`, is shown load-bearing at the semantic level by
`tests/LeanVMTests/Semantics/Execution.lean` (a `JUMP` at the sentinel chains two steps from the
initial to the final registers, yet no run is a `ValidExecution`).
-/

namespace LeanVMTests.Arithmetization.Soundness.Theorem

open LeanVM.Parameters LeanVM.Semantics LeanVM.Arithmetization
open Air.Flat (EnsembleWitness)
open LeanVMTests.Arithmetization.Completeness.Fixture

/-! ## The trust base -/

/--
info: 'LeanVM.Arithmetization.constraintSoundness' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms constraintSoundness

/--
info: 'LeanVM.Arithmetization.mem_channel_sound' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms mem_channel_sound

/--
info: 'LeanVM.Arithmetization.bytecode_channel_sound' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms bytecode_channel_sound

/--
info: 'LeanVM.Arithmetization.no_row_at_sentinel' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms no_row_at_sentinel

/--
info: 'LeanVM.Arithmetization.exists_run_of_balanced' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms exists_run_of_balanced

/-! ## A round trip -/

/-- Runs from one state that reach the final registers take the same number of steps: the machine
halts there. -/
theorem run_steps_unique {κ : ℕ} {prog : Program} {L : MemImage κ} {r : Regs K} {m n : ℕ}
    (hm : run prog L m r = some (Regs.final prog)) (hn : run prog L n r = some (Regs.final prog)) :
    m = n := by
  have key : ∀ a b, run prog L a r = some (Regs.final prog) →
      run prog L b r = some (Regs.final prog) → a < b → False := by
    intro a b ha hb hab
    obtain ⟨c, rfl⟩ : ∃ c, b = a + (c + 1) := ⟨b - a - 1, by omega⟩
    rw [run_add, ha] at hb
    change run prog L (c + 1) (Regs.final prog) = _ at hb
    rw [run_succ_of_eq rfl] at hb
    simp at hb
  rcases Nat.lt_trichotomy m n with h | h | h
  · exact (key m n hm hn h).elim
  · exact h
  · exact (key n m hn hm h).elim

/-- **Constraint soundness at an instance, after completeness.** The witness completeness builds
for `badTrace` satisfies the statement, and soundness extracts from it a valid execution that the
witness represents, of one step, the run's. -/
theorem bad_roundtrip :
    ∃ w, SatisfiedBy jumpProg badInput w ∧
      ∃ t, AssignmentRepresents w t ∧ ValidExecution jumpProg badInput t ∧ t.steps = 1 := by
  obtain ⟨w, hs, hr'⟩ := constraintCompleteness badTrace_valid (by decide)
  obtain ⟨t, hr, hv⟩ := constraintSoundness jumpProg_sentinelSafe hs
  refine ⟨w, hs, t, hr, hv, ?_⟩
  have himg := (assignmentRepresents_image hr).symm.trans (assignmentRepresents_image hr')
  show t.steps = badTrace.steps
  obtain ⟨κ, img, n⟩ := t
  obtain ⟨rfl, himg⟩ := Sigma.mk.inj himg
  obtain rfl := eq_of_heq himg
  exact run_steps_unique hv.2 badTrace_valid.2

/-! ## `no_row_at_sentinel` over the interactions -/

/-- **`no_row_at_sentinel` over the interactions is false for every witness**: the verifier
pulls the final registers `(g^(N_prog - 1), 1)` on the state pull channel, and its interaction
is among `w.interactions`. -/
theorem verifier_pulls_sentinel (prog : Program) (w : EnsembleWitness (leanIsaEnsemble prog)) :
    ¬ ∀ i ∈ w.interactions, i.channel.name = StatePull.name →
      ∀ pc fp : K, i.msg = #[pc, fp] → pc ≠ prog.finalPc := by
  intro hall
  have hmem : #[prog.finalPc, 1] ∈ messagesOn w StatePull.toRaw := by
    rw [messagesOn_eq_chanOf]
    unfold allSends EnsembleWitness.allTables
    rw [List.flatMap_cons, EnsembleWitness.verifierTable_table, List.flatMap_singleton,
      chanOf_append]
    refine List.mem_append_left _ ?_
    rw [show w.verifierTable.component = ⟨leanIsaVerifier prog⟩ from rfl, verifier_sends,
      Channel.toRaw_name]
    simp [chanOf, StatePull, StatePush]
  obtain ⟨i, hi, hmsg⟩ := List.mem_map.mp hmem
  obtain ⟨hi, hn⟩ := List.mem_filter.mp hi
  exact hall i hi (of_decide_eq_true hn) _ _ hmsg rfl

/-- That statement fails on the round-trip witness, which satisfies the statement. -/
example : ∃ w, SatisfiedBy jumpProg badInput w ∧
    ¬ ∀ i ∈ w.interactions, i.channel.name = StatePull.name →
      ∀ pc fp : K, i.msg = #[pc, fp] → pc ≠ jumpProg.finalPc := by
  obtain ⟨w, hs, -⟩ := bad_roundtrip
  exact ⟨w, hs, verifier_pulls_sentinel _ w⟩

/-! ## Lemma 6.3 needs its hypotheses -/

/-- A zero count is closed under multiplication by `g`: the nonzero count product is
load-bearing. -/
theorem zero_closed : (([0] : List K).map (g * ·)).Perm [0] := by
  simp

/-- Without the nonzero hypothesis, Lemma 6.3 fails. -/
example : ¬ ∀ P : List K, (P.map (g * ·)).Perm P → P.length < 2 ^ 64 - 1 → P = [] :=
  fun h ↦ List.cons_ne_nil _ _ (h [0] zero_closed (by decide))

/-- The `2^64 - 1` powers of `g` are closed under multiplication by `g`: the read bound is
load-bearing. -/
theorem powers_closed :
    (((List.range (2 ^ 64 - 1)).map gpow).map (g * ·)).Perm
      ((List.range (2 ^ 64 - 1)).map gpow) := by
  have e1 : ((List.range (2 ^ 64 - 1)).map gpow).map (g * ·) =
      (List.range (2 ^ 64 - 1)).map fun i ↦ gpow (i + 1) := by
    rw [List.map_map]
    exact List.map_congr_left fun i _ ↦ (gpow_succ i).symm
  have hN : gpow (2 ^ 64 - 2 + 1) = gpow 0 := by
    rw [show 2 ^ 64 - 2 + 1 = 2 ^ 64 - 1 by decide]
    exact g_pow_card_sub_one
  rw [e1, show 2 ^ 64 - 1 = (2 ^ 64 - 2) + 1 by decide]
  conv_lhs => rw [List.range_succ, List.map_append, List.map_singleton, hN]
  conv_rhs => rw [List.range_succ_eq_map, List.map_cons, List.map_map]
  exact List.perm_append_singleton _ _

/-- Without the read bound, Lemma 6.3 fails. -/
example : ¬ ∀ P : List K, (∀ c ∈ P, c ≠ 0) → (P.map (g * ·)).Perm P → P = [] := fun h ↦ by
  have := h _ (fun c hc ↦ by
    obtain ⟨i, -, rfl⟩ := List.mem_map.mp hc
    exact gpow_ne_zero i) powers_closed
  simp at this

end LeanVMTests.Arithmetization.Soundness.Theorem
