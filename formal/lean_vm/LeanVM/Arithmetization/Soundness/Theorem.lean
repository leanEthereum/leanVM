/-
  LeanVM.Arithmetization.Soundness.Theorem

  Constraint soundness: a witness satisfying the constraint statement of well-formed bytecode
  represents a valid execution.
-/

module

public import LeanVM.Arithmetization.Soundness.StateWalk
public import LeanVM.Arithmetization.Completeness.Theorem

@[expose] public section

/-!
# Constraint soundness

At leanVM main `40f877dc2c858f013c5974ab71ca594b31a7aec9` and Clean pin `b41c196b`. The soundness
direction for the proof system's constraint statement (`SatisfiedBy`), `constraintSoundness`.
It assumes that statement, whose `KECCAK` validity is a conjunct (the blocks' rows are the
witness's fixed columns and derived data, theorems of `Statement`), and nothing of the program: the machine halts in the final state
`(g^(N_prog - 1), 1)`, so the walk the state channel contains, cut at its first visit of that
state, is a run.

**The trace.** The witness names its trace: the image the prover data names (`imageOf`), and as
step count the length of the run `Soundness.StateWalk` extracts from the balanced state channel
(`exists_walk`, specification Proposition 6.1). It is a valid execution: the memory window is
`Caps`', the two public words are `SatisfiedBy.word0_eq` and `word1_eq` (§8.2), and the run is
that one. The witness represents it: the image is the trace's by construction, and every step of
the run is a row of one of the six tables (the walk is made of rows), whose state pull and push are
the step's two states.

**Composition.** Per-table soundness is Clean's instantiated soundness theorem of each of the opcode
tables (`Component.weakSoundness`, in `Soundness.Rows`), applied directly to the witness's rows with
the tables' `Assumptions` from `assumptions_of_keccakRowsValid h.keccak_valid`, the constraints
from `h.constraints`, and the pull guarantees from the two lookup theorems
(`mem_channel_sound`, `bytecode_channel_sound`); never through Clean's `TableSoundness`, which
takes the field-sum `BalancedChannels` (unsound in characteristic two), nor through
`soundness_of_tableSoundness_and_specConsistency`, whose `AssumptionsConsistency` sources the
tables' `Assumptions` from the public input alone.

## Wrong readings excluded

* The trace is not the witness's rows: rows off the run (the closed walks of the fill, §8.3) are
  in no step of the trace, and a row may serve several steps (`AssignmentRepresents` is
  occurrence, not injection).
* The run is extracted, not assumed: no hypothesis names a run, a step count or a reachable state.
-/

namespace LeanVM.Arithmetization

open LeanVM.Parameters LeanVM.Semantics
open Air.Flat (Component EnsembleWitness)

/-- **Constraint soundness**. A witness satisfying the
constraint statement of well-formed bytecode on `input` represents a valid execution of the
program on `input`: the trace is the image the data names and the run the state channel's balance
contains, each of whose steps is a row of the witness. -/
theorem constraintSoundness {prog : LeanIsaProgram} {input : PublicInput} {κ : ℕ}
    {w : EnsembleWitness (leanIsaEnsemble prog κ)} (h : SatisfiedBy prog input w) :
    ∃ t, AssignmentRepresents w t ∧ ValidExecution prog input t := by
  obtain ⟨f, hf, n, hn, hsteps⟩ := exists_walk h
  let t : Execution prog := ⟨(imageOf w.data).1, (imageOf w.data).2, n⟩
  have hv : run prog t.memory t.stepCount Registers.initial = some (Registers.final prog) := hn
  refine ⟨t, ⟨rfl, fun _ _ ↦ rfl, ?_⟩,
    ⟨h.caps.minLogMem_le, h.caps.le_maxLogMem, h.word0_eq, h.word1_eq⟩, hn⟩
  intro k hk
  have hlen : t.regs.length = n + 1 := Execution.regs_length hv
  have e : ∀ j (hj : j < t.regs.length), t.regs[j] = stateAt t j := fun j hj ↦ by
    rw [List.getElem_of_eq (regs_eq_map hv) hj]
    simp
  obtain ⟨p, hp, h1, h2⟩ := hsteps k (by omega)
  have s1 : stateAt t k = (f p).src := by simp only [stateAt, t, h1, Option.getD_some]
  have s2 : stateAt t (k + 1) = (f p).next := by simp only [stateAt, t, h2, Option.getD_some]
  rw [e k (by omega), e (k + 1) hk, s1, s2]
  obtain ⟨ht, hrow⟩ := mem_opPairs hp
  refine ⟨p.1, List.mem_of_mem_take ht, p.2, hrow, ?_, ?_⟩
  · rw [rowMessagesOn_eq_rowSends, (hf p hp).1, Channel.toRaw_name]
    exact (RowRec.chanOf_sends_of_ne _ (by simp [StatePull, MemPull])
      (by simp [StatePull, MemPush])).trans (sendsOf_statePull _ _ _ _ _ _)
  · rw [rowMessagesOn_eq_rowSends, (hf p hp).1, Channel.toRaw_name]
    exact (RowRec.chanOf_sends_of_ne _ (by simp [StatePush, MemPull])
      (by simp [StatePush, MemPush])).trans (sendsOf_statePush _ _ _ _ _ _)

end LeanVM.Arithmetization
