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

At leanVM pin `127510d14c98ade4e8a97646c44fa7f1ff5e752d` and Clean pin `42fe4b26`. The soundness
direction for the proof system's constraint statement (`SatisfiedBy`), `constraintSoundness`.
It assumes that statement, whose three hypotheses Clean cannot yet express and whose BLAKE2s
validity are conjuncts, and `SentinelSafe` (the last instruction is not a `JUMP`), the one
condition on the program.

**The trace.** The witness names its trace: the image the prover data names (`imageOf`), and as
step count the length of the run `Soundness.StateWalk` extracts from the balanced state channel
(`exists_walk`, specification Proposition 6.1). It is a valid execution: the memory window is
`Caps`', the two public words are `SatisfiedBy.word0_eq` and `word1_eq` (§8.2), and the run is
that one. The witness represents it: the image is the trace's by construction, and every step of
the run is a row of one of the six tables (the walk is made of rows), whose state pull and push are
the step's two states.

**Composition.** Per-table soundness is Clean's instantiated soundness theorem of each of the opcode
tables (`Component.weakSoundness`, in `Soundness.Rows`), applied directly to the witness's rows with
the tables' `Assumptions` from `assumptions_of_blake2sRowsValid h.blake2s_valid`, the constraints
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
theorem constraintSoundness {prog : Program} {input : PublicInput}
    {w : EnsembleWitness (leanIsaEnsemble prog)} (hsafe : SentinelSafe prog)
    (h : SatisfiedBy prog input w) :
    ∃ t, AssignmentRepresents w t ∧ ValidExecution prog input t := by
  obtain ⟨f, hf, n, hn, hsteps⟩ := exists_walk hsafe h
  let t : Trace prog := ⟨(imageOf w.data).1, (imageOf w.data).2, n⟩
  have hv : run prog t.image t.steps Regs.initial = some (Regs.final prog) := hn
  refine ⟨t, ⟨rfl, fun _ _ ↦ rfl, ?_⟩,
    ⟨h.caps.minLogMem_le, h.caps.le_maxLogMem, h.word0_eq, h.word1_eq⟩, hn⟩
  intro k hk
  have hlen : t.regs.length = n + 1 := Trace.regs_length hv
  have e : ∀ j (hj : j < t.regs.length), t.regs[j] = stateAt t j := fun j hj ↦ by
    rw [List.getElem_of_eq (regs_eq_map hv) hj]
    simp
  obtain ⟨p, hp, h1, h2⟩ := hsteps k (by omega)
  have s1 : stateAt t k = (f p).src := by simp only [stateAt, t, h1, Option.getD_some]
  have s2 : stateAt t (k + 1) = (f p).next := by simp only [stateAt, t, h2, Option.getD_some]
  rw [e k (by omega), e (k + 1) hk, s1, s2]
  obtain ⟨ht, hrow⟩ := mem_opPairs hp
  refine ⟨p.1, List.mem_of_mem_take ht, p.2, hrow, ?_, ?_⟩
  · rw [rowMessagesOn_eq_rowSends, (hf p hp).1, RowRec.sends, Channel.toRaw_name,
      sendsOf_statePull]
    rfl
  · rw [rowMessagesOn_eq_rowSends, (hf p hp).1, RowRec.sends, Channel.toRaw_name,
      sendsOf_statePush]

end LeanVM.Arithmetization
