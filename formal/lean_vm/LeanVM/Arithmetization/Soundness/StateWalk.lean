/-
  LeanVM.Arithmetization.Soundness.StateWalk

  The state channel of a satisfying witness: every row of the six tables is a step of the program
  over the committed image, and the balanced state pair contains a run from the initial to the
  final registers.
-/

module

public import LeanVM.Arithmetization.Soundness.MemChannel
public import LeanVM.Arithmetization.Soundness.Walk

@[expose] public section

/-!
# The state channel

At leanVM main `40f877dc2c858f013c5974ab71ca594b31a7aec9` and Clean pin `b41c196b`. Specification
Proposition 6.1 (`doc/leanvm/body/06-bus-interactions.tex`, §6.1), as `exists_run_of_balanced`. It
assumes the constraint statement `SatisfiedBy` alone, nothing of the program, and serves
`constraintSoundness`.

**The rows are steps** (`opRecs_step`). For a row of the six tables, the table's `Assumptions`
are `SatisfiedBy.keccak_valid` (`assumptions_of_keccakRowsValid`), its constraints are
`SatisfiedBy.constraints`, and the guarantees of its pulls are the two lookup theorems
(`mem_channel_sound`, `bytecode_guarantee`; every interaction is on one of the six channels,
`ChannelOk`). The table's soundness (`Soundness.Rows`) makes the row execute an instruction encoded
by its bytecode read, which `opRecs_bc_sound` makes the program's at the row's counter: the row is
`step prog L` from its pulled state to its pushed state, `L` the image the data names.

**The run** (`exists_run_of_balanced`, Proposition 6.1). The state pair pushes `(1, 1)` (the
verifier) and the rows' successors, and pulls `(g^(N_prog - 1), 1)` (the verifier) and the rows'
states; its balance is the hypothesis of `exists_run_of_perm` (`Soundness.Walk`) over the rows,
which yields a run from `Registers.initial` to `Registers.final prog`, the walk from the initial state cut at
its first visit of the final state, each of whose steps is a row (`exists_walk`, which
`Soundness.Theorem` uses for `AssignmentRepresents`). Every state before the cut is not the final
state, so `run`, which halts in the final state only, steps from it; a row at the last slot in
another frame is a step like any other.

**Under any semantics** (`RowsStep`, `exists_walkB`): the same, for
rows that are steps of a semantics `S` of `KECCAK`: the deployed one under the `KECCAK` validity
(`rowsStep_deployed`), the reduction-blind one `keccakFree` without it (`rowsStep_free`).

## Wrong readings excluded

* The state pull carries no guarantee: nothing is claimed of a pulled state
  except through the walk; the rows not on the run are closed walks.
* No row is excluded at the last slot: the machine halts in the final state, `(g^(N_prog - 1), 1)`,
  and a row at the last slot in another frame is a step of the program, which a valid execution
  may take (leanVM's `halts_in_the_final_state`, `crates/leanvm_core/src/cpu/mod.rs:826-864`).
-/

namespace LeanVM.Arithmetization

open LeanVM.Parameters LeanVM.Semantics
open Air.Flat (Component EnsembleWitness)

variable {prog : LeanIsaProgram} {κ : ℕ} {input : PublicInput} {w : EnsembleWitness (leanIsaEnsemble prog κ)}

/-! ## The rows are steps -/

/-- The interactions of a row of a witness's table are interactions of the witness. -/
theorem eval_mem_interactions {t : Air.Flat.Table K} (ht : t ∈ w.tables) {row : Array K}
    (hrow : row ∈ t.table) {a : AbstractInteraction K}
    (ha : a ∈ t.component.operations.interactions) :
    a.eval (t.environment row) ∈ w.interactions := by
  unfold EnsembleWitness.interactions
  refine List.mem_append_right _ (List.mem_flatMap.mpr ⟨t, ht, ?_⟩)
  unfold Air.Flat.Table.interactions
  exact List.mem_flatMap.mpr ⟨row, hrow, List.mem_map_of_mem ha⟩

/-- The pulls of a row of the six tables have their guarantees: the memory reads are the image's
words (`mem_channel_sound`) and the bytecode entry decodes (`bytecode_guarantee`). -/
theorem opRecs_guarantees (h : SatisfiedByB prog input w) {f : Air.Flat.Table K × Array K → RowRec}
    (hf : OpRecs w f) {p : Air.Flat.Table K × Array K} (hp : p ∈ opPairs w) :
    p.1.component.operations.FullGuarantees (p.1.environment p.2) := by
  obtain ⟨ht, hrow⟩ := mem_opPairs hp
  have ht' := List.mem_of_mem_take ht
  have hdata := environment_data ht' p.2
  intro a ha
  have hmem := eval_mem_interactions ht' hrow ha
  rcases (hf p hp).2.2.2.2.1 a ha with hc | hc | hc
  · obtain ⟨ch, mult, msg, ag⟩ := a
    dsimp only at hc
    subst hc
    intro _ hmult
    rw [hdata]
    exact mem_channel_sound h _ hmem rfl hmult _
      (by rw [ProvableType.toElements_fromElements]; rfl)
  · obtain ⟨ch, mult, msg, ag⟩ := a
    dsimp only at hc
    subst hc
    intro _ _
    rw [hdata]
    exact bytecode_guarantee h _ hmem rfl _
      (by rw [ProvableType.toElements_fromElements]; rfl)
  · exact fun _ ↦ hc _ _ _

/-- **Every row of the six tables is a step of the program** over the image the data names, from
its pulled state to its pushed state; its counter is a slot `g^k` of the program, and unless the
program holds a `JUMP` there the successor is the fall-through. -/
theorem opRecs_step (h : SatisfiedBy prog input w) {f : Air.Flat.Table K × Array K → RowRec}
    (hf : OpRecs w f) {p : Air.Flat.Table K × Array K} (hp : p ∈ opPairs w) :
    step prog (imageOf w.data).2 (f p).src = some (f p).next ∧
      ∃ k : Fin (2 ^ prog.logSize), (f p).pc = addressOfIndex k ∧
        ((prog.instructions k).opcode ≠ .jump → (f p).next = ⟨g * (f p).pc, (f p).fp⟩) := by
  obtain ⟨ht, hrow⟩ := mem_opPairs hp
  have ht' := List.mem_of_mem_take ht
  have ha := p.1.circuitAssumptions_of_assumptions
    (assumptions_of_keccakRowsValid h.keccak_valid p.1 ht') p.2 hrow
  have hc := h.constraints p.1 ht' p.2 hrow
  obtain ⟨ins, he, hexec, hnj⟩ := (hf p hp).2.2.2.2.2.1 ha hc (opRecs_guarantees h.toB hf hp)
  obtain ⟨k, hpc, hek⟩ := opRecs_bc_sound h.toB hf hp
  have hins : prog.instructions k = ins := entry_injective (hek.symm.trans he)
  refine ⟨?_, k, hpc, fun hj ↦ hnj (hins ▸ hj)⟩
  have hfetch : prog.fetch (f p).src.pc = some ins := by
    rw [show (f p).src.pc = (f p).pc from rfl, hpc, LeanIsaProgram.fetch_gpow, hins]
  rw [step_of_fetch_eq_some hfetch]
  exact hexec

/-- **Every row of the six tables is a step under the semantics `S`**, from its pulled state to
its pushed state; its counter is a slot of the program, and the successor is the fall-through
unless the program holds a `JUMP` there. -/
def RowsStep (S : KeccakSem) (w : EnsembleWitness (leanIsaEnsemble prog κ))
    (f : Air.Flat.Table K × Array K → RowRec) : Prop :=
  ∀ p ∈ opPairs w, stepB S prog (imageOf w.data).2 (f p).src = some (f p).next ∧
    ∃ k : Fin (2 ^ prog.logSize), (f p).pc = addressOfIndex k ∧
      ((prog.instructions k).opcode ≠ .jump → (f p).next = ⟨g * (f p).pc, (f p).fp⟩)

/-- The rows are steps of the deployed semantics. -/
theorem rowsStep_deployed (h : SatisfiedBy prog input w)
    {f : Air.Flat.Table K × Array K → RowRec} (hf : OpRecs w f) : RowsStep keccakDeployed w f :=
  fun _ hp ↦ by
    rw [stepB_deployed]
    exact opRecs_step h hf hp

/-! ## The state pair -/

/-- A state message as an array. -/
def regsArr (r : Registers K) : Array K := #[r.pc, r.fp]

/-- The state of a state message, `0` for a missing coordinate. -/
def arrRegs (a : Array K) : Registers K := ⟨a.getD 0 0, a.getD 1 0⟩

/-- Reading a state message back gives the state. -/
theorem arrRegs_regsArr (r : Registers K) : arrRegs (regsArr r) = r := rfl

/-- **The states a satisfying witness pushes**: the verifier's `(1, 1)` and the rows'
successors. -/
theorem statePush_eq (h : SatisfiedByB prog input w) {f : Air.Flat.Table K × Array K → RowRec}
    (hf : OpRecs w f) :
    messagesOn w StatePush.toRaw =
      regsArr Registers.initial :: (opPairs w).map fun p ↦ regsArr (f p).next := by
  obtain ⟨mfin, bfin, hall⟩ := allSends_eq h hf
  rw [messagesOn_eq_chanOf, chanOf_allSends _ hall]
  simp only [Channel.toRaw_name]
  rw [chanOf_verifier_statePush,
    chanOf_memSeed_eq_nil _ _ (by simp [StatePush, MemPull]) (by simp [StatePush, MemPush]),
    chanOf_bcSeed_eq_nil _ (by simp [StatePush, BytecodePull]) (by simp [StatePush, BytecodePush])]
  have hrow : ∀ p, chanOf StatePush.name (f p).sends = [regsArr (f p).next] := fun p ↦ by
    rw [RowRec.chanOf_sends_of_ne _ (by simp [StatePush, MemPull]) (by simp [StatePush, MemPush])]
    exact sendsOf_statePush _ _ _ _ _ _
  simp only [hrow, List.append_nil, flatMap_singleton_eq_map']
  rfl

/-- **The states a satisfying witness pulls**: the verifier's final registers and the rows'
states. -/
theorem statePull_eq (h : SatisfiedByB prog input w) {f : Air.Flat.Table K × Array K → RowRec}
    (hf : OpRecs w f) :
    messagesOn w StatePull.toRaw =
      regsArr (Registers.final prog) :: (opPairs w).map fun p ↦ regsArr (f p).src := by
  obtain ⟨mfin, bfin, hall⟩ := allSends_eq h hf
  rw [messagesOn_eq_chanOf, chanOf_allSends _ hall]
  simp only [Channel.toRaw_name]
  rw [chanOf_verifier_statePull,
    chanOf_memSeed_eq_nil _ _ (by simp [StatePull, MemPull]) (by simp [StatePull, MemPush]),
    chanOf_bcSeed_eq_nil _ (by simp [StatePull, BytecodePull]) (by simp [StatePull, BytecodePush])]
  have hrow : ∀ p, chanOf StatePull.name (f p).sends = [regsArr (f p).src] := fun p ↦ by
    rw [RowRec.chanOf_sends_of_ne _ (by simp [StatePull, MemPull]) (by simp [StatePull, MemPush])]
    exact sendsOf_statePull _ _ _ _ _ _
  simp only [hrow, List.append_nil, flatMap_singleton_eq_map']
  rfl

/-! ## The run -/

/-- **The walk of a witness**, under any semantics `S` its rows are steps of: records for its
rows and a run under `S` from the initial to the final registers over the image the data names,
each of whose steps is a row. -/
theorem exists_walkB (S : KeccakSem) (h : SatisfiedByB prog input w)
    (hS : ∀ f, OpRecs w f → RowsStep S w f) :
    ∃ f, OpRecs w f ∧ ∃ n, runB S prog (imageOf w.data).2 n Registers.initial = some (Registers.final prog) ∧
      ∀ k < n, ∃ p ∈ opPairs w, runB S prog (imageOf w.data).2 k Registers.initial = some (f p).src ∧
        runB S prog (imageOf w.data).2 (k + 1) Registers.initial = some (f p).next := by
  obtain ⟨f, hf⟩ := exists_opRecs w
  refine ⟨f, hf, ?_⟩
  have hb := h.state_balanced
  unfold BalancedPair at hb
  rw [statePush_eq h hf, statePull_eq h hf] at hb
  have hperm := hb.map arrRegs
  simp only [List.map_cons, List.map_map, Function.comp_def, arrRegs_regsArr] at hperm
  exact exists_runB_of_perm S (fun p ↦ (f p).src) (fun p ↦ (f p).next) (opPairs w)
    (fun p hp ↦ (hS f hf p hp).1) Registers.initial hperm

/-- **The walk of a satisfying witness**: records for its rows and a run from the initial to the
final registers over the image the data names, each of whose steps is a row. -/
theorem exists_walk (h : SatisfiedBy prog input w) :
    ∃ f, OpRecs w f ∧ ∃ n, run prog (imageOf w.data).2 n Registers.initial = some (Registers.final prog) ∧
      ∀ k < n, ∃ p ∈ opPairs w, run prog (imageOf w.data).2 k Registers.initial = some (f p).src ∧
        run prog (imageOf w.data).2 (k + 1) Registers.initial = some (f p).next := by
  simpa only [runB_deployed] using
    exists_walkB keccakDeployed h.toB fun _ hf ↦ rowsStep_deployed h hf

/-- **Specification Proposition 6.1**: a balanced state channel over rows that are steps contains a
run from `(1, 1)` to `(g^(N_prog - 1), 1)`, cut at its first visit of the final state; the remaining
rows are closed walks. -/
theorem exists_run_of_balanced (h : SatisfiedBy prog input w) :
    ∃ n, run prog (imageOf w.data).2 n Registers.initial = some (Registers.final prog) := by
  obtain ⟨-, -, n, hn, -⟩ := exists_walk h
  exact ⟨n, hn⟩

end LeanVM.Arithmetization
