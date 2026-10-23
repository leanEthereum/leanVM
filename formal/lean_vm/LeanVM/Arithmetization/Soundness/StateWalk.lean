/-
  LeanVM.Arithmetization.Soundness.StateWalk

  The state channel of a satisfying witness: every row of the six tables is a step of the program
  over the committed image, no row sits at the sentinel counter, and the balanced state pair
  contains a run from the initial to the final registers.
-/

module

public import LeanVM.Arithmetization.Soundness.BytecodeChannel
public import LeanVM.Arithmetization.Soundness.Walk

@[expose] public section

/-!
# The state channel

At leanVM pin `127510d14c98ade4e8a97646c44fa7f1ff5e752d` and Clean pin `42fe4b26`. Specification
Proposition 6.1 (`doc/leanvm/body/06-bus-interactions.tex`, §6.1), as `no_row_at_sentinel` and
`exists_run_of_balanced`. They assume the constraint statement `SatisfiedBy` and `SentinelSafe`
(the last instruction is not a `JUMP`), and serve `constraintSoundness`.

**The rows are steps** (`opRecs_step`). For a row of the six tables, the table's `Assumptions`
are `SatisfiedBy.blake2s_valid` (`assumptions_of_blake2sRowsValid`), its constraints are
`SatisfiedBy.constraints`, and the guarantees of its pulls are the two lookup theorems
(`mem_channel_sound`, `bytecode_guarantee`; every interaction is on one of the six channels,
`ChannelOk`). The table's soundness (`Soundness.Rows`) makes the row execute an instruction encoded
by its bytecode read, which `opRecs_bc_sound` makes the program's at the row's counter: the row is
`step prog L` from its pulled state to its pushed state, `L` the image the data names.

**No row at the sentinel** (`no_row_at_sentinel`). A row at the sentinel
counter `g^(N_prog - 1)` executes the sentinel slot's instruction, which is not a `JUMP`
(`SentinelSafe`), so it pushes `(g^N_prog, fp)`. Balance makes some pull carry that state: not the
verifier's `(g^(N_prog - 1), 1)`, and not a row's, whose counter is `g^k` for a slot `k < N_prog`
(the bytecode channel); both since `g` has order `2^64 - 1 > N_prog`.

**The run** (`exists_run_of_balanced`, Proposition 6.1). The state pair pushes `(1, 1)` (the
verifier) and the rows' successors, and pulls `(g^(N_prog - 1), 1)` (the verifier) and the rows'
states; its balance is the hypothesis of `exists_run_of_perm` (`Soundness.Walk`) over the rows,
which yields a run from `Regs.initial` to `Regs.final prog`, each of whose steps is a row
(`exists_walk`, which `Soundness.Theorem` uses for `AssignmentRepresents`).

## Why the rows, not `w.interactions`

`no_row_at_sentinel` is not stated over `w.interactions`, which includes the verifier's own
pull of the final registers `(g^(N_prog - 1), 1)` (Clean's `EnsembleWitness.interactions` ranges
over `allTables`, the verifier table first). Over those it is false for every witness, satisfying
or not (`verifier_pulls_sentinel` in `tests/LeanVMTests/Arithmetization/Soundness/Theorem.lean`);
the statement proved here quantifies over the rows of the witness's tables, `w.tables`, which is
what "no row sits at the sentinel counter" means.

## Wrong readings excluded

* The state pull carries no guarantee: nothing is claimed of a pulled state
  except through the walk; the rows not on the run are closed walks.
* A row at the sentinel is not excluded locally: its table accepts it, and only the balance of
  the state pair rejects it.
-/

namespace LeanVM.Arithmetization

open LeanVM.Parameters LeanVM.Semantics
open Air.Flat (Component EnsembleWitness)

variable {prog : Program} {input : PublicInput} {w : EnsembleWitness (leanIsaEnsemble prog)}

/-! ## The rows are steps -/

/-- An interaction of a table is sent by one of its rows. -/
theorem mem_rowSends_of_mem_interactions {t : Air.Flat.Table K} {i : Interaction K}
    (hi : i ∈ t.interactions) :
    ∃ row ∈ t.table, i.msg ∈ chanOf i.channel.name (rowSends t.component (t.environment row)) := by
  unfold Air.Flat.Table.interactions at hi
  obtain ⟨row, hrow, hi⟩ := List.mem_flatMap.mp hi
  refine ⟨row, hrow, ?_⟩
  rw [Component.interactionsValues_eq] at hi
  unfold chanOf rowSends
  refine List.mem_map.mpr ⟨(i.channel.name, i.msg), List.mem_filter.mpr ⟨?_, by simp⟩, rfl⟩
  exact List.mem_map_of_mem hi

/-- The interactions of a row of a witness's table are interactions of the witness. -/
theorem eval_mem_interactions {t : Air.Flat.Table K} (ht : t ∈ w.tables) {row : Array K}
    (hrow : row ∈ t.table) {a : AbstractInteraction K}
    (ha : a ∈ t.component.operations.interactions) :
    a.eval (t.environment row) ∈ w.interactions := by
  unfold EnsembleWitness.interactions
  refine List.mem_flatMap.mpr ⟨t, w.mem_allTables_of_mem_tables ht, ?_⟩
  unfold Air.Flat.Table.interactions
  exact List.mem_flatMap.mpr ⟨row, hrow, List.mem_map_of_mem ha⟩

/-- The pulls of a row of the six tables have their guarantees: the memory reads are the image's
words (`mem_channel_sound`) and the bytecode entry decodes (`bytecode_guarantee`). -/
theorem opRecs_guarantees (h : SatisfiedBy prog input w) {f : Air.Flat.Table K × Array K → RowRec}
    (hf : OpRecs w f) {p : Air.Flat.Table K × Array K} (hp : p ∈ opPairs w) :
    p.1.component.operations.FullGuarantees (p.1.environment p.2) := by
  obtain ⟨ht, hrow⟩ := mem_opPairs hp
  have ht' := List.mem_of_mem_take ht
  have hdata := environment_data ht' p.2
  intro a ha
  have hmem := eval_mem_interactions ht' hrow ha
  rcases (hf p hp).2.2.1 a ha with hc | hc | hc
  · obtain ⟨ch, mult, msg, ag⟩ := a
    dsimp only at hc
    subst hc
    intro _ _
    rw [hdata]
    exact mem_channel_sound h _ hmem rfl _
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
      ∃ k : Fin (2 ^ prog.logSize), (f p).pc = gpow k ∧
        ((prog.code k).opcode ≠ .jump → (f p).next = ⟨g * (f p).pc, (f p).fp⟩) := by
  obtain ⟨ht, hrow⟩ := mem_opPairs hp
  have ht' := List.mem_of_mem_take ht
  have ha := assumptions_of_blake2sRowsValid h.blake2s_valid p.1
    (w.mem_allTables_of_mem_tables ht') p.2 hrow
  have hc := h.constraints p.1 (w.mem_allTables_of_mem_tables ht') p.2 hrow
  obtain ⟨ins, he, hexec, hnj⟩ := (hf p hp).2.2.2 ha hc (opRecs_guarantees h hf hp)
  obtain ⟨k, hpc, hek⟩ := opRecs_bc_sound h hf hp
  have hins : prog.code k = ins := entry_injective (hek.symm.trans he)
  refine ⟨?_, k, hpc, fun hj ↦ hnj (hins ▸ hj)⟩
  have hfetch : prog.fetch (f p).src.pc = some ins := by
    rw [show (f p).src.pc = (f p).pc from rfl, hpc, Program.fetch_gpow, hins]
  rw [step_of_fetch_eq_some hfetch]
  exact hexec

/-! ## The state pair -/

/-- A state message as an array. -/
def regsArr (r : Regs K) : Array K := #[r.pc, r.fp]

/-- The state of a state message, `0` for a missing coordinate. -/
def arrRegs (a : Array K) : Regs K := ⟨a.getD 0 0, a.getD 1 0⟩

/-- Reading a state message back gives the state. -/
theorem arrRegs_regsArr (r : Regs K) : arrRegs (regsArr r) = r := rfl

/-- **The states a satisfying witness pushes**: the verifier's `(1, 1)` and the rows'
successors. -/
theorem statePush_eq (h : SatisfiedBy prog input w) {f : Air.Flat.Table K × Array K → RowRec}
    (hf : OpRecs w f) :
    messagesOn w StatePush.toRaw =
      regsArr Regs.initial :: (opPairs w).map fun p ↦ regsArr (f p).next := by
  obtain ⟨mfin, bfin, hall⟩ := allSends_eq h hf
  rw [messagesOn_eq_chanOf, chanOf_allSends _ hall]
  simp only [Channel.toRaw_name]
  rw [chanOf_verifier_statePush,
    chanOf_memSeed_eq_nil _ _ (by simp [StatePush, MemPull]) (by simp [StatePush, MemPush]),
    chanOf_bcSeed_eq_nil _ (by simp [StatePush, BytecodePull]) (by simp [StatePush, BytecodePush])]
  simp only [RowRec.sends, chanOf, sendsOf_statePush, List.append_nil, flatMap_singleton_eq_map']
  rfl

/-- **The states a satisfying witness pulls**: the verifier's final registers and the rows'
states. -/
theorem statePull_eq (h : SatisfiedBy prog input w) {f : Air.Flat.Table K × Array K → RowRec}
    (hf : OpRecs w f) :
    messagesOn w StatePull.toRaw =
      regsArr (Regs.final prog) :: (opPairs w).map fun p ↦ regsArr (f p).src := by
  obtain ⟨mfin, bfin, hall⟩ := allSends_eq h hf
  rw [messagesOn_eq_chanOf, chanOf_allSends _ hall]
  simp only [Channel.toRaw_name]
  rw [chanOf_verifier_statePull,
    chanOf_memSeed_eq_nil _ _ (by simp [StatePull, MemPull]) (by simp [StatePull, MemPush]),
    chanOf_bcSeed_eq_nil _ (by simp [StatePull, BytecodePull]) (by simp [StatePull, BytecodePush])]
  simp only [RowRec.sends, chanOf, sendsOf_statePull, List.append_nil, flatMap_singleton_eq_map']
  rfl

/-! ## No row at the sentinel -/

/-- The bytecode has at most `2^32` slots, fewer than the order of `g`. -/
theorem two_pow_logSize_lt (prog : Program) : 2 ^ prog.logSize < 2 ^ 64 - 1 :=
  lt_of_le_of_lt (Nat.pow_le_pow_right (by norm_num) prog.logSize_le) (by decide)

/-- **No row of the six tables sits at the sentinel counter**: its instruction is not a `JUMP`, so
it would push `(g^N_prog, fp)`, which no pull balances. -/
theorem opRecs_pc_ne_finalPc (hsafe : SentinelSafe prog) (h : SatisfiedBy prog input w)
    {f : Air.Flat.Table K × Array K → RowRec} (hf : OpRecs w f) {p : Air.Flat.Table K × Array K}
    (hp : p ∈ opPairs w) : (f p).pc ≠ prog.finalPc := by
  intro hfin
  have hN := two_pow_logSize_lt prog
  have hpos := Nat.two_pow_pos prog.logSize
  obtain ⟨-, k, hk, hnj⟩ := opRecs_step h hf hp
  have hkN : (k : ℕ) = 2 ^ prog.logSize - 1 := by
    have : gpow k = gpow (2 ^ prog.logSize - 1) := hk.symm.trans hfin
    exact gpow_injOn (by simp only [Set.mem_Iio]; have := k.isLt; omega)
      (by simp only [Set.mem_Iio]; omega) this
  have hsafe : (prog.code k).opcode ≠ .jump := by
    have hk' : k = ⟨2 ^ prog.logSize - 1, Nat.sub_lt (Nat.two_pow_pos _) (by decide)⟩ :=
      Fin.ext hkN
    rw [hk']
    exact hsafe
  have hnext := hnj hsafe
  have hpush : regsArr ⟨gpow (2 ^ prog.logSize), (f p).fp⟩ ∈ messagesOn w StatePush.toRaw := by
    rw [statePush_eq h hf]
    refine List.mem_cons_of_mem _ (List.mem_map.mpr ⟨p, hp, ?_⟩)
    rw [hnext, hfin, Program.finalPc, ← gpow_succ, Nat.sub_add_cancel hpos]
  have hpull := h.state_balanced.subset hpush
  rw [statePull_eq h hf] at hpull
  rcases List.mem_cons.mp hpull with heq | heq
  · have h1 : gpow (2 ^ prog.logSize) = gpow (2 ^ prog.logSize - 1) :=
      (by simpa [regsArr, Regs.final, Program.finalPc] using heq : _ ∧ _).1
    have := gpow_injOn (by simp only [Set.mem_Iio]; omega) (by simp only [Set.mem_Iio]; omega) h1
    omega
  · obtain ⟨q, hq, hqe⟩ := List.mem_map.mp heq
    obtain ⟨-, k', hk', -⟩ := opRecs_step h hf hq
    have h1 : gpow (2 ^ prog.logSize) = gpow k' := by
      rw [← hk']
      exact (by simpa [regsArr, RowRec.src] using hqe.symm : _ ∧ _).1
    have := gpow_injOn (by simp only [Set.mem_Iio]; omega)
      (by simp only [Set.mem_Iio]; have := k'.isLt; omega) h1
    have := k'.isLt
    omega

/-- **No row sits at the sentinel counter**: no state pull of a row of the
witness's tables carries the counter `g^(N_prog - 1)`. Its bytecode entry is not a `JUMP`, so the
row would push `(g^N_prog, fp)`, a counter no bytecode read can balance. The verifier's own pull
of the final registers is not a row (the module docstring). -/
theorem no_row_at_sentinel (hsafe : SentinelSafe prog) (h : SatisfiedBy prog input w) :
    ∀ t ∈ w.tables, ∀ i ∈ t.interactions, i.channel.name = StatePull.name →
      ∀ pc fp : K, i.msg = #[pc, fp] → pc ≠ prog.finalPc := by
  obtain ⟨f, hf⟩ := exists_opRecs w
  intro t ht i hi hname pc fp hmsg
  obtain ⟨row, hrow, hsend⟩ := mem_rowSends_of_mem_interactions hi
  rw [hname] at hsend
  rw [tables_eq w] at ht
  rcases List.mem_append.mp ht with ht | ht
  · have hp : (t, row) ∈ opPairs w :=
      List.mem_flatMap.mpr ⟨t, ht, List.mem_map_of_mem hrow⟩
    rw [(hf _ hp).1, RowRec.sends, chanOf, sendsOf_statePull, hmsg] at hsend
    have : pc = (f (t, row)).pc := (by simpa using hsend : _ ∧ _).1
    rw [this]
    exact opRecs_pc_ne_finalPc hsafe h hf hp
  · exfalso
    have hblock : i.msg ∈ chanOf StatePull.name (tableSends t) :=
      (chanOf_flatMap' _ _ _).symm ▸ List.mem_flatMap.mpr ⟨row, hrow, hsend⟩
    rcases List.mem_cons.mp ht with rfl | ht
    · obtain ⟨mfin, hmem⟩ := memBlock_sends_eq h
      rw [hmem, chanOf_memSeed_eq_nil _ _ (by simp [StatePull, MemPull])
        (by simp [StatePull, MemPush])] at hblock
      exact List.not_mem_nil hblock
    · rw [List.mem_singleton] at ht
      subst ht
      obtain ⟨bfin, hbc⟩ := bcBlock_sends_eq h
      rw [hbc, chanOf_bcSeed_eq_nil _ (by simp [StatePull, BytecodePull])
        (by simp [StatePull, BytecodePush])] at hblock
      exact List.not_mem_nil hblock

/-! ## The run -/

/-- **The walk of a satisfying witness**: records for its rows and a run from the initial to the
final registers over the image the data names, each of whose steps is a row. -/
theorem exists_walk (hsafe : SentinelSafe prog) (h : SatisfiedBy prog input w) :
    ∃ f, OpRecs w f ∧ ∃ n, run prog (imageOf w.data).2 n Regs.initial = some (Regs.final prog) ∧
      ∀ k < n, ∃ p ∈ opPairs w, run prog (imageOf w.data).2 k Regs.initial = some (f p).src ∧
        run prog (imageOf w.data).2 (k + 1) Regs.initial = some (f p).next := by
  obtain ⟨f, hf⟩ := exists_opRecs w
  refine ⟨f, hf, ?_⟩
  have hb := h.state_balanced
  unfold BalancedPair at hb
  rw [statePush_eq h hf, statePull_eq h hf] at hb
  have hperm := hb.map arrRegs
  simp only [List.map_cons, List.map_map, Function.comp_def, arrRegs_regsArr] at hperm
  exact exists_run_of_perm (fun p ↦ (f p).src) (fun p ↦ (f p).next) (opPairs w)
    (fun p hp ↦ ⟨opRecs_pc_ne_finalPc hsafe h hf hp, (opRecs_step h hf hp).1⟩) Regs.initial hperm

/-- **Specification Proposition 6.1**: a balanced state channel over rows that are steps contains a
run from `(1, 1)` to `(g^(N_prog - 1), 1)`; the remaining rows are closed walks. -/
theorem exists_run_of_balanced (hsafe : SentinelSafe prog) (h : SatisfiedBy prog input w) :
    ∃ n, run prog (imageOf w.data).2 n Regs.initial = some (Regs.final prog) := by
  obtain ⟨-, -, n, hn, -⟩ := exists_walk hsafe h
  exact ⟨n, hn⟩

end LeanVM.Arithmetization
