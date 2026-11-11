/-
  LeanVM.Arithmetization.Completeness.Theorem

  Constraint completeness: a valid execution whose tables fit the row cap has a witness that
  satisfies the constraint statement and represents it.
-/

module

public import LeanVM.Arithmetization.Completeness.Satisfied

@[expose] public section

/-!
# Constraint completeness

At leanVM `3a37fb6e1c7423e36b67d1cac4eda70c3ad4dd45`. The completeness direction for the proof
system's constraint statement (`SatisfiedBy`). `constraintCompleteness`: a valid execution of at
most `2^30` steps has a witness of the ensemble at its memory log-size, satisfying
`SatisfiedBy prog input` and representing it.

**The witness.** The skeletons are the run's (`Execution.runSkels`: the states stepped from and the
instructions fetched there), and nothing else: a table holds exactly its run rows, any number of
them, and the protocol pads it to a power of two with public padding rows that are not on the bus
(`doc/leanvm` §`sec:e2e-pad`). `skelWitness` (`Completeness.Witness`) writes one row per skeleton in
the table of its opcode, the image as the memory block and the program as the bytecode block, with
the read counts that make the three channel pairs balance (`Completeness.Bus`,
`Completeness.Balance`), and the prover data Clean derives from the tables, whose image is the
trace's (`imageOf_skelWitness`). `skelWitness_satisfiedBy` (`Completeness.Satisfied`) reduces `SatisfiedBy`
to facts about the skeletons and the image, which this file proves:

* the skeletons are sound: the run's from the valid run (`skAt_ok`);
* the state pair balances: the run's pushes and pulls rotate with the boundary's initial push and
  final pull (`runSkels_state_perm`, from `shift_perm`);
* every table is within the row cap (`Execution.count_runSkels`);
* the memory window and the two public words, from `ValidExecution`.

`AssignmentRepresents` follows from `skelWitness_rowSteps`: every skeleton is a row whose state
pull is its state and push its successor, and the run's register sequence is the run's skeletons.

## Wrong readings excluded

* The row cap is not part of validity: a valid execution with more than `2^30` rows of one opcode
  has no witness at all (`Caps`), which is why the theorem takes `hrows`
  (`tests/LeanVMTests/Arithmetization/Completeness/LongRun.lean`).
* The witness represents `t` itself, over its own image: no row reads or writes a cell the run
  does not, and the memory is not grown.
-/

open scoped List

namespace LeanVM.Arithmetization

open LeanVM.Parameters LeanVM.Semantics
open Air.Flat (Component EnsembleWitness)

section Run

variable {prog : LeanIsaProgram}

/-- The state after `k` steps of the run of `t`, the initial state if the run fails. -/
noncomputable def stateAt (t : Execution prog) (k : ℕ) : Registers K :=
  (run prog t.memory k Registers.initial).getD Registers.initial

/-- The skeleton stepped from at step `k`: the state and the instruction fetched there. -/
noncomputable def skAt (t : Execution prog) (k : ℕ) : Skel :=
  ⟨(stateAt t k).pc, (stateAt t k).fp, (prog.fetch (stateAt t k).pc).getD (.setConstant 0 0)⟩

/-- A list all of whose entries map to `some` is the `filterMap` of the entries' values. -/
theorem filterMap_eq_map_of {α β : Type} (p : α → Option β) (f : α → β) (l : List α)
    (h : ∀ x ∈ l, p x = some (f x)) : l.filterMap p = l.map f := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    rw [List.filterMap_cons, h x List.mem_cons_self, List.map_cons, ih fun y hy ↦
      h y (List.mem_cons_of_mem _ hy)]

variable {t : Execution prog}

/-- The run to step `k ≤ steps` reaches `stateAt t k`. -/
theorem run_stateAt (hv : run prog t.memory t.stepCount Registers.initial = some (Registers.final prog)) {k : ℕ}
    (hk : k ≤ t.stepCount) : run prog t.memory k Registers.initial = some (stateAt t k) := by
  obtain ⟨r, hr, -⟩ := run_prefix (m := k) (n := t.stepCount - k)
    (by rwa [Nat.add_sub_cancel' hk])
  simp [stateAt, hr]

/-- Every step of a valid run is taken away from the final state, fetches and executes. -/
theorem stateAt_step (hv : run prog t.memory t.stepCount Registers.initial = some (Registers.final prog))
    {k : ℕ} (hk : k < t.stepCount) :
    stateAt t k ≠ Registers.final prog ∧ step prog t.memory (stateAt t k) = some (stateAt t (k + 1)) := by
  have h1 := run_stateAt hv (show k + 1 ≤ t.stepCount by omega)
  have h0 := run_stateAt hv hk.le
  rw [run_add, h0] at h1
  have h1' : run prog t.memory 1 (stateAt t k) = some (stateAt t (k + 1)) := h1
  have hne := ne_final_of_run_succ h1'
  refine ⟨hne, ?_⟩
  rw [run_succ_of_ne_final hne] at h1'
  generalize step prog t.memory (stateAt t k) = s at h1' ⊢
  cases s with
  | none => simp at h1'
  | some r => simpa using h1'

end Run

section Run

variable {prog : LeanIsaProgram} {t : Execution prog}

/-- The register sequence of a valid run is the states `stateAt t 0, …, stateAt t steps`. -/
theorem regs_eq_map (hv : run prog t.memory t.stepCount Registers.initial = some (Registers.final prog)) :
    t.regs = (List.range (t.stepCount + 1)).map (stateAt t) := by
  unfold Execution.regs
  exact filterMap_eq_map_of _ _ _ fun k hk ↦ by
    simp only [run_stateAt hv (Nat.lt_succ_iff.mp (List.mem_range.mp hk))]

/-- Every state stepped from fetches an instruction that executes to the next state. -/
theorem stateAt_exec (hv : run prog t.memory t.stepCount Registers.initial = some (Registers.final prog))
    {k : ℕ} (hk : k < t.stepCount) :
    ∃ ins, prog.fetch (stateAt t k).pc = some ins ∧
      execute t.memory (stateAt t k) ins = some (stateAt t (k + 1)) := by
  obtain ⟨-, hs⟩ := stateAt_step hv hk
  unfold step at hs
  obtain ⟨ins, hf, hex⟩ := Option.bind_eq_some_iff.mp hs
  exact ⟨ins, hf, hex⟩

/-- The instruction of a skeleton of the run is the one fetched. -/
theorem skAt_ins {k : ℕ} {ins : LeanIsaInstruction} (hf : prog.fetch (stateAt t k).pc = some ins) :
    (skAt t k).ins = ins := by
  simp only [skAt, hf, Option.getD_some]

/-- The skeletons of a valid run are those stepped from, one per step. -/
theorem runSkels_eq (hv : run prog t.memory t.stepCount Registers.initial = some (Registers.final prog)) :
    t.runSkels = (List.range t.stepCount).map (skAt t) := by
  unfold Execution.runSkels
  rw [regs_eq_map hv, List.range_succ, List.map_append, List.map_singleton, List.dropLast_concat,
    List.filterMap_map]
  refine filterMap_eq_map_of _ _ _ fun k hk ↦ ?_
  obtain ⟨ins, hf, -⟩ := stateAt_exec hv (List.mem_range.mp hk)
  simp only [Function.comp_apply, hf, Option.map_some, skAt, Option.getD_some]

/-- Every skeleton of a valid run is sound over the run's image. -/
theorem skAt_ok (hv : run prog t.memory t.stepCount Registers.initial = some (Registers.final prog))
    {k : ℕ} (hk : k < t.stepCount) : SkelOk prog t.memory (skAt t k) := by
  obtain ⟨ins, hf, hex⟩ := stateAt_exec hv hk
  refine ⟨?_, stateAt t (k + 1), ?_⟩
  · show prog.fetch (stateAt t k).pc = some (skAt t k).ins
    rw [skAt_ins hf]
    exact hf
  · show execute t.memory (stateAt t k) (skAt t k).ins = _
    rw [skAt_ins hf]
    exact hex

/-- The successor of a skeleton of the run is the next state. -/
theorem nextOf_skAt (hv : run prog t.memory t.stepCount Registers.initial = some
    (Registers.final prog))
    {k : ℕ} (hk : k < t.stepCount) : nextOf t.memory (skAt t k) = stateAt t (k + 1) := by
  obtain ⟨ins, hf, hex⟩ := stateAt_exec hv hk
  show (execute t.memory (stateAt t k) (skAt t k).ins).getD (stateAt t k) = _
  rw [skAt_ins hf, hex]
  rfl

/-- **The run's state pulls and pushes balance with the boundary**: the initial state is pushed,
the final one pulled, and each state stepped to is stepped from. -/
theorem runSkels_state_perm (hv : run prog t.memory t.stepCount Registers.initial = some (Registers.final prog)) :
    (#[1, 1] :: t.runSkels.map fun sk ↦ #[(nextOf t.memory sk).pc, (nextOf t.memory sk).fp]).Perm
      (#[prog.pcFinal, 1] :: t.runSkels.map fun sk ↦ #[sk.pc, sk.fp]) := by
  obtain ⟨f, hf⟩ : ∃ f : ℕ → Array K, f = fun k ↦ #[(stateAt t k).pc, (stateAt t k).fp] :=
    ⟨_, rfl⟩
  have hlast : stateAt t t.stepCount = Registers.final prog := by
    have := run_stateAt hv le_rfl
    rw [hv] at this
    exact (Option.some.inj this).symm
  have h0 : f 0 = #[1, 1] := by rw [hf]; rfl
  have hn : f t.stepCount = #[prog.pcFinal, 1] := by
    rw [hf]
    show #[(stateAt t t.stepCount).pc, (stateAt t t.stepCount).fp] = _
    rw [hlast]
    rfl
  have hstate : (List.range t.stepCount).map (fun k ↦ #[(skAt t k).pc, (skAt t k).fp]) =
      (List.range t.stepCount).map f := by rw [hf]; rfl
  have hnext : (List.range t.stepCount).map
      (fun k ↦ #[(nextOf t.memory (skAt t k)).pc, (nextOf t.memory (skAt t k)).fp]) =
      (List.range t.stepCount).map fun k ↦ f (k + 1) :=
    List.map_congr_left fun k hk ↦ by rw [nextOf_skAt hv (List.mem_range.mp hk), hf]
  rw [runSkels_eq hv, List.map_map, List.map_map]
  simp only [Function.comp_def]
  rw [hstate, hnext, ← h0, ← hn]
  exact shift_perm f t.stepCount

end Run

/-! ## The witness represents the trace -/

/-- **A skeleton's row steps.** Every skeleton of the list the witness is built from is a row
whose one state pull is its state and one state push its successor. -/
theorem skelWitness_rowSteps (prog : LeanIsaProgram) (input : PublicInput) {κ : ℕ}
    (img : MemoryImage κ) (S : List Skel) (hκ : κ ≤ maxLogMem)
    (hrows : ∀ op, Skel.count op S ≤ 2 ^ maxLogRows)
    (hS : ∀ sk ∈ S, ∃ next, execute img sk.regs sk.ins = some next) {sk : Skel}
    (hsk : sk ∈ S) : RowSteps (skelWitness prog input img S hκ hrows) sk.regs (nextOf img sk) := by
  have hR : ∀ r ∈ skelRows img S, ∃ next, execute img r.sk.regs r.sk.ins = some next :=
    fun r hr ↦ hS _ (mem_mkRows_sk hr)
  obtain ⟨r, hr, rfl⟩ : ∃ r ∈ skelRows img S, r.sk = sk := by
    have h := hsk
    rw [← mkRows_sk img (fun _ ↦ 0) (fun _ ↦ 0) S] at h
    obtain ⟨r, hr, h⟩ := List.mem_map.mp h
    exact ⟨r, hr, h⟩
  -- The witness's table of the row's opcode: the opcode's table, but for its data.
  have hT : ∃ t ∈ (skelWitness prog input img S hκ hrows).tables,
      t.component = opComponent r.sk.ins.opcode ∧
        t.table = opRows img (skelRows img S) r.sk.ins.opcode := by
    have hm : (opComponent r.sk.ins.opcode, opRows img (skelRows img S) r.sk.ins.opcode) ∈
        (skelTables prog img S hκ hrows).map fun t ↦ (t.component, t.table) := by
      cases h : r.sk.ins.opcode <;> simp [skelTables, opTable, ownTable]
    rw [← skelWitnessTables_map, List.mem_map] at hm
    obtain ⟨t, ht, he⟩ := hm
    exact ⟨t, ht, congrArg Prod.fst he, congrArg Prod.snd he⟩
  obtain ⟨t, ht, hc, htab⟩ := hT
  have hrow : PRow.raw img r ∈ t.table := by
    rw [htab]
    exact List.mem_map.mpr ⟨r, List.mem_filter.mpr ⟨hr, by simp⟩, rfl⟩
  refine ⟨t, ht, PRow.raw img r, hrow, ?_, ?_⟩
  · rw [rowMessagesOn_eq_rowSends, Air.Flat.Table.environment, hc,
      PRow.rowSends_raw (hR r hr) t.data, Channel.toRaw_name,
      PRow.sends_filter_of_ne img r (by simp [StatePull, MemPull]) (by simp [StatePull, MemPush])]
    exact sendsOf_statePull _ _ _ _ _ _
  · rw [rowMessagesOn_eq_rowSends, Air.Flat.Table.environment, hc,
      PRow.rowSends_raw (hR r hr) t.data, Channel.toRaw_name,
      PRow.sends_filter_of_ne img r (by simp [StatePush, MemPull]) (by simp [StatePush, MemPush])]
    exact sendsOf_statePush _ _ _ _ _ _

/-- **The witness of a run represents its trace**: the image the data names is the
trace's, and every step of the trace's register sequence is a row. -/
theorem skelWitness_represents (prog : LeanIsaProgram) (input : PublicInput) {T : Execution prog}
    (hκ : T.logMemorySize ≤ maxLogMem)
    (hv : run prog T.memory T.stepCount Registers.initial = some (Registers.final prog))
    (S : List Skel) (hrows : ∀ op, Skel.count op S ≤ 2 ^ maxLogRows)
    (hS : ∀ sk ∈ S, ∃ next, execute T.memory sk.regs sk.ins = some next)
    (hrun : ∀ k < T.stepCount, skAt T k ∈ S) :
    AssignmentRepresents (skelWitness prog input T.memory S hκ hrows) T where
  κ_eq := imageOf_fst_of_memRows (memRows_skelWitness prog input T.memory S hκ hrows) hκ
  image_eq := fun i hi ↦
    imageOf_apply_of_memRows (memRows_skelWitness prog input T.memory S hκ hrows) hκ i _
  regs_embed := by
    intro k hk
    have hlen : T.regs.length = T.stepCount + 1 := Execution.regs_length hv
    have e : ∀ j (hj : j < T.regs.length), T.regs[j] = stateAt T j := fun j hj ↦ by
      rw [List.getElem_of_eq (regs_eq_map hv) hj]
      simp
    have hk' : k < T.stepCount := by omega
    rw [e k (by omega), e (k + 1) hk]
    have := skelWitness_rowSteps prog input T.memory S hκ hrows hS (hrun k hk')
    rwa [nextOf_skAt hv hk'] at this

/-! ## The theorem -/

/-- **Constraint completeness, with the row counts.** A valid execution whose run has at most
`2^maxLogRows` rows of every opcode has a witness, at the trace's memory log-size, satisfying the
constraint statement and representing it, whose six opcode tables, in the ensemble's order, hold
exactly the run's rows. -/
theorem constraintCompleteness_rows {prog : LeanIsaProgram} {input : PublicInput} {t :
    Execution prog}
    (h : ValidExecution prog input t) (hrows : ∀ op, t.runRows op ≤ 2 ^ maxLogRows) :
    ∃ w : EnsembleWitness (leanIsaEnsemble prog t.logMemorySize),
      SatisfiedBy prog input w ∧ AssignmentRepresents w t ∧
        ∀ j : Fin 6, (tableAt w ⟨j, by omega⟩).table.length = t.runRows (tableOpcode j) := by
  obtain ⟨⟨hmin, hcap, hw0, hw1⟩, hrun⟩ := h
  have hS : ∀ sk ∈ t.runSkels, SkelOk prog t.memory sk := by
    intro sk hsk
    rw [runSkels_eq hrun] at hsk
    obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hsk
    exact skAt_ok hrun (List.mem_range.mp hk)
  have hcount : ∀ op, Skel.count op t.runSkels ≤ 2 ^ maxLogRows :=
    fun op ↦ (t.count_runSkels op).trans_le (hrows op)
  have hlen : ∀ op, (opRows t.memory (skelRows t.memory t.runSkels) op).length = t.runRows op := by
    intro op
    rw [opRows, List.length_map, skelRows, length_filter_mkRows, Execution.count_runSkels]
  refine ⟨skelWitness prog input t.memory t.runSkels hcap hcount, ?_, ?_, ?_⟩
  · exact skelWitness_satisfiedBy prog input t.memory _ hmin hcap hS (runSkels_state_perm hrun)
      hcount hw0 hw1
  · refine skelWitness_represents prog input hcap hrun _ hcount (fun sk hsk ↦ (hS sk hsk).2) ?_
    intro k hk
    rw [runSkels_eq hrun]
    exact List.mem_map_of_mem (List.mem_range.mpr hk)
  · intro j
    rw [skelWitness_tableAt_table]
    fin_cases j
    exacts [hlen .xor, hlen .mulNative, hlen .setConstant, hlen .deref, hlen .jump, hlen .keccak]

/-- **Constraint completeness**. A valid execution of at most `2^maxLogRows` steps has a witness,
at the trace's memory log-size, satisfying the constraint statement and representing it: the rows
of the run in the six tables, the image as the memory block and the program as the bytecode
block, with the counts that balance the buses (`constraintCompleteness_rows`, which also gives
the tables' row counts). -/
theorem constraintCompleteness {prog : LeanIsaProgram} {input : PublicInput} {t : Execution prog}
    (h : ValidExecution prog input t) (hsteps : t.stepCount ≤ 2 ^ maxLogRows) :
    ∃ w : EnsembleWitness (leanIsaEnsemble prog t.logMemorySize),
      SatisfiedBy prog input w ∧ AssignmentRepresents w t := by
  obtain ⟨w, hw, hrep, -⟩ := constraintCompleteness_rows h
    fun op ↦ (t.runRows_le_steps h.2 op).trans hsteps
  exact ⟨w, hw, hrep⟩

end LeanVM.Arithmetization
