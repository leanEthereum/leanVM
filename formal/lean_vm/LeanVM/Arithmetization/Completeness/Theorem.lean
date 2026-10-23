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
most `2^32` steps has a witness satisfying `SatisfiedBy prog input` and representing it.

**The witness.** The skeletons are the run's (`Trace.runSkels`: the states stepped from and the
instructions fetched there), and nothing else: a table holds exactly its run rows, any number of
them, and the protocol pads it to a power of two with public padding rows that are not on the bus
(`doc/leanvm` §`sec:e2e-pad`). `skelWitness` (`Completeness.Witness`) writes one row per skeleton in
the table of its opcode, the image as the memory block and the program as the bytecode block, with
the read counts that make the three channel pairs balance (`Completeness.Bus`,
`Completeness.Balance`). `skelWitness_satisfiedBy` (`Completeness.Satisfied`) reduces `SatisfiedBy`
to facts about the skeletons and the image, which this file proves:

* the skeletons are sound: the run's from the valid run (`skAt_ok`);
* the state pair balances: the run's pushes and pulls rotate with the boundary's initial push and
  final pull (`runSkels_state_perm`, from `shift_perm`);
* every table is within the row cap (`Trace.count_runSkels`);
* the memory window and the two public words, from `ValidExecution`.

`AssignmentRepresents` follows from `skelWitness_rowSteps`: every skeleton is a row whose state
pull is its state and push its successor, and the run's register sequence is the run's skeletons.

## Wrong readings excluded

* The row cap is not part of validity: a valid execution with more than `2^32` rows of one opcode
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

variable {prog : Program}

/-- The state after `k` steps of the run of `t`, the initial state if the run fails. -/
noncomputable def stateAt (t : Trace prog) (k : ℕ) : Regs K :=
  (run prog t.image k Regs.initial).getD Regs.initial

/-- The skeleton stepped from at step `k`: the state and the instruction fetched there. -/
noncomputable def skAt (t : Trace prog) (k : ℕ) : Skel :=
  ⟨(stateAt t k).pc, (stateAt t k).fp, (prog.fetch (stateAt t k).pc).getD (.setConstant 0 0)⟩

/-- A list all of whose entries map to `some` is the `filterMap` of the entries' values. -/
theorem filterMap_eq_map_of {α β : Type} (p : α → Option β) (f : α → β) (l : List α)
    (h : ∀ x ∈ l, p x = some (f x)) : l.filterMap p = l.map f := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    rw [List.filterMap_cons, h x List.mem_cons_self, List.map_cons, ih fun y hy ↦
      h y (List.mem_cons_of_mem _ hy)]

variable {t : Trace prog}

/-- The run to step `k ≤ steps` reaches `stateAt t k`. -/
theorem run_stateAt (hv : run prog t.image t.steps Regs.initial = some (Regs.final prog)) {k : ℕ}
    (hk : k ≤ t.steps) : run prog t.image k Regs.initial = some (stateAt t k) := by
  obtain ⟨r, hr, -⟩ := run_prefix (m := k) (n := t.steps - k)
    (by rwa [Nat.add_sub_cancel' hk])
  simp [stateAt, hr]

/-- Every step of a valid run is taken away from the sentinel, fetches and executes. -/
theorem stateAt_step (hv : run prog t.image t.steps Regs.initial = some (Regs.final prog))
    {k : ℕ} (hk : k < t.steps) :
    (stateAt t k).pc ≠ prog.finalPc ∧ step prog t.image (stateAt t k) = some (stateAt t (k + 1)) := by
  have h1 := run_stateAt hv (show k + 1 ≤ t.steps by omega)
  have h0 := run_stateAt hv hk.le
  rw [run_add, h0] at h1
  have h1' : run prog t.image 1 (stateAt t k) = some (stateAt t (k + 1)) := h1
  have hpc := pc_ne_finalPc_of_run_succ h1'
  refine ⟨hpc, ?_⟩
  rw [run_succ_of_ne hpc] at h1'
  generalize step prog t.image (stateAt t k) = s at h1' ⊢
  cases s with
  | none => simp at h1'
  | some r => simpa using h1'

end Run

section Run

variable {prog : Program} {t : Trace prog}

/-- The register sequence of a valid run is the states `stateAt t 0, …, stateAt t steps`. -/
theorem regs_eq_map (hv : run prog t.image t.steps Regs.initial = some (Regs.final prog)) :
    t.regs = (List.range (t.steps + 1)).map (stateAt t) := by
  unfold Trace.regs
  exact filterMap_eq_map_of _ _ _ fun k hk ↦ by
    simp only [run_stateAt hv (Nat.lt_succ_iff.mp (List.mem_range.mp hk))]

/-- Every state stepped from fetches an instruction that executes to the next state. -/
theorem stateAt_exec (hv : run prog t.image t.steps Regs.initial = some (Regs.final prog))
    {k : ℕ} (hk : k < t.steps) :
    ∃ ins, prog.fetch (stateAt t k).pc = some ins ∧
      execute t.image (stateAt t k) ins = some (stateAt t (k + 1)) := by
  obtain ⟨-, hs⟩ := stateAt_step hv hk
  unfold step at hs
  obtain ⟨ins, hf, hex⟩ := Option.bind_eq_some_iff.mp hs
  exact ⟨ins, hf, hex⟩

/-- The instruction of a skeleton of the run is the one fetched. -/
theorem skAt_ins {k : ℕ} {ins : Instr} (hf : prog.fetch (stateAt t k).pc = some ins) :
    (skAt t k).ins = ins := by
  simp only [skAt, hf, Option.getD_some]

/-- The skeletons of a valid run are those stepped from, one per step. -/
theorem runSkels_eq (hv : run prog t.image t.steps Regs.initial = some (Regs.final prog)) :
    t.runSkels = (List.range t.steps).map (skAt t) := by
  unfold Trace.runSkels
  rw [regs_eq_map hv, List.range_succ, List.map_append, List.map_singleton, List.dropLast_concat,
    List.filterMap_map]
  refine filterMap_eq_map_of _ _ _ fun k hk ↦ ?_
  obtain ⟨ins, hf, -⟩ := stateAt_exec hv (List.mem_range.mp hk)
  simp only [Function.comp_apply, hf, Option.map_some, skAt, Option.getD_some]

/-- Every skeleton of a valid run is sound over the run's image. -/
theorem skAt_ok (hv : run prog t.image t.steps Regs.initial = some (Regs.final prog))
    {k : ℕ} (hk : k < t.steps) : SkelOk prog t.image (skAt t k) := by
  obtain ⟨ins, hf, hex⟩ := stateAt_exec hv hk
  refine ⟨?_, stateAt t (k + 1), ?_⟩
  · show prog.fetch (stateAt t k).pc = some (skAt t k).ins
    rw [skAt_ins hf]
    exact hf
  · show execute t.image (stateAt t k) (skAt t k).ins = _
    rw [skAt_ins hf]
    exact hex

/-- The successor of a skeleton of the run is the next state. -/
theorem nextOf_skAt (hv : run prog t.image t.steps Regs.initial = some (Regs.final prog))
    {k : ℕ} (hk : k < t.steps) : nextOf t.image (skAt t k) = stateAt t (k + 1) := by
  obtain ⟨ins, hf, hex⟩ := stateAt_exec hv hk
  show (execute t.image (stateAt t k) (skAt t k).ins).getD (stateAt t k) = _
  rw [skAt_ins hf, hex]
  rfl

/-- **The run's state pulls and pushes balance with the boundary**: the initial state is pushed,
the final one pulled, and each state stepped to is stepped from. -/
theorem runSkels_state_perm (hv : run prog t.image t.steps Regs.initial = some (Regs.final prog)) :
    (#[1, 1] :: t.runSkels.map fun sk ↦ #[(nextOf t.image sk).pc, (nextOf t.image sk).fp]).Perm
      (#[prog.finalPc, 1] :: t.runSkels.map fun sk ↦ #[sk.pc, sk.fp]) := by
  obtain ⟨f, hf⟩ : ∃ f : ℕ → Array K, f = fun k ↦ #[(stateAt t k).pc, (stateAt t k).fp] :=
    ⟨_, rfl⟩
  have hlast : stateAt t t.steps = Regs.final prog := by
    have := run_stateAt hv le_rfl
    rw [hv] at this
    exact (Option.some.inj this).symm
  have h0 : f 0 = #[1, 1] := by rw [hf]; rfl
  have hn : f t.steps = #[prog.finalPc, 1] := by
    rw [hf]
    show #[(stateAt t t.steps).pc, (stateAt t t.steps).fp] = _
    rw [hlast]
    rfl
  have hstate : (List.range t.steps).map (fun k ↦ #[(skAt t k).pc, (skAt t k).fp]) =
      (List.range t.steps).map f := by rw [hf]; rfl
  have hnext : (List.range t.steps).map
      (fun k ↦ #[(nextOf t.image (skAt t k)).pc, (nextOf t.image (skAt t k)).fp]) =
      (List.range t.steps).map fun k ↦ f (k + 1) :=
    List.map_congr_left fun k hk ↦ by rw [nextOf_skAt hv (List.mem_range.mp hk), hf]
  rw [runSkels_eq hv, List.map_map, List.map_map]
  simp only [Function.comp_def]
  rw [hstate, hnext, ← h0, ← hn]
  exact shift_perm f t.steps

end Run

/-! ## The witness represents the trace -/

/-- **A skeleton's row steps.** Every skeleton of the list the witness is built from is a row
whose one state pull is its state and one state push its successor. -/
theorem skelWitness_rowSteps (prog : Program) (input : PublicInput) {κ : ℕ} (img : MemImage κ)
    (S : List Skel) (hS : ∀ sk ∈ S, ∃ next, execute img sk.regs sk.ins = some next) {sk : Skel}
    (hsk : sk ∈ S) : RowSteps (skelWitness prog input img S) sk.regs (nextOf img sk) := by
  have hR : ∀ r ∈ skelRows img S, ∃ next, execute img r.sk.regs r.sk.ins = some next :=
    fun r hr ↦ hS _ (mem_mkRows_sk hr)
  obtain ⟨r, hr, rfl⟩ : ∃ r ∈ skelRows img S, r.sk = sk := by
    have h := hsk
    rw [← mkRows_sk img (fun _ ↦ 0) (fun _ ↦ 0) S] at h
    obtain ⟨r, hr, h⟩ := List.mem_map.mp h
    exact ⟨r, hr, h⟩
  have hmemT : ∀ op, opTable img (imageData img) (skelRows img S) op ∈
      (skelWitness prog input img S).tables := by
    intro op
    cases op <;> simp [skelWitness]
  refine ⟨opTable img (imageData img) (skelRows img S) r.sk.ins.opcode, hmemT _, PRow.raw img r,
    List.mem_map.mpr ⟨r, List.mem_filter.mpr ⟨hr, by simp⟩, rfl⟩, ?_, ?_⟩
  · rw [rowMessagesOn_eq_rowSends]
    show ((rowSends (opComponent r.sk.ins.opcode)
      (Environment.fromArray (r.raw img) (imageData img))).filter _).map _ = _
    rw [PRow.rowSends_raw (hR r hr) (imageData img)]
    exact sendsOf_statePull _ _ _ _ _ _
  · rw [rowMessagesOn_eq_rowSends]
    show ((rowSends (opComponent r.sk.ins.opcode)
      (Environment.fromArray (r.raw img) (imageData img))).filter _).map _ = _
    rw [PRow.rowSends_raw (hR r hr) (imageData img)]
    exact sendsOf_statePush _ _ _ _ _ _

/-- **The witness of a run represents its trace**: the image the data names is the
trace's, and every step of the trace's register sequence is a row. -/
theorem skelWitness_represents (prog : Program) (input : PublicInput) {T : Trace prog}
    (hκ : T.κ ≤ maxLogMem)
    (hv : run prog T.image T.steps Regs.initial = some (Regs.final prog)) (S : List Skel)
    (hS : ∀ sk ∈ S, ∃ next, execute T.image sk.regs sk.ins = some next)
    (hrun : ∀ k < T.steps, skAt T k ∈ S) :
    AssignmentRepresents (skelWitness prog input T.image S) T where
  κ_eq := imageData_logSize T.image hκ
  image_eq := fun i hi ↦ imageData_apply' T.image hκ i _
  regs_embed := by
    intro k hk
    have hlen : T.regs.length = T.steps + 1 := Trace.regs_length hv
    have e : ∀ j (hj : j < T.regs.length), T.regs[j] = stateAt T j := fun j hj ↦ by
      rw [List.getElem_of_eq (regs_eq_map hv) hj]
      simp
    have hk' : k < T.steps := by omega
    rw [e k (by omega), e (k + 1) hk]
    have := skelWitness_rowSteps prog input T.image S hS (hrun k hk')
    rwa [nextOf_skAt hv hk'] at this

/-! ## The theorem -/

/-- **Constraint completeness, with the row counts.** A valid execution whose run has at most
`2^maxLogRows` rows of every opcode has a witness satisfying the constraint statement and
representing it, whose six opcode tables, in the ensemble's order, hold exactly the run's rows. -/
theorem constraintCompleteness_rows {prog : Program} {input : PublicInput} {t : Trace prog}
    (h : ValidExecution prog input t) (hrows : ∀ op, t.runRows op ≤ 2 ^ maxLogRows) :
    ∃ w, SatisfiedBy prog input w ∧ AssignmentRepresents w t ∧
      ∀ j : Fin 6, (tableAt w ⟨j, by omega⟩).table.length = t.runRows (tableOpcode j) := by
  obtain ⟨⟨hmin, hcap, hw0, hw1⟩, hrun⟩ := h
  have hS : ∀ sk ∈ t.runSkels, SkelOk prog t.image sk := by
    intro sk hsk
    rw [runSkels_eq hrun] at hsk
    obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hsk
    exact skAt_ok hrun (List.mem_range.mp hk)
  have hlen : ∀ op, List.length
      (opTable t.image (imageData t.image) (skelRows t.image t.runSkels) op).table =
        t.runRows op := by
    intro op
    show (List.map _ (List.filter _ _)).length = _
    rw [List.length_map, skelRows, length_filter_mkRows, Trace.count_runSkels]
  refine ⟨skelWitness prog input t.image t.runSkels, ?_, ?_, ?_⟩
  · refine skelWitness_satisfiedBy prog input t.image _ hmin hcap hS (runSkels_state_perm hrun)
      (fun op ↦ (t.count_runSkels op).trans_le (hrows op)) hw0 hw1
  · refine skelWitness_represents prog input hcap hrun _ (fun sk hsk ↦ (hS sk hsk).2) ?_
    intro k hk
    rw [runSkels_eq hrun]
    exact List.mem_map_of_mem (List.mem_range.mpr hk)
  · intro j
    fin_cases j
    exacts [hlen .xor, hlen .mulNative, hlen .setConstant, hlen .deref, hlen .jump, hlen .blake2s]

/-- **Constraint completeness**. A valid execution of
at most `2^maxLogRows` steps has a witness satisfying the constraint statement and representing
it: the rows of the run in the six tables, the image as the memory block and the program as the
bytecode block, with the counts that balance the buses (`constraintCompleteness_rows`, which also
gives the tables' row counts). -/
theorem constraintCompleteness {prog : Program} {input : PublicInput} {t : Trace prog}
    (h : ValidExecution prog input t) (hsteps : t.steps ≤ 2 ^ maxLogRows) :
    ∃ w, SatisfiedBy prog input w ∧ AssignmentRepresents w t := by
  obtain ⟨w, hw, hrep, -⟩ := constraintCompleteness_rows h
    fun op ↦ (t.runRows_le_steps h.2 op).trans hsteps
  exact ⟨w, hw, hrep⟩

end LeanVM.Arithmetization
