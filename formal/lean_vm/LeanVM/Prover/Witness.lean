/-
  LeanVM.Prover.Witness

  The executable witness of an execution is the specification's: `checkTrace` decides a valid
  execution within the cap, and `witness?` returns, from the same run, the announced sizes, every
  column of the instance and the stack of the specification witness, which is a child's witness
  (`ChildFor`).
-/

module

public import LeanVM.Prover.WitnessCols
public import LeanVM.Prover.WitnessStack
public import LeanVM.Guest.Child.Honest

/-!
# The witness of an execution

The specification prover runs at `traceWitness prog input t` (`skelWitness` of the run's
skeletons) and `traceSizes prog input t` (the sizes it carries, `witnessSizes`), with the stack
`stackOf prog s w`. The executable prover runs `witness?` (`Statement/Prover/Columns.lean`).

* `checkTrace_iff` (`WitnessRun.lean`): `checkTrace` is a valid execution whose committed size is
  at most `2^32`; `isSome_witness?_iff`: `witness?` returns exactly when it holds.
* `witness?_spec`: then `witness?` returns data meeting `WitnessSpec`: the row counts of
  `traceSizes`, the verifier's layout of them, every column at its verifier's number the instance's
  column of `stackOf` (the `KECCAK` output lanes included), the stack `stackOf`'s cells, and the
  announcement `announce`.
* `childFor_trace`: the specification witness at its sizes is a child's witness at every valid
  rate (`exists_childFor`, for the concrete witness).
-/

namespace LeanVM.Prover

open LeanVM.Parameters LeanVM.Semantics LeanVM.Arithmetization LeanVM.Extraction
open LeanVM.Protocol LeanVM.Protocol.LeanIsa LeanVM.Protocol.EndToEnd.Front
open LeanVM.Protocol.EndToEnd.Complete LeanVM.Protocol.Halting LeanVM.Protocol.Verifier
open LeanVM.Guest.Child
open Air.Flat (EnsembleWitness)

@[expose] public section

variable {prog : LeanIsaProgram} {input : PublicInput} {t : Execution prog}

/-! ## The specification witness is a child's -/

/-- The run's skeletons are sound. -/
theorem skelOk_runSkels (hv : ValidExecution prog input t) :
    ∀ sk ∈ t.runSkels, SkelOk prog t.memory sk := by
  intro sk hsk
  rw [runSkels_eq hv.2] at hsk
  obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hsk
  exact skAt_ok hv.2 (List.mem_range.mp hk)

/-- The specification witness's opcode tables hold the run's rows. -/
theorem length_traceWitness (hb : TraceBounds t) (j : Fin 6) :
    (tableAt (traceWitness prog input t) ⟨j, by omega⟩).table.length =
      Skel.count (tableOpcode j) t.runSkels := by
  rw [traceWitness_eq hb, tableAt_skelWitness, opRows, List.length_map, skelRows,
    length_filter_mkRows]

/-- The specification witness carries its sizes. -/
theorem ofWitness_traceWitness (hv : ValidExecution prog input t) (hb : TraceBounds t) :
    Sizes.ofWitness (traceWitness prog input t) = some (traceSizes prog input t) := by
  rw [traceSizes_eq hv hb]
  unfold Sizes.ofWitness
  simp only [traceWitness_pos hv hb, dite_true]
  rfl

/-- **The specification witness is a child's witness**, for a valid execution within the cap and
a valid rate: `exists_childFor`, for the concrete witness. -/
theorem childFor_trace (hv : ValidExecution prog input t)
    (hbudget : t.committedSize ≤ 2 ^ 32) {ρ : ℕ} (hρ : validRate ρ) :
    ChildFor prog input t ρ (traceWitness prog input t) (traceSizes prog input t) := by
  have hb : TraceBounds t := traceBounds_of hv hbudget
  have hcount : ∀ op, t.opcodeCount op = t.runRows op := Execution.count_eq_runRows hv.2
  have hheight : ∀ op, 2 ^ Nat.clog 2 (t.opcodeCount op) ≤ t.committedSize := by
    intro op
    have : 0 < 2 ^ prog.logSize := Nat.two_pow_pos _
    have hk : 2 ^ Nat.clog 2 (t.opcodeCount .keccak) ≤ 2 ^ max (Nat.clog 2 (t.opcodeCount
        .keccak)) 9 :=
      Nat.pow_le_pow_right (by norm_num) (le_max_left _ _)
    simp only [Execution.committedSize]
    cases op <;> omega
  have hcap : (2 : ℕ) ^ 32 ≤ 2 ^ maxLogRows := Nat.pow_le_pow_right (by norm_num) (by decide)
  have hrows : ∀ op, t.runRows op ≤ 2 ^ maxLogRows := fun op ↦ by
    rw [← hcount]
    exact (Nat.le_pow_clog (by norm_num) _).trans (((hheight op).trans hbudget).trans hcap)
  obtain ⟨⟨hmin, hκ, hw0, hw1⟩, hrun⟩ := hv
  have hS := skelOk_runSkels (input := input) ⟨⟨hmin, hκ, hw0, hw1⟩, hrun⟩
  have hw : SatisfiedBy prog input (traceWitness prog input t) := by
    rw [traceWitness_eq hb]
    exact skelWitness_satisfiedBy prog input t.memory _ hmin hκ hS (runSkels_state_perm hrun)
      hb.2 hw0 hw1
  have hrep : AssignmentRepresents (traceWitness prog input t) t := by
    rw [traceWitness_eq hb]
    refine skelWitness_represents prog input hκ hrun _ hb.2 (fun sk hsk ↦ (hS sk hsk).2) ?_
    intro k hk
    rw [runSkels_eq hrun]
    exact List.mem_map_of_mem (List.mem_range.mpr hk)
  have hv : ValidExecution prog input t := ⟨⟨hmin, hκ, hw0, hw1⟩, hrun⟩
  have hs0 := ofWitness_traceWitness hv hb
  rw [traceSizes_eq hv hb] at hs0 ⊢
  have hmem : (witnessSizes (traceWitness prog input t) (traceWitness_pos hv hb)).logMem = t.logMemorySize :=
    hrep.κ_eq
  have hr : ∀ j : Fin 6,
      (witnessSizes (traceWitness prog input t) (traceWitness_pos hv hb)).rows j =
        t.opcodeCount (tableOpcode j) :=
    fun j ↦ (length_traceWitness hb j).trans ((t.count_runSkels _).trans (hcount _).symm)
  have htotal : (LeanIsa.blocks prog
      (witnessSizes (traceWitness prog input t) (traceWitness_pos hv hb))).total =
      t.committedSize := by
    have e : tableOpcode 0 = .xor ∧ tableOpcode 1 = .mulNative ∧ tableOpcode 2 = .setConstant ∧
        tableOpcode 3 = .deref ∧ tableOpcode 4 = .jump ∧ tableOpcode 5 = .keccak := by decide
    rw [blocks_total_eq, hmem, pow_add 2 _ 6]
    simp only [Sizes.τ, hr, e, Execution.committedSize]
    have f0 : tableLogFloors.getD ((0 : Fin 6) : ℕ) 0 = 0 := rfl
    have f1 : tableLogFloors.getD ((1 : Fin 6) : ℕ) 0 = 0 := rfl
    have f2 : tableLogFloors.getD ((2 : Fin 6) : ℕ) 0 = 0 := rfl
    have f3 : tableLogFloors.getD ((3 : Fin 6) : ℕ) 0 = 0 := rfl
    have f4 : tableLogFloors.getD ((4 : Fin 6) : ℕ) 0 = 0 := rfl
    have f5 : tableLogFloors.getD ((5 : Fin 6) : ℕ) 0 = 9 := rfl
    simp only [f0, f1, f2, f3, f4, f5, Nat.max_zero]
    ring
  refine ⟨⟨hρ, hw, hs0, ⟨?_, ?_, fun j ↦ (hr j).trans_le (by rw [hcount]; exact hrows _),
    leanIsaμ_le_of_total_le (htotal ▸ hbudget)⟩, hrep⟩, htotal⟩
  · rw [hmem]
    exact hmin
  · rw [hmem]
    exact hκ

/-! ## The executable data -/

/-- **What the executable data of an execution is**: the row counts of the specification
witness (`traceSizes`), the verifier's layout of its sizes, every column of the instance read off
its stack by the verifier's column number, the stack's cells, and the announcement. -/
structure WitnessSpec (prog : LeanIsaProgram) (input : PublicInput) (t : Execution prog)
    (W : Witness) : Prop where
  /-- The six row counts. -/
  rows : W.rows = List.ofFn (traceSizes prog input t).rows
  /-- The verifier's layout. -/
  layout : W.layout = verifierLayout prog (traceSizes prog input t)
  /-- Every column, the `KECCAK` output lanes included. -/
  cols : ∀ c : Col, W.cols.getD (refCol c) #[] =
    ((inst prog (traceSizes prog input t)).column
      (stackOf prog (traceSizes prog input t) (traceWitness prog input t)) c).values.toArray
  /-- The stack. -/
  stack : W.stack =
    (stackOf prog (traceSizes prog input t) (traceWitness prog input t)).values.toArray
  /-- The announced sizes and rate. -/
  announce : ∀ ρ, W.announce ρ = LeanVM.Protocol.EndToEnd.Front.announce (traceSizes prog input t) ρ

/-- The fields of the data built at a layout. -/
theorem buildWitness_fields {κ : ℕ} (img : MemoryImage κ) (acc : Rows) (layout : Layout) :
    (buildWitness img acc layout).layout = layout ∧
      (buildWitness img acc layout).cols = colsOf img acc layout.tableLogHeights ∧
      (buildWitness img acc layout).stack =
        stackArray layout (colsOf img acc layout.tableLogHeights) :=
  ⟨rfl, by simp only [buildWitness], by simp only [buildWitness]⟩

/-- The verifier's layout's log-heights are the tables'. -/
theorem verifierLayout_tableLogHeights (s : Sizes) :
    (verifierLayout prog s).tableLogHeights = tableLogs s := rfl

/-- **The data built from a valid run at the verifier's layout is the specification's.** -/
theorem buildWitness_spec (hv : ValidExecution prog input t) (hcap : t.committedSize ≤ 2 ^ 32) :
    WitnessSpec prog input t
      (buildWitness t.memory (traceRows t) (verifierLayout prog (traceSizes prog input t))) := by
  have hb := traceBounds_of hv hcap
  obtain ⟨hL, hC, hS⟩ := buildWitness_fields t.memory (traceRows t)
    (verifierLayout prog (traceSizes prog input t))
  rw [verifierLayout_tableLogHeights] at hC hS
  have hsize :
      (colsOf t.memory (traceRows t) (tableLogs (traceSizes prog input t))).size = 165 := by
    unfold colsOf; exact Array.size_ofFn
  refine ⟨rowsList_trace hv hb, hL, fun c ↦ by rw [hC]; exact cols_trace hv hb c, ?_, fun ρ ↦ ?_⟩
  · rw [hS]
    refine stackArray_eq prog _ _ _ hsize (cols_trace hv hb) fun x hx h ↦ ?_
    exact Blocks.stackAt_getElem_of_total_le _ _ _ hx h
  · show (((traceSizes prog input t).logMem :: (traceRows t).tabs.toList.map (·.size)) ++
      [ρ]).map eOfNat = _
    rw [rowsList_trace hv hb]
    rfl

/-- The verifier's layout of a valid execution's sizes within the cap is built. -/
theorem buildLayout_trace (hv : ValidExecution prog input t) (hcap : t.committedSize ≤ 2 ^ 32) :
    buildLayout (bytecodeWords prog) t.logMemorySize ((traceRows t).tabs.toList.map (·.size)) =
      some (verifierLayout prog (traceSizes prog input t)) := by
  obtain ⟨⟨-, -, -, hadm, -⟩, -⟩ := childFor_trace hv hcap (ρ := 1) ⟨le_rfl, by decide⟩
  have hb := traceBounds_of hv hcap
  rw [← logMem_trace hv hb, rowsList_trace hv hb]
  have e := buildLayout_eq prog (traceSizes prog input t)
  rw [tableRows] at e
  have hok : LayoutOk (traceSizes prog input t) := ⟨hadm.1, hadm.2.1, hadm.2.2.1⟩
  simp only [e, hok, ↓reduceIte]

/-- **The executable witness of a valid execution within the cap** is built from its run, at the
verifier's layout. -/
theorem witness?_eq (hv : ValidExecution prog input t) (hcap : t.committedSize ≤ 2 ^ 32) :
    witness? prog input t =
      some (buildWitness t.memory (traceRows t) (verifierLayout prog (traceSizes prog input t))) := by
  unfold witness?
  rw [ite_eq_left ((boundaryOK_iff input t).mpr hv.1)]
  simp only
  rw [runSteps_eq t (κ_lt_of_valid hv), ite_eq_left hv.2]
  simp only
  rw [committedSizeOf_eq t (opCount_traceSteps hv.2), ite_eq_left (show _ ≤ maxCommitted from hcap)]
  exact congrArg (Option.map _) (buildLayout_trace hv hcap)

/-- **The executable witness** of a valid execution within the cap meets `WitnessSpec`. -/
theorem witness?_spec (hv : ValidExecution prog input t) (hcap : t.committedSize ≤ 2 ^ 32) :
    ∃ W, witness? prog input t = some W ∧ WitnessSpec prog input t W :=
  ⟨_, witness?_eq hv hcap, buildWitness_spec hv hcap⟩

/-- `witness?` returns only where `checkTrace` holds. -/
theorem checkTrace_of_isSome (h : (witness? prog input t).isSome = true) :
    checkTrace prog input t = true := by
  unfold witness? at h
  unfold checkTrace
  by_cases hb : boundaryOK input t = true
  · simp only [hb, Bool.true_and, ↓reduceIte] at h ⊢
    cases hr : runSteps (powIndex t.logMemorySize) (powIndex prog.logSize) prog t with
    | none => simp [hr] at h
    | some steps =>
      by_cases hc : committedSizeOf prog.logSize t.logMemorySize (opCount steps) ≤ maxCommitted
      · simp [hc]
      · simp [hr, hc] at h
  · simp [hb] at h

/-- `witness?` returns exactly on a valid execution within the cap. -/
theorem isSome_witness?_iff (prog : LeanIsaProgram) (input : PublicInput) (t : Execution prog) :
    (witness? prog input t).isSome = true ↔
      ValidExecution prog input t ∧ t.committedSize ≤ 2 ^ 32 :=
  ⟨fun h ↦ (checkTrace_iff input t).mp (checkTrace_of_isSome h),
    fun ⟨hv, hcap⟩ ↦ by rw [witness?_eq hv hcap]; rfl⟩

end

end LeanVM.Prover
