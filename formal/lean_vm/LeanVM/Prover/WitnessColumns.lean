/-
  LeanVM.Prover.WitnessColumns

  The executable columns of a valid execution are the instance's columns of the stack of its
  specification witness, every one of them, the `KECCAK` output lanes included.
-/

module

public import LeanVM.Prover.WitnessRows
public import LeanVM.Prover.WitnessSpec
public import LeanVM.Protocol.EndToEnd.Front.LayoutInstance

/-!
# The columns of an execution

`traceWitness prog input t` is the specification's witness of an execution (`skelWitness` of its
run's skeletons, the witness `exists_childFor` builds), `traceSizes` the sizes it carries, and
`traceRows t` the executable pass over the run's steps. On a valid execution:

* the pass's tables are the witness's opcode tables, row for row (`tabs_trace`), its counters the
  memory and bytecode blocks' finalize counts;
* the sizes are the trace's memory log-size and the pass's row counts (`logMem_trace`,
  `rows_trace`);
* **every column** (`cols_trace`): `colsOf` at the verifier's number of an instance column is that
  column of the stack of the witness, the `KECCAK` output lanes the instance's derived columns.
-/

namespace LeanVM.Prover

open LeanVM.Parameters LeanVM.Semantics LeanVM.Arithmetization LeanVM.Extraction
open LeanVM.Protocol LeanVM.Protocol.LeanIsa LeanVM.Protocol.EndToEnd.Front
open LeanVM.Protocol.EndToEnd.Complete LeanVM.Protocol.Halting
open Air.Flat (EnsembleWitness)

@[expose] public section

variable {prog : LeanIsaProgram} {input : PublicInput} {t : Execution prog}

/-! ## The specification's witness and the executable pass -/

/-- What `skelWitness` needs of an execution: its memory within the address space and every
opcode's rows within the rows' cap (Clean's tables hold at most `2^64` rows). A valid execution
within the committed-size cap has them (`traceBounds_of`). -/
def TraceBounds (t : Execution prog) : Prop :=
  t.logMemorySize ≤ maxLogMem ∧ ∀ op, Skel.count op t.runSkels ≤ 2 ^ maxLogRows

/-- A valid execution within the committed-size cap is within `skelWitness`'s bounds. -/
theorem traceBounds_of (hv : ValidExecution prog input t) (hcap : t.committedSize ≤ 2 ^ 28) :
    TraceBounds t := by
  refine ⟨hv.1.2.1, fun op ↦ ?_⟩
  have hcount : ∀ op, t.opcodeCount op = t.runRows op := Execution.count_eq_runRows hv.2
  have hheight : 2 ^ Nat.clog 2 (t.opcodeCount op) ≤ t.committedSize := by
    have : 0 < 2 ^ prog.logSize := Nat.two_pow_pos _
    have hk : 2 ^ Nat.clog 2 (t.opcodeCount .keccak) ≤ 2 ^ max (Nat.clog 2 (t.opcodeCount
        .keccak)) 9 :=
      Nat.pow_le_pow_right (by norm_num) (le_max_left _ _)
    simp only [Execution.committedSize]
    cases op <;> omega
  have h28 : (2 : ℕ) ^ 28 ≤ 2 ^ maxLogRows := Nat.pow_le_pow_right (by norm_num) (by decide)
  rw [Execution.count_runSkels, ← hcount]
  exact (Nat.le_pow_clog (by norm_num) _).trans ((hheight.trans hcap).trans h28)

/-- Some witness at every memory log-size: `skelWitness` of no skeletons within the address
space, `witnessOf` past it. `traceWitness`'s value off `TraceBounds`, where nothing reads it. -/
theorem nonempty_witness (prog : LeanIsaProgram) (κ : ℕ) :
    Nonempty (EnsembleWitness (leanIsaEnsemble prog κ)) := by
  by_cases hκ : κ ≤ maxLogMem
  · exact ⟨skelWitness prog ⟨fun _ ↦ 0⟩ (fun _ ↦ 0) [] hκ fun op ↦ by
      simp [Skel.count, Skel.onTable]⟩
  · exact ⟨witnessOf prog ⟨κ, by unfold maxLogMem at hκ; omega, fun _ ↦ 0⟩
      ⟨(Vector.replicate _ 0 : Vector K _)⟩⟩

open Classical in
/-- **The specification's witness of an execution**: the rows of its run's skeletons, its image,
the program (`skelWitness`; the witness of `exists_childFor`), at the execution's memory
log-size, within `skelWitness`'s bounds (`TraceBounds`; any witness off them). -/
noncomputable def traceWitness (prog : LeanIsaProgram) (input : PublicInput) (t : Execution prog) :
    EnsembleWitness (leanIsaEnsemble prog t.logMemorySize) :=
  if h : TraceBounds t then skelWitness prog input t.memory t.runSkels h.1 h.2
  else Classical.choice (nonempty_witness prog _)

/-- Within the bounds, the specification's witness is `skelWitness` of the run's skeletons. -/
theorem traceWitness_eq (h : TraceBounds t) :
    traceWitness prog input t = skelWitness prog input t.memory t.runSkels h.1 h.2 := by
  unfold traceWitness
  rw [dite_eq_left h]

/-- The executable pass over the steps of an execution's run. -/
noncomputable def traceRows (t : Execution prog) : Rows :=
  rowsOf (powIndex t.logMemorySize) t.memory prog.logSize (traceSteps t).toArray

/-- A valid execution's memory is within `addressIndex?`'s address space. -/
theorem κ_lt_of_valid (hv : ValidExecution prog input t) : t.logMemorySize < 64 := by
  have := hv.1.2.1; unfold maxLogMem at this; omega

/-- The pass over a valid run keeps the invariant at the run's skeletons. -/
theorem rowsInv_trace (hv : ValidExecution prog input t) :
    RowsInv t.memory prog.logSize (traceRows t) t.runSkels := by
  have := rowsInv_rowsOf (κ_lt_of_valid hv) t.memory (traceSteps t) (stepOk_traceSteps hv.2)
  rwa [runSkels_eq_steps hv.2] at this

/-- The rows of the opcode tables of `skelWitness`. -/
theorem tableAt_skelWitness {κ : ℕ} (img : MemoryImage κ) (S : List Skel) (hκ : κ ≤ maxLogMem)
    (hrows : ∀ op, Skel.count op S ≤ 2 ^ maxLogRows) (j : Fin 6) :
    (tableAt (skelWitness prog input img S hκ hrows) ⟨j, by omega⟩).table =
      Arithmetization.opRows img (skelRows img S) (tableOpcode j) := by
  rw [skelWitness_tableAt_table]
  fin_cases j <;> rfl

/-- The table of the opcode of table `j` is `j`. -/
theorem tableOf_tableOpcode (j : Fin 6) : opTableIdx (tableOpcode j) = j := by
  fin_cases j <;> rfl

/-- **The pass's tables are the witness's opcode tables.** -/
theorem tabs_trace (hv : ValidExecution prog input t) (hb : TraceBounds t) (j : Fin 6) :
    ((traceRows t).tabs.getD j #[]).toList =
      (tableAt (traceWitness prog input t) ⟨j, by omega⟩).table := by
  have h := (rowsInv_trace hv).tabs (tableOpcode j)
  rw [tableOf_tableOpcode] at h
  rw [h, traceWitness_eq hb, tableAt_skelWitness]
  rfl

/-! ## The sizes -/

/-- The witness's memory log-size is the trace's. -/
theorem traceWitness_logSize (hb : TraceBounds t) :
    (imageOf (traceWitness prog input t).data).1 = t.logMemorySize := by
  rw [traceWitness_eq hb, imageOf_skelWitness]

/-- The witness has at least two memory cells. -/
theorem traceWitness_pos (hv : ValidExecution prog input t) (hb : TraceBounds t) :
    0 < (imageOf (traceWitness prog input t).data).1 := by
  rw [traceWitness_logSize hb]
  have := hv.1.1
  unfold minLogMem at this
  omega

/-- **The sizes of an execution**: those its specification witness carries (`witnessSizes`); a
placeholder when it carries none (never, on a valid execution). -/
noncomputable def traceSizes (prog : LeanIsaProgram) (input : PublicInput) (t : Execution prog) :
    Sizes :=
  if h : 0 < (imageOf (traceWitness prog input t).data).1 then
    witnessSizes (traceWitness prog input t) h
  else ⟨1, Nat.one_pos, fun _ ↦ 0⟩

theorem traceSizes_eq (hv : ValidExecution prog input t) (hb : TraceBounds t) :
    traceSizes prog input t =
      witnessSizes (traceWitness prog input t) (traceWitness_pos hv hb) := by
  unfold traceSizes
  rw [dite_eq_left (traceWitness_pos hv hb)]

/-- The memory log-size is the trace's. -/
theorem logMem_trace (hv : ValidExecution prog input t) (hb : TraceBounds t) :
    (traceSizes prog input t).logMem = t.logMemorySize := by
  rw [traceSizes_eq hv hb]
  exact traceWitness_logSize hb

/-- The row counts are the pass's tables' sizes. -/
theorem rows_trace (hv : ValidExecution prog input t) (hb : TraceBounds t) (j : Fin 6) :
    (traceSizes prog input t).rows j = ((traceRows t).tabs.getD j #[]).size := by
  rw [traceSizes_eq hv hb, ← Array.length_toList, tabs_trace hv hb j]
  rfl

/-- The pass's row counts, as a list, are the sizes'. -/
theorem rowsList_trace (hv : ValidExecution prog input t) (hb : TraceBounds t) :
    (traceRows t).tabs.toList.map (·.size) = List.ofFn (traceSizes prog input t).rows := by
  have h6 := (rowsInv_trace hv).tabs_size
  apply List.ext_getElem (by simp [h6])
  intro i h1 h2
  have hi : i < 6 := by simpa [h6] using h1
  rw [List.getElem_map, List.getElem_ofFn, rows_trace hv hb ⟨i, hi⟩, Array.getElem_toList]
  simp [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem (h6 ▸ hi)]

/-! ## Cells -/

/-- A table read through the pass is the witness's table. -/
theorem cellAt_eq {R : Array (Array K)} {T : Air.Flat.Table K} (h : R.toList = T.table) (x i : ℕ) :
    cellAt R x i = cellOf T x i := by
  unfold cellAt cellOf
  rw [← h, Array.getElem?_toList]

/-- The twelve-round states of the pass. -/
theorem midStates_getD (R : Array (Array K)) (h x : ℕ) (hx : x < 2 ^ h) :
    (midStates R h).getD x zeroState =
      keccakSegment 0 (laneState fun l : Fin 25 ↦ cellAt R x (15 + l.val)) := by
  simp only [midStates, Array.getD_eq_getD_getElem?, Array.getElem?_ofFn, hx, dite_true,
    Option.getD_some]
  split_ifs with hr
  · rfl
  · have hz : (fun l : Fin 25 ↦ cellAt R x (15 + l.val)) = fun _ ↦ 0 := funext fun l ↦ by
      simp [cellAt, Array.getElem?_eq_none (Nat.not_lt.mp hr)]
    rw [hz, laneState_zero]
    rfl

/-- The twenty-four-round states of the pass. -/
theorem outStates_getD (R : Array (Array K)) (h x : ℕ) (hx : x < 2 ^ h) :
    (outStates R (midStates R h)).getD x zeroState =
      keccakSegment 1 (keccakSegment 0 (laneState fun l : Fin 25 ↦ cellAt R x (15 + l.val))) := by
  have hm := midStates_getD R h x hx
  have hsize : (midStates R h).size = 2 ^ h := by simp [midStates]
  have hx' : x < (midStates R h).size := by rw [hsize]; exact hx
  have hm' : (midStates R h)[x]'hx' =
      keccakSegment 0 (laneState fun l : Fin 25 ↦ cellAt R x (15 + l.val)) := by
    rw [← hm, Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hx', Option.getD_some]
  simp only [outStates, Array.getD_eq_getD_getElem?, Array.getElem?_ofFn, hx', dite_true,
    Option.getD_some, Fin.getElem_fin]
  split_ifs with hr
  · rw [hm']
    rfl
  · have hz : (fun l : Fin 25 ↦ cellAt R x (15 + l.val)) = fun _ ↦ 0 := funext fun l ↦ by
      simp [cellAt, Array.getElem?_eq_none (Nat.not_lt.mp hr)]
    rw [hz, laneState_zero]
    rfl

/-- The memory block's cells. -/
theorem memCell_trace (hb : TraceBounds t) (x : ℕ) (hx : x < 2 ^ t.logMemorySize) (k : ℕ) :
    cellOf (tableAt (traceWitness prog input t) 6) x k =
      (#[(t.memory ⟨x, hx⟩).limb 0, (t.memory ⟨x, hx⟩).limb 1, addressOfIndex x,
        g ^ skelMemFin t.memory t.runSkels (addressOfIndex x)][k]?).getD 0 := by
  rw [cellOf, traceWitness_eq hb, skelWitness_tableAt_table]
  show ((List.ofFn fun i : Fin (2 ^ t.logMemorySize) ↦ rawRow (memRowOf t.memory i
    (g ^ skelMemFin t.memory t.runSkels (addressOfIndex i))))[x]?.bind (·[k]?)).getD 0 = _
  rw [List.getElem?_ofFn]
  simp [hx, rawRow, memRow_toArray, memRowOf]

/-- The bytecode block's finalize counts. -/
theorem bcCell_trace (hb : TraceBounds t) (x : ℕ) (hx : x < 2 ^ prog.logSize) :
    cellOf (tableAt (traceWitness prog input t) 7) x 1 = g ^ skelBcFin t.runSkels (addressOfIndex
        x) := by
  rw [cellOf, traceWitness_eq hb, skelWitness_tableAt_table]
  show ((List.ofFn fun i : Fin (2 ^ prog.logSize) ↦ rawRow (bytecodeRowOf prog i
    (g ^ skelBcFin t.runSkels (addressOfIndex i))))[x]?.bind (·[1]?)).getD 0 = _
  rw [List.getElem?_ofFn]
  simp [hx, rawRow, bytecodeRow_toArray, bytecodeRowOf]

end

end LeanVM.Prover
