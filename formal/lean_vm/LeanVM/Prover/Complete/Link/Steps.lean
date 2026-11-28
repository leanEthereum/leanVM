/-
  LeanVM.Prover.Complete.Link.Steps

  The honest witness's rows as the run's steps.
-/

module

public import LeanVM.Prover.Complete.Link.OneHot
public import LeanVM.Prover.Complete.Witness
public import LeanVM.Protocol.Relation.Link.Steps
public import LeanVM.Prover.Complete.Link.RowShape
public import LeanVM.Prover.Complete.StackLayout
import LeanVM.Semantics.Lemmas

/-!
# The rows are the run's steps

`witness?` (`Statement/Prover/Witness.lean`, `Columns.lean`) runs the trace (`traceSteps`, its
`k`-th step stepped from the run's `k`-th state) and fills each table with the rows of the steps of
its opcode, in order (`rowsOf`). So:

* `rowsOf_getD`: table `t`'s rows are `rowOf` of its steps `tablePairs L t` (a step and its cycle);
  `rowCounts_getD`: their number;
* `rowValue_witness`: on an executed row `u` of table `t`, the witness's columns (`rowValue`) are
  `rowOf`'s of the step `(tablePairs L t)[u]`;
* `rowOf_state`: `rowOf` puts `pc` and `fp` at columns `0` and `1`, the cycle pointer
  `K.ofBits (encode cycle)` at the state link's `cycle` column and the program pointer
  `K.ofBits (encode slot)` at the program link's `pointer` column; `cycle_oneHot`,
  `bytecode_oneHot`: those columns are one-hot (`OneHotWords`);
* `sum_tablePairs`: a sum over every table's executed rows is a sum over the steps;
* `step_succ`: the step `k < T` is stepped from the run's state `k` and executes to state `k + 1`.
-/

@[expose] public section

namespace LeanVM.Prover.Complete

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol.Verifier LeanVM.Prover LeanVM.Extraction
open Finset

/-! ## A table's steps -/

/-- The steps of table `t`, each with its cycle, in the order they ran. -/
def tablePairs (L : List Step) (t : ℕ) : List (Step × ℕ) :=
  L.zipIdx.filter fun p ↦ decide (opTableIdx p.1.ins.opcode = t)

theorem rowsOf_foldl {κ : ℕ} (ctx : FillCtx κ) {t : ℕ} (ht : t < nTables) :
    ∀ (P : List (Step × ℕ)) (tabs : Array (Array (Array K))), tabs.size = nTables →
      (P.foldl (fun tabs (p : Step × ℕ) ↦
          tabs.modify (opTableIdx p.1.ins.opcode) (·.push (rowOf ctx p.2 p.1))) tabs).getD t #[] =
        tabs.getD t #[] ++ ((P.filter fun p ↦ decide (opTableIdx p.1.ins.opcode = t)).map
          fun p ↦ rowOf ctx p.2 p.1).toArray
  | [], tabs, _ => by simp
  | p :: P, tabs, hs => by
    rw [List.foldl_cons, rowsOf_foldl ctx ht P _ (by simp [hs]), List.filter_cons]
    by_cases hp : opTableIdx p.1.ins.opcode = t
    · rw [hp, Keccak.getD_modify_self, ite_eq_left (by omega)]
      simp
    · rw [Keccak.getD_modify_of_ne _ hp]
      simp [hp]

/-- **Table `t`'s rows** are `rowOf` of its steps. -/
theorem rowsOf_getD {κ : ℕ} (ctx : FillCtx κ) (L : List Step) {t : ℕ} (ht : t < nTables) :
    (rowsOf ctx L.toArray).getD t #[] = ((tablePairs L t).map fun p ↦ rowOf ctx p.2 p.1).toArray := by
  unfold rowsOf
  rw [← Array.foldl_toList, Array.toList_zipIdx, List.toList_toArray, rowsOf_foldl ctx ht _ _ (by simp)]
  simp [Array.getD_eq_getD_getElem?, ht, tablePairs]

theorem length_tablePairs (L : List Step) (t : ℕ) :
    (tablePairs L t).length = L.countP fun st ↦ decide (opTableIdx st.ins.opcode = t) := by
  rw [tablePairs, ← List.countP_eq_length_filter]
  have : L.zipIdx.map Prod.fst = L := by simp
  conv_rhs => rw [← this]
  rw [List.countP_map]
  rfl

/-- **Table `t`'s row count** is its number of steps. -/
theorem rowCounts_getD (L : List Step) {t : ℕ} (ht : t < nTables) :
    (rowCounts L.toArray).getD t 0 = (tablePairs L t).length := by
  rw [length_tablePairs]
  simp [rowCounts, ht, List.countP_toArray]

/-! ## A row's state and pointers -/

/-- **What `rowOf` writes**: as many columns as its table has, `pc` and `fp` at columns `0` and
`1`, the cycle pointer at the state link's `cycle` column and the program pointer at the program
link's `pointer` column. -/
theorem rowOf_state {κ : ℕ} (ctx : FillCtx κ) (k : ℕ) (st : Step) :
    (rowOf ctx k st).size = tableWidths.getD (opTableIdx st.ins.opcode) 0 ∧
      (rowOf ctx k st).getD 0 0 = st.pc ∧ (rowOf ctx k st).getD 1 0 = st.fp ∧
      (rowOf ctx k st).getD
        (tables.getD (opTableIdx st.ins.opcode) default).links.stateLink.cycle 0 = ctx.ptr k ∧
      (rowOf ctx k st).getD
        (tables.getD (opTableIdx st.ins.opcode) default).links.bytecodeLink.pointer 0 =
          ctx.ptr st.slot := by
  rcases st with ⟨pc, fp, slot, ins⟩
  cases ins
  case keccak om otail ob8 ocap oout inOdd outOdd outCells =>
    have hc : (tables.getD opKeccak default).links.stateLink.cycle = 67 := by decide +kernel
    have hb : (tables.getD opKeccak default).links.bytecodeLink.pointer = 66 := by decide +kernel
    have hw : tableWidths.getD opKeccak 0 = 68 := by decide +kernel
    simp only [opTableIdx, LeanIsaInstruction.opcode, hc, hb, hw]
    refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
      simp only [rowOf, Array.getD_eq_getD_getElem?, Array.getElem?_append, Array.size_append,
        Array.size_ofFn, List.size_toArray, List.length_map, List.length_cons, List.length_nil] <;>
      simp
  all_goals exact ⟨rfl, rfl, rfl, rfl, rfl⟩

/-! ## The honest witness -/

/-- What the honest witness's rows are filled with. -/
def fillCtx {prog : LeanIsaProgram} (ex : Execution prog) (W : Witness) :
    FillCtx ex.logMemorySize :=
  ⟨powIndex ex.logMemorySize, ex.memory, W.chunks⟩

theorem logMemorySize_lt {prog : LeanIsaProgram} {input : PublicInput} {ex : Execution prog}
    (hv : ValidExecution prog input ex) : ex.logMemorySize < 64 := by
  have := hv.1.2.1; unfold maxLogMem at this; omega

/-- **The honest witness from a valid execution**: its rows are its trace's steps'. -/
theorem witness_steps {prog : LeanIsaProgram} {input : PublicInput} {ex : Execution prog}
    {W : Witness} (hW : witness? prog input ex = some W) (hv : ValidExecution prog input ex) :
    W.rows = rowCounts (traceSteps ex).toArray ∧
      W.cols = colsOf ex.memory (rowsOf (fillCtx ex W) (traceSteps ex).toArray)
        W.layout.tableLogHeights ∧
      buildLayout (bytecodeWords prog) ex.logMemorySize W.rows = some W.layout ∧
      Chunks.new (pointerWidth ex.logMemorySize prog.logSize W.rows.sum) = some W.chunks := by
  obtain ⟨-, steps, hs, hr, hl, -, hc, hcols, -⟩ := witness?_spec hW
  rw [runSteps_eq ex (logMemorySize_lt hv) hv.2, Option.some.injEq] at hs
  subst hs
  exact ⟨hr, hcols, hl, hc⟩

/-- `buildLayout`'s heights hold its rows. -/
theorem rows_le_height {bytecode : List K} {logMemory : ℕ} {rows : List ℕ} {layout : Layout}
    (h : buildLayout bytecode logMemory rows = some layout) {t : ℕ} (ht : t < nTables) :
    rows.getD t 0 ≤ 2 ^ layout.tableLogHeights.getD t 0 := by
  obtain ⟨-, -, hlen, -⟩ := buildLayout_spec h
  unfold buildLayout at h
  split at h
  · cases h
  · split at h
    · simp only [Option.some.injEq] at h
      subst h
      exact LeanVM.Protocol.Relation.le_two_pow_zipWith _ _ t (by rw [hlen]; exact ht)
        (by rw [show tableLogFloors.length = nTables from rfl]; exact ht)
    · cases h

/-- `buildLayout` at a program's bytecode: the program's log-size. -/
theorem logBytecode_witness {prog : LeanIsaProgram} {logMemory : ℕ} {rows : List ℕ}
    {layout : Layout} (h : buildLayout (bytecodeWords prog) logMemory rows = some layout) :
    layout.logBytecode = prog.logSize := by
  have hlen : (bytecodeWords prog).length = 2 ^ (prog.logSize + bytecodeSlotBits) := by
    rw [LeanVM.Rpm.bytecodeWords_length, pow_add, mul_comm]; rfl
  unfold buildLayout at h
  rw [hlen, log2Strict_two_pow] at h
  simp only at h
  split at h
  · simp only [Option.some.injEq] at h
    subst h
    simp
  · cases h

theorem opTableIdx_lt (o : Opcode) : opTableIdx o < nTables := by cases o <;> decide

theorem mem_tablePairs {L : List Step} {t : ℕ} {p : Step × ℕ} (hp : p ∈ tablePairs L t) :
    opTableIdx p.1.ins.opcode = t := by
  simpa [tablePairs] using (List.mem_filter.mp hp).2

/-- **An executed row's columns are its step's `rowOf`.** -/
theorem rowValue_witness {prog : LeanIsaProgram} {input : PublicInput} {ex : Execution prog}
    {W : Witness} (hW : witness? prog input ex = some W) (hv : ValidExecution prog input ex)
    {t u : ℕ} (ht : t < nTables) (hu : u < (tablePairs (traceSteps ex) t).length) :
    rowValue (W.tableCols t) u = fun c ↦ ofK ((rowOf (fillCtx ex W)
      (tablePairs (traceSteps ex) t)[u].2 (tablePairs (traceSteps ex) t)[u].1).getD c 0) := by
  obtain ⟨hr, hcols, hl, -⟩ := witness_steps hW hv
  set p := (tablePairs (traceSteps ex) t)[u]
  have hpt : opTableIdx p.1.ins.opcode = t := mem_tablePairs (List.getElem_mem hu)
  have hsize := (rowOf_state (fillCtx ex W) p.2 p.1).1
  rw [hpt] at hsize
  have hcsize : W.cols.size = nColumns := by rw [hcols]; simp [colsOf]
  funext c
  unfold rowValue
  congr 1
  by_cases hc : c < tableWidths.getD t 0
  · obtain ⟨h1, h2, h3⟩ := tableOf_base t ht c hc
    have hlt : c < min (globalColumnBases.getD t 0 + tableWidths.getD t 0) W.cols.size -
        globalColumnBases.getD t 0 := by rw [hcsize]; omega
    have htc : (W.tableCols t).getD c #[] = W.cols.getD (globalColumnBases.getD t 0 + c) #[] := by
      simp only [Witness.tableCols, Array.getD_eq_getD_getElem?, Array.getElem?_extract, hlt,
        ↓reduceIte]
    rw [htc, hcols, colsOf_getD _ _ _ (by rw [← nColumns_eq]; exact h3)]
    have hm0 : globalColumnBases.getD t 0 + c ≠ memory0 := by unfold memory0; omega
    have hm1 : globalColumnBases.getD t 0 + c ≠ memory1 := by unfold memory1; omega
    have hq : globalColumnBases.getD t 0 + c ≠ qkeccak := by unfold qkeccak; omega
    have hheight := rows_le_height hl ht
    rw [hr, rowCounts_getD _ ht] at hheight
    simp only [hm0, hm1, hq, ↓reduceIte, h1, Nat.add_sub_cancel_left]
    rw [Keccak.tableColumn_getD _ _ _ _ (by omega), rowsOf_getD _ _ ht]
    simp [hu, cellAt, p]
  · have hnone : (W.tableCols t)[c]? = none := by
      simp only [Witness.tableCols, Array.getElem?_extract]
      rw [ite_eq_right (by rw [hcsize]; omega)]
    have hr0 : (rowOf (fillCtx ex W) p.2 p.1).getD c 0 = 0 := by
      rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none (by omega)]
      rfl
    rw [hr0]
    simp [Array.getD_eq_getD_getElem?, hnone]

/-! ## The steps of the trace -/

/-- The run's state after `k` steps, the initial state if there is none. -/
noncomputable def stateAt {prog : LeanIsaProgram} (ex : Execution prog) (k : ℕ) : Registers K :=
  (run prog ex.memory k Registers.initial).getD Registers.initial

theorem length_traceSteps {prog : LeanIsaProgram} (ex : Execution prog) :
    (traceSteps ex).length = ex.stepCount := by simp [traceSteps]

theorem getElem?_traceSteps {prog : LeanIsaProgram} (ex : Execution prog) {k : ℕ}
    (hk : k < ex.stepCount) : (traceSteps ex)[k]? = some (stepOf prog (stateAt ex k)) := by
  simp [traceSteps, hk, stateAt]

/-- A pair of a table is the trace's step at its cycle. -/
theorem tablePairs_step {prog : LeanIsaProgram} {ex : Execution prog} {t : ℕ} {p : Step × ℕ}
    (hp : p ∈ tablePairs (traceSteps ex) t) :
    p.2 < ex.stepCount ∧ p.1 = stepOf prog (stateAt ex p.2) := by
  have hz := List.mem_zipIdx_iff_getElem?.mp (List.mem_filter.mp hp).1
  have hk : p.2 < ex.stepCount := by
    rw [← length_traceSteps]
    exact (List.getElem?_eq_some_iff.mp hz).1
  rw [getElem?_traceSteps ex hk, Option.some.injEq] at hz
  exact ⟨hk, hz.symm⟩

/-- **A step of a valid trace**: from the run's state `k < T`, its instruction executes to state
`k + 1`; the states start initial and end final. -/
theorem step_succ {prog : LeanIsaProgram} {input : PublicInput} {ex : Execution prog}
    (hv : ValidExecution prog input ex) {k : ℕ} (hk : k < ex.stepCount) :
    executeWith ex.memory.read (stateAt ex k) (stepOf prog (stateAt ex k)).ins =
      some (stateAt ex (k + 1)) := by
  obtain ⟨r1, h1, hne⟩ := run_intermediate hv.2 hk
  obtain ⟨r2, h2, -⟩ := run_prefix (m := k + 1) (n := ex.stepCount - (k + 1))
    (by rw [show k + 1 + (ex.stepCount - (k + 1)) = ex.stepCount by omega]; exact hv.2)
  rw [run_add k 1, h1] at h2
  change run prog ex.memory 1 r1 = some r2 at h2
  rw [run_succ_of_ne_final hne] at h2
  obtain ⟨r2', hs, h0⟩ := Option.bind_eq_some_iff.mp h2
  rw [run_zero, Option.some.injEq] at h0
  subst h0
  obtain ⟨ins, hf, he⟩ := Option.bind_eq_some_iff.mp hs
  have h2' : run prog ex.memory (k + 1) Registers.initial = some r2' := by
    rw [run_add k 1, h1]
    change run prog ex.memory 1 r1 = some r2'
    rw [run_succ_of_ne_final hne]
    simp [hs]
  simp only [stateAt, h1, h2', Option.getD_some, stepOf, hf]
  exact he

theorem stateAt_zero {prog : LeanIsaProgram} (ex : Execution prog) :
    stateAt ex 0 = Registers.initial := rfl

theorem stateAt_stepCount {prog : LeanIsaProgram} {input : PublicInput} {ex : Execution prog}
    (hv : ValidExecution prog input ex) : stateAt ex ex.stepCount = Registers.final prog := by
  simp [stateAt, hv.2]

theorem slot_stepOf (prog : LeanIsaProgram) (r : Registers K) :
    (stepOf prog r).slot < 2 ^ prog.logSize := by
  unfold stepOf
  rcases addressIndex? prog.logSize r.pc with _ | i
  · exact Nat.two_pow_pos _
  · exact i.isLt

/-! ## Sums over the rows -/

theorem sum_getElem?_map {α : Type} (G : α → E) :
    ∀ l : List α, ∑ u ∈ range l.length, ((l[u]?).map G).getD 0 = (l.map G).sum
  | [] => by simp
  | a :: l => by
    rw [List.length_cons, Finset.sum_range_succ', List.map_cons, List.sum_cons, add_comm]
    simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.map_some,
      Option.getD_some]
    rw [sum_getElem?_map G l]

theorem sum_filter_tables (G : Step × ℕ → E) :
    ∀ P : List (Step × ℕ), ∑ t ∈ range nTables,
        ((P.filter fun p ↦ decide (opTableIdx p.1.ins.opcode = t)).map G).sum = (P.map G).sum
  | [] => by simp
  | p :: P => by
    simp only [List.filter_cons, List.map_cons, List.sum_cons, decide_eq_true_eq]
    rw [← sum_filter_tables G P]
    have : ∀ t ∈ range nTables, ((if opTableIdx p.1.ins.opcode = t then
        p :: P.filter (fun p ↦ decide (opTableIdx p.1.ins.opcode = t))
        else P.filter (fun p ↦ decide (opTableIdx p.1.ins.opcode = t))).map G).sum =
        (if opTableIdx p.1.ins.opcode = t then G p else 0) +
          ((P.filter fun p ↦ decide (opTableIdx p.1.ins.opcode = t)).map G).sum := by
      intro t _
      split_ifs <;> simp
    rw [Finset.sum_congr rfl this, Finset.sum_add_distrib, Finset.sum_ite_eq,
      ite_eq_left (Finset.mem_range.mpr (opTableIdx_lt _))]

/-- **A sum over every table's executed rows is a sum over the steps.** -/
theorem sum_tablePairs (L : List Step) (G : Step × ℕ → E) :
    ∑ t ∈ range nTables, ∑ u ∈ range (tablePairs L t).length,
        (((tablePairs L t)[u]?).map G).getD 0 =
      ∑ k ∈ range L.length, ((L[k]?).map fun st ↦ G (st, k)).getD 0 := by
  simp only [sum_getElem?_map]
  rw [show (fun t ↦ ((tablePairs L t).map G).sum) = fun t ↦
      ((L.zipIdx.filter fun p ↦ decide (opTableIdx p.1.ins.opcode = t)).map G).sum from rfl,
    sum_filter_tables]
  rw [← List.length_zipIdx (l := L), ← sum_getElem?_map]
  refine Finset.sum_congr rfl fun k hk ↦ ?_
  rw [List.length_zipIdx] at hk
  rw [List.getElem?_zipIdx]
  cases L[k]? <;> simp

/-- The tables' row counts add up to the steps. -/
theorem sum_rowCounts (L : List Step) : (rowCounts L.toArray).sum = L.length := by
  have h1 : (rowCounts L.toArray).sum = ∑ t ∈ range nTables, (tablePairs L t).length := by
    simp only [length_tablePairs]
    simp [rowCounts, nTables, List.range_succ, Finset.sum_range_succ, List.countP_toArray]
    ring
  rw [h1]
  simp only [length_tablePairs]
  clear h1
  induction L with
  | nil => simp
  | cons st L ih =>
    simp only [List.countP_cons, Finset.sum_add_distrib, ih, List.length_cons]
    simp [Finset.sum_ite_eq, opTableIdx_lt]

/-! ## The pointer columns -/

/-- Table `t`'s row `u`'s cycle, `0` past its rows. -/
def rowCycle (L : List Step) (t u : ℕ) : ℕ := (((tablePairs L t)[u]?).map (·.2)).getD 0

/-- Table `t`'s row `u`'s instruction slot, `0` past its rows. -/
def rowSlot (L : List Step) (t u : ℕ) : ℕ := (((tablePairs L t)[u]?).map (·.1.slot)).getD 0

/-- **An executed row's words are its step's `rowOf`.** -/
theorem word_witness {prog : LeanIsaProgram} {input : PublicInput} {ex : Execution prog}
    {W : Witness} (hW : witness? prog input ex = some W) (hv : ValidExecution prog input ex)
    {t u : ℕ} (ht : t < nTables) (hu : u < (tablePairs (traceSteps ex) t).length) (c : ℕ) :
    ((W.tableCols t).getD c #[]).getD u 0 = (rowOf (fillCtx ex W)
      (tablePairs (traceSteps ex) t)[u].2 (tablePairs (traceSteps ex) t)[u].1).getD c 0 :=
  ofK_injective (congrFun (rowValue_witness hW hv ht hu) c)

/-- The honest row counts are the steps'. -/
theorem rows_witness {prog : LeanIsaProgram} {input : PublicInput} {ex : Execution prog}
    {W : Witness} (hW : witness? prog input ex = some W) (hv : ValidExecution prog input ex)
    {t : ℕ} (ht : t < nTables) : W.rows.getD t 0 = (tablePairs (traceSteps ex) t).length := by
  rw [(witness_steps hW hv).1, rowCounts_getD _ ht]

/-- **The pointer width holds the cycles, the memory and the program.** -/
theorem width_witness {prog : LeanIsaProgram} {input : PublicInput} {ex : Execution prog}
    {W : Witness} (hW : witness? prog input ex = some W) (hv : ValidExecution prog input ex) :
    ChunksOK W.chunks ∧ W.rows.sum = ex.stepCount ∧ ex.stepCount < 2 ^ W.chunks.width ∧
      ex.logMemorySize ≤ W.chunks.width ∧ prog.logSize ≤ W.chunks.width := by
  obtain ⟨hr, -, -, hc⟩ := witness_steps hW hv
  obtain ⟨hok, hw⟩ := chunksOK_new hc
  have hsum : W.rows.sum = ex.stepCount := by rw [hr, sum_rowCounts, length_traceSteps]
  rw [hsum] at hw
  refine ⟨hok, hsum, ?_, ?_, ?_⟩ <;> rw [hw] <;> unfold pointerWidth
  · exact bitLength_lt (by omega)
  · omega
  · omega

/-- **The cycle pointers are one-hot**, at the rows' cycles. -/
theorem cycle_oneHot {prog : LeanIsaProgram} {input : PublicInput} {ex : Execution prog}
    {W : Witness} (hW : witness? prog input ex = some W) (hv : ValidExecution prog input ex)
    {t : ℕ} (ht : t < nTables) :
    OneHotWords W.chunks ((W.tableCols t).getD (tables.getD t default).links.stateLink.cycle #[])
      (W.rows.getD t 0) (rowCycle (traceSteps ex) t) := by
  intro u hu
  rw [rows_witness hW hv ht] at hu
  have hpt := mem_tablePairs (List.getElem_mem hu)
  have hrc : rowCycle (traceSteps ex) t u = (tablePairs (traceSteps ex) t)[u].2 := by
    simp [rowCycle, hu]
  refine ⟨?_, ?_⟩
  · rw [hrc]
    exact (tablePairs_step (List.getElem_mem hu)).1.trans (width_witness hW hv).2.2.1
  · rw [word_witness hW hv ht hu, hrc]
    generalize (tablePairs (traceSteps ex) t)[u] = p at hpt ⊢
    have h := (rowOf_state (fillCtx ex W) p.2 p.1).2.2.2.1
    rw [hpt] at h
    exact h

/-- **The program pointers are one-hot**, at the rows' instruction slots. -/
theorem bytecode_oneHot {prog : LeanIsaProgram} {input : PublicInput} {ex : Execution prog}
    {W : Witness} (hW : witness? prog input ex = some W) (hv : ValidExecution prog input ex)
    {t : ℕ} (ht : t < nTables) :
    OneHotWords W.chunks
      ((W.tableCols t).getD (tables.getD t default).links.bytecodeLink.pointer #[])
      (W.rows.getD t 0) (rowSlot (traceSteps ex) t) := by
  intro u hu
  rw [rows_witness hW hv ht] at hu
  have hpt := mem_tablePairs (List.getElem_mem hu)
  have hrs : rowSlot (traceSteps ex) t u = (tablePairs (traceSteps ex) t)[u].1.slot := by
    simp [rowSlot, hu]
  refine ⟨?_, ?_⟩
  · rw [hrs, (tablePairs_step (List.getElem_mem hu)).2]
    exact lt_of_lt_of_le (slot_stepOf _ _)
      (Nat.pow_le_pow_right (by norm_num) (width_witness hW hv).2.2.2.2)
  · rw [word_witness hW hv ht hu, hrs]
    generalize (tablePairs (traceSteps ex) t)[u] = p at hpt ⊢
    have h := (rowOf_state (fillCtx ex W) p.2 p.1).2.2.2.2
    rw [hpt] at h
    exact h

/-- The index of the cell at `a` a row's memory pointer names: its address index, `0` outside
the memory. -/
def cellIndex {κ : ℕ} (ctx : FillCtx κ) (a : K) : ℕ := ((gLogIn ctx.memIdx κ a).map (·.val)).getD 0

theorem cell_eq {κ : ℕ} (ctx : FillCtx κ) (a : K) :
    ctx.cell a = K.ofBits (ctx.chunks.encode (cellIndex ctx a)) := rfl

theorem cellIndex_lt {κ : ℕ} (ctx : FillCtx κ) (a : K) : cellIndex ctx a < 2 ^ κ := by
  unfold cellIndex
  rcases gLogIn ctx.memIdx κ a with _ | i
  · exact Nat.two_pow_pos _
  · exact i.isLt

/-- **A memory pointer names its cell**: on the honest witness, the address index of `a`. -/
theorem cellIndex_witness {prog : LeanIsaProgram} {input : PublicInput} {ex : Execution prog}
    {W : Witness} (hv : ValidExecution prog input ex) (a : K) :
    cellIndex (fillCtx ex W) a = ((addressIndex? ex.logMemorySize a).map (·.val)).getD 0 := by
  rw [cellIndex, fillCtx, gLogIn_powIndex (logMemorySize_lt hv)]

/-- A memory pointer of an honest row is one-hot, below the pointer width. -/
theorem cell_oneHot {prog : LeanIsaProgram} {input : PublicInput} {ex : Execution prog}
    {W : Witness} (hW : witness? prog input ex = some W) (hv : ValidExecution prog input ex)
    (a : K) : cellIndex (fillCtx ex W) a < 2 ^ W.chunks.width ∧
      (fillCtx ex W).cell a = K.ofBits (W.chunks.encode (cellIndex (fillCtx ex W) a)) :=
  ⟨lt_of_lt_of_le (cellIndex_lt _ a)
    (Nat.pow_le_pow_right (by norm_num) (width_witness hW hv).2.2.2.1), rfl⟩

end LeanVM.Prover.Complete

end
