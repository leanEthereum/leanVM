/-
  LeanVM.Protocol.EndToEnd.Front.LayoutInstance

  The layout the verifier program builds from the bytecode and the announced sizes is the
  leanISA instance's: the bytecode words, the global column numbering, the stacked size and
  every column's placement on the stack.
-/

module

public import LeanVM.Protocol.EndToEnd.Front.LayoutStack
public import LeanVM.Protocol.LeanIsa
public import LeanVM.Protocol.Verifier
public import LeanVM.Spec.Statement

/-!
# The verifier's layout is the instance's

The verifier program (`LeanVM.Protocol.Verifier`, `python-verifier/verifier.py` at leanVM
`127510d14c98ade4e8a97646c44fa7f1ff5e752d`) computes its own layout (`buildLayout`) from the
bytecode words and the announced sizes; the oracle protocol reads the stack through the leanISA
instance's layout (`leanIsaInstance F prog s`, `LeanVM.Protocol.LeanIsa`). This module proves
they are one layout, for every program and every size vector:

* `bytecodeWords prog`: the bytecode the verifier takes, the instance's public bytecode column
  (`bytecodeColumn`, `FixedColumns.lean`) as a list: `2 ^ (logSize + 4)` words, instruction bits
  low, slot bits high, sixteen slots per instruction, the entry at slots 3 to 10.
* `pyCol c`: the Python's global column number of the instance's column `c`, its position in the
  instance's global order (`columns`): the memory columns `0 to 3`, `BFCNT` `4`, `QFLOCK` `5`, then
  the six opcode tables' columns in order. `pyCol_*` give the named columns.
* `buildLayout_eq`: the layout is built from the announced rows (`tableRows`) exactly when the
  sizes are in the windows `buildLayout` checks (`LayoutOk`), and is then `verifierLayout prog s`,
  whose log-heights are `tableLogs s` (`map_log2Ceil_tableRows`).
* `stackLog_verifierLayout`: its stacked size is the instance's `μ`.
* `placement_committed`, `placement_limb`: every committed column at its block's offset, every
  `BLAKE2S` limb at its Flock slot (for the deployed slots `Blake2sFlock.slots`).
* `stackPoint_eq_extend`: a point placed by the verifier's layout is the instance layout's lift
  of that point; hence `onStack_holds_iff`: a verifier column claim holds of a stack exactly when
  the instance's column claim holds.
-/

namespace LeanVM.Protocol.EndToEnd.Front

open LeanVM.Parameters LeanVM.Semantics LeanVM.Arithmetization LeanVM.Protocol.Verifier
open LeanVM.Protocol.LeanIsa CompPoly CMlPolynomialEval

@[expose] public section

/-! ## The bytecode -/

export LeanVM (bytecodeWords)

/-- The bytecode the verifier takes (`LeanVM.bytecodeWords`) is the program's sixteen-slot
bytecode column as a list of words, instruction bits low, slot bits high (`bytecodeColumn`). -/
theorem bytecodeWords_eq_column (prog : Program) :
    bytecodeWords prog = (bytecodeColumn prog).values.toList := by
  have h16 : 2 ^ prog.logSize * 16 = 2 ^ (prog.logSize + 4) := by rw [pow_add]; norm_num
  rw [bytecodeColumn, Vector.toList_ofFn, List.ofFn_congr h16.symm, List.ofFn_mul',
    LeanVM.bytecodeWords, List.flatMap_def]
  simp only [← List.ofFn_eq_map]
  congr 1
  refine List.ofFn_inj.mpr (funext fun s ↦ List.ofFn_inj.mpr (funext fun i ↦ ?_))
  have hs : (cubeSplit prog.logSize 4).symm
      (Fin.cast h16 ⟨2 ^ prog.logSize * s + i, by have := s.isLt; have := i.isLt; nlinarith⟩) =
        (i, s) := by
    rw [Equiv.symm_apply_eq, cubeSplit_apply]
    ext
    simp only [Fin.val_cast, cubeIndex]
    ring
  simp only [hs]

/-- The bytecode has `2 ^ (logSize + 4)` words. -/
theorem length_bytecodeWords (prog : Program) :
    (bytecodeWords prog).length = 2 ^ (prog.logSize + 4) := by
  simp [bytecodeWords_eq_column]

/-- **The bytecode names the program.** -/
theorem bytecodeWords_injective : Function.Injective bytecodeWords := by
  intro prog prog' h
  have hl := congrArg List.length h
  rw [length_bytecodeWords, length_bytecodeWords] at hl
  have hs : prog.logSize = prog'.logSize := by
    have := Nat.pow_right_injective (le_refl 2) hl
    omega
  exact bytecodeColumn_injective hs (by rwa [bytecodeWords_eq_column, bytecodeWords_eq_column] at h)

/-- `log2_strict` of a power of two. -/
theorem log2Strict_two_pow (n : ℕ) : log2Strict (2 ^ n) = some n := by
  have hpos : 0 < 2 ^ n := Nat.two_pow_pos n
  have hand : 2 ^ n &&& (2 ^ n - 1) = 0 := by
    apply Nat.eq_of_testBit_eq
    intro i
    rw [Nat.testBit_and, Nat.testBit_two_pow_sub_one, Nat.testBit_two_pow]
    simp only [Nat.zero_testBit, Bool.and_eq_false_iff, decide_eq_false_iff_not]
    by_cases h : n = i <;> simp [h]
  have hbl : bitLength (2 ^ n) = n + 1 := by
    simp [bitLength, Nat.log2_two_pow]
  simp [log2Strict, hpos, hand, hbl]

/-- The bytecode's `log2_strict` length. -/
theorem log2Strict_length_bytecodeWords (prog : Program) :
    log2Strict (bytecodeWords prog).length = some (prog.logSize + 4) := by
  rw [length_bytecodeWords, log2Strict_two_pow]

/-! ## The global columns -/

/-- The table row counts the prover announces, in opcode order. -/
def tableRows (s : Sizes) : List ℕ := List.ofFn s.rows

/-- The tables' log-heights, in opcode order. -/
def tableLogs (s : Sizes) : List ℕ := List.ofFn s.τ

/-- The verifier's log-heights of the announced rows (`log2_ceil`) are the tables'. -/
theorem map_log2Ceil_tableRows (s : Sizes) : (tableRows s).map log2Ceil = tableLogs s := by
  simp only [tableRows, tableLogs, List.map_ofFn, Function.comp_def, log2Ceil_eq_clog]
  rfl

/-- The Python's global column number of the instance's column `c`: its position in the global
order. -/
def pyCol (c : Col) : ℕ := columns.idxOf c

/-- The instance has `110` columns, as the Python. -/
theorem length_columns : columns.length = 110 := by decide +kernel

/-- Every column is in the global order. -/
theorem mem_columns (c : Col) : c ∈ columns := by
  simp only [columns, List.mem_flatMap, List.mem_finRange, List.mem_map, true_and]
  exact ⟨c.1, c.2, rfl⟩

/-- A global column number is below `110`. -/
theorem pyCol_lt (c : Col) : pyCol c < 110 :=
  length_columns ▸ List.idxOf_lt_length_of_mem (mem_columns c)

/-- The column at a global number. -/
theorem getElem_columns_pyCol (c : Col) :
    columns[pyCol c]'(length_columns ▸ pyCol_lt c) = c :=
  List.getElem_idxOf _

/-- Distinct columns have distinct numbers. -/
theorem pyCol_injective : Function.Injective pyCol := by
  intro a b h
  rw [← getElem_columns_pyCol a, ← getElem_columns_pyCol b]
  simp only [h]

/-- The memory columns are global columns `0 to 3`: `MEMORY_0, MEMORY_1, MEMORY_2` and
`MEMORY_FINAL_COUNTERS`. -/
theorem pyCol_memCol (i : Fin 4) : pyCol (memCol i) = i := by
  revert i; decide +kernel

/-- `BFCNT` is `BYTECODE_FINAL_COUNTERS`. -/
theorem pyCol_bfcntCol : pyCol bfcntCol = bytecodeFinalCounters := by decide +kernel

/-- `QFLOCK` is `QFLOCK`. -/
theorem pyCol_flockCol : pyCol flockCol = qflock := by decide +kernel

/-- Column `i` of opcode table `j` is the Python's `GLOBAL_COLUMN_BASES[j] + i`. -/
theorem pyCol_opIdx (j : Fin 6) (i : Fin (width (opIdx j))) :
    pyCol ⟨opIdx j, i⟩ = globalColumnBases.getD j 0 + i := by
  revert j i; decide +kernel

/-- A table's Python width is the instance's. -/
theorem width_opIdx (j : Fin 6) : width (opIdx j) = (tables.getD j default).width := by
  revert j; decide +kernel

/-! ## The layout -/

/-- The checks `build_layout` makes of the sizes (`verifier.py:858-866`) for the program's
bytecode: the memory window `[16, 32]` and the row cap `2 ^ 32`. The bytecode's checks hold by
construction (`Program.logSize_le`). -/
def LayoutOk (s : Sizes) : Prop :=
  minLogMem ≤ s.logMem ∧ s.logMem ≤ maxLogMem ∧ ∀ j, s.rows j ≤ 2 ^ maxLogRows

instance (s : Sizes) : Decidable (LayoutOk s) := inferInstanceAs (Decidable (_ ∧ _))

/-- The Python's column log-sizes, in global order (`columnKappas`). -/
abbrev pyKappas (prog : Program) (s : Sizes) : List ℕ :=
  columnKappas s.logMem prog.logSize (tableLogs s)

/-- The layout the verifier builds for the program `prog` at the sizes `s`: `build_layout`'s
value when its checks pass. -/
def verifierLayout (prog : Program) (s : Sizes) : Verifier.Layout :=
  let (push, pull, count) := busBlocks (tableLogs s) (tableRows s)
  let (placements, stackLog) := placementsOf (pyKappas prog s)
  ⟨s.logMem, prog.logSize, bytecodeWords prog, push, pull, count, placements, stackLog,
    tableLogs s⟩

/-- Every table's announced row count is within the cap, as a list. -/
private theorem all_tableRows (s : Sizes) :
    ((tableRows s).all fun t ↦ decide (t ≤ 2 ^ 32)) = true ↔ ∀ j, s.rows j ≤ 2 ^ maxLogRows := by
  simp [tableRows, maxLogRows, Fin.forall_fin_succ]

/-- **The layout is built** exactly when the sizes pass `build_layout`'s checks, and it is then
`verifierLayout prog s`. -/
theorem buildLayout_eq (prog : Program) (s : Sizes) :
    buildLayout (bytecodeWords prog) s.logMem (tableRows s) =
      if LayoutOk s then some (verifierLayout prog s) else none := by
  have hL := prog.logSize_le
  unfold buildLayout
  rw [log2Strict_length_bytecodeWords]
  simp only [busBits, Nat.add_sub_cancel, map_log2Ceil_tableRows]
  have hlen : (tableRows s).length = tables.length := by
    simp [tableRows, tables]
  by_cases hok : LayoutOk s
  · obtain ⟨h1, h2, h3⟩ := hok
    have hc : 4 ≤ prog.logSize + 4 ∧ 16 ≤ s.logMem ∧ s.logMem ≤ 32 ∧
        ((tableRows s).all fun t ↦ decide (t ≤ 2 ^ 32)) = true ∧
        prog.logSize ≤ 32 ∧ (tableRows s).length = tables.length :=
      ⟨by omega, h1, h2, (all_tableRows s).mpr h3, by simpa [maxLogBytecode] using hL, hlen⟩
    have hok : LayoutOk s := ⟨h1, h2, h3⟩
    simp only [hc, hok, and_self, ↓reduceIte]
    rfl
  · have hc : ¬ (4 ≤ prog.logSize + 4 ∧ 16 ≤ s.logMem ∧ s.logMem ≤ 32 ∧
        ((tableRows s).all fun t ↦ decide (t ≤ 2 ^ 32)) = true ∧
        prog.logSize ≤ 32 ∧ (tableRows s).length = tables.length) := by
      rintro ⟨-, h1, h2, h3, -, -⟩
      exact hok ⟨h1, h2, (all_tableRows s).mp h3⟩
    simp only [hc, hok, ↓reduceIte]

/-! ## The column sizes and the blocks -/

/-- The instance's widths, table by table. -/
theorem width_vals : width 0 = 4 ∧ width 1 = 1 ∧ width 2 = 1 ∧ width 3 = 15 ∧ width 4 = 15 ∧
    width 5 = 8 ∧ width 6 = 15 ∧ width 7 = 14 ∧ width 8 = 37 := by
  decide +kernel

/-- A function of the table, along the global order. -/
theorem columns_map_fst (h : Fin 9 → ℕ) :
    columns.map (fun c ↦ h c.1) =
      (List.finRange 9).flatMap fun j ↦ List.replicate (width j) (h j) := by
  simp only [columns, List.map_flatMap, List.map_map]
  congr 1
  funext j
  simp [Function.comp_def, List.map_const']

/-- The Python's column log-sizes are the instance's, in global order. -/
theorem pyKappas_eq (prog : Program) (s : Sizes) :
    pyKappas prog s = columns.map (kappa prog s) := by
  rw [columns_map_fst (height prog s)]
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩ := width_vals
  rw [show List.finRange 9 = [0, 1, 2, 3, 4, 5, 6, 7, 8] by decide]
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, h0, h1, h2, h3, h4, h5, h6,
    h7, h8]
  simp only [pyKappas, columnKappas, tables, List.flatMap_cons, List.flatMap_nil,
    List.append_nil]
  have hq : (tableLogs s).getD opBlake2s 0 + qflockSlotBits = height prog s 2 := by
    rw [add_comm]
    rfl
  rw [hq]
  rfl

/-- The Python's log-size of a column is the instance's. -/
theorem getD_pyKappas (prog : Program) (s : Sizes) (c : Col) :
    (pyKappas prog s).getD (pyCol c) 0 = kappa prog s c := by
  have h : pyCol c < (columns.map (kappa prog s)).length := by
    rw [List.length_map, length_columns]
    exact pyCol_lt c
  rw [pyKappas_eq, List.getD_eq_getElem _ _ h, List.getElem_map, getElem_columns_pyCol]

/-- The Python has `110` columns. -/
theorem length_pyKappas (prog : Program) (s : Sizes) : (pyKappas prog s).length = 110 := by
  rw [pyKappas_eq, List.length_map, length_columns]

/-- The Flock slot of a global column: the deployed slot of a limb, none otherwise. -/
theorem limbSlot_pyCol (c : Col) :
    limbSlot (pyCol c) = if h : IsLimb c then
      some (Blake2sFlock.slots ⟨c.2.val - 9, by have := h.2.2; omega⟩).val else none := by
  revert c; decide +kernel

/-- The Python's committed columns (`block_cols`) are the instance's, in global order. -/
theorem blockCols_eq :
    (List.range 110).filter (fun c ↦ (limbSlot c).isNone) = committedColumns.map pyCol := by
  decide +kernel

/-- The committed columns are distinct. -/
theorem nodup_committedColumns : committedColumns.Nodup := by decide +kernel

/-- The Python's block index of a committed column is its index among the committed
columns. -/
theorem idxOf_blockCols : ∀ c ∈ committedColumns,
    (committedColumns.map pyCol).idxOf (pyCol c) = committedColumns.idxOf c := by
  decide +kernel

/-- The block sizes the Python stacks are the committed columns' log-sizes. -/
theorem blockSizes_eq (prog : Program) (s : Sizes) :
    (committedColumns.map pyCol).map ((pyKappas prog s).getD · 0) =
      committedColumns.map (kappa prog s) := by
  rw [List.map_map]
  exact List.map_congr_left fun c _ ↦ getD_pyKappas prog s c

/-! ## The stacking order -/

/-- The committed columns' indices, in order, are the range. -/
private theorem map_idxOf_self {α : Type} [BEq α] [LawfulBEq α] {l : List α} (hl : l.Nodup) :
    l.map l.idxOf = List.range l.length := by
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp only [List.getElem_map, List.getElem_range]
  exact hl.idxOf_getElem i _

/-- The size of the block at a committed column's index. -/
private theorem getD_blockSizes (prog : Program) (s : Sizes) {c : Col}
    (hc : c ∈ committedColumns) :
    (committedColumns.map (kappa prog s)).getD (committedColumns.idxOf c) 0 = kappa prog s c := by
  rw [List.getD_eq_getElem _ _ (by
      rw [List.length_map]; exact List.idxOf_lt_length_of_mem hc),
    List.getElem_map, List.getElem_idxOf]

/-- **The Python's stacking order is the instance's**: `stack_offsets`' sort of the committed
columns' indices is the instance's stacking order, read as indices. -/
theorem order_eq (prog : Program) (s : Sizes) :
    (List.range committedColumns.length).mergeSort
        (fun i j ↦ decide ((committedColumns.map (kappa prog s)).getD j 0 ≤
          (committedColumns.map (kappa prog s)).getD i 0)) =
      (stackOrder prog s).map committedColumns.idxOf := by
  rw [stackOrder, List.map_mergeSort (s := fun i j ↦ decide
      ((committedColumns.map (kappa prog s)).getD j 0 ≤
        (committedColumns.map (kappa prog s)).getD i 0)),
    map_idxOf_self nodup_committedColumns]
  intro a ha b hb
  rw [getD_blockSizes prog s ha, getD_blockSizes prog s hb]

/-- The instance's offsets: the heights of the blocks before, in stacking order. -/
theorem offsetNat_eq (prog : Program) (s : Sizes) (k : ℕ) (hk : k ≤ (blocks prog s).n) :
    (blocks prog s).offsetNat k =
      (((stackOrder prog s).take k).map fun c ↦ 2 ^ kappa prog s c).sum := by
  induction k with
  | zero => simp [Blocks.offsetNat]
  | succ k ih =>
    rw [Blocks.offsetNat_succ _ k (by omega), ih (by omega),
      List.take_succ_eq_append_getElem (by simpa [blocks] using hk), List.map_append,
      List.sum_append]
    rfl

/-- The stacking order holds the committed columns. -/
private theorem mem_committed_of_mem_stackOrder (prog : Program) (s : Sizes) {c : Col}
    (h : c ∈ stackOrder prog s) : c ∈ committedColumns :=
  List.mem_mergeSort.mp h

/-- **The Python's offsets are the instance's**: in `stack_offsets` of the committed columns'
sizes, the block of a committed column starts at the instance's offset of its block. -/
theorem stackOffsets_getD (prog : Program) (s : Sizes) (c : Col) (h : ¬ IsLimb c) :
    (stackOffsets (committedColumns.map (kappa prog s))).1.getD (committedColumns.idxOf c) 0 =
      (blocks prog s).offset (blockOf c h) := by
  have hnd := (List.mergeSort_perm (List.range committedColumns.length)
    (fun i j ↦ decide ((committedColumns.map (kappa prog s)).getD j 0 ≤
      (committedColumns.map (kappa prog s)).getD i 0))).nodup_iff.mpr List.nodup_range
  rw [order_eq] at hnd
  rw [stackOffsets_eq]
  simp only [List.length_map]
  rw [order_eq]
  have hk : (blockOf (prog := prog) (s := s) c h).val < ((stackOrder prog s).map
      committedColumns.idxOf).length := by
    rw [List.length_map]; exact (blockOf c h).isLt
  have hget : ((stackOrder prog s).map committedColumns.idxOf)[(blockOf (prog := prog)
      (s := s) c h).val] = committedColumns.idxOf c := by
    rw [List.getElem_map]
    have := stackOrder_blockOf prog s c h
    simp only [this]
  have hfold := placeFold_getElem? (fun i ↦ 2 ^ (committedColumns.map (kappa prog s)).getD i 0)
    _ hnd (List.replicate committedColumns.length 0, 0) (fun i hi ↦ by
      obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hi
      simpa using List.idxOf_lt_length_of_mem (mem_committed_of_mem_stackOrder prog s ha)) _ hk
  rw [hget] at hfold
  rw [List.getD_eq_getElem?_getD, hfold, Option.getD_some, zero_add, Blocks.offset,
    offsetNat_eq prog s _ (blockOf c h).isLt.le, ← List.map_take, List.map_map]
  refine congrArg List.sum (List.map_congr_left fun a ha ↦ ?_)
  simp only [Function.comp_apply]
  rw [getD_blockSizes prog s (mem_committed_of_mem_stackOrder prog s
    (List.mem_of_mem_take ha))]

/-- The Python's stacked total is the instance's. -/
theorem stackOffsets_snd (prog : Program) (s : Sizes) :
    (stackOffsets (committedColumns.map (kappa prog s))).2 = Nat.clog 2 (blocks prog s).total := by
  rw [stackOffsets_eq]
  simp only [List.length_map]
  rw [order_eq, placeFold_snd, log2Ceil_eq_clog, Blocks.total,
    offsetNat_eq prog s _ le_rfl, zero_add]
  congr 2
  rw [List.take_of_length_le (by simp [blocks]), List.map_map]
  refine List.map_congr_left fun a ha ↦ ?_
  simp only [Function.comp_apply]
  rw [getD_blockSizes prog s (mem_committed_of_mem_stackOrder prog s ha)]

/-! ## The placements -/

/-- The Python's offset of a global column's block (`offset_of` in `placements_of`). -/
def pyOffset (prog : Program) (s : Sizes) (column : ℕ) : ℕ :=
  let blockCols := (List.range (pyKappas prog s).length).filter fun c ↦ (limbSlot c).isNone
  (stackOffsets (blockCols.map ((pyKappas prog s).getD · 0))).1.getD (blockCols.idxOf column) 0

/-- `placements_of`, unfolded: each column's placement from its log-size and the offsets. -/
theorem placementsOf_pyKappas (prog : Program) (s : Sizes) :
    placementsOf (pyKappas prog s) =
      ((pyKappas prog s).zipIdx.map fun (kappa, column) ↦
        match limbSlot column with
        | some slot =>
          ({ vars := kappa, index := pyOffset prog s qflock + slot, low := qflockSlotBits } :
            Placement)
        | none => { vars := kappa, index := pyOffset prog s column },
      max minStackedLog (stackOffsets (((List.range (pyKappas prog s).length).filter
        fun c ↦ (limbSlot c).isNone).map ((pyKappas prog s).getD · 0))).2) := rfl

/-- The Python's offset of a committed column is its block's. -/
theorem pyOffset_pyCol (prog : Program) (s : Sizes) (c : Col) (h : ¬ IsLimb c) :
    pyOffset prog s (pyCol c) = (blocks prog s).offset (blockOf c h) := by
  unfold pyOffset
  simp only [length_pyKappas, blockCols_eq, blockSizes_eq]
  rw [idxOf_blockCols c (mem_committedColumns h), stackOffsets_getD]

/-- **The stacked size is the instance's `μ`.** -/
theorem stackLog_verifierLayout (prog : Program) (s : Sizes) :
    (verifierLayout prog s).stackLog = leanIsaμ prog s := by
  show (placementsOf (pyKappas prog s)).2 = _
  rw [placementsOf_pyKappas]
  simp only [length_pyKappas, blockCols_eq, blockSizes_eq]
  rw [stackOffsets_snd, max_comm]
  rfl

/-- The Python's placement of a global column. -/
theorem placements_getD (prog : Program) (s : Sizes) (c : Col) :
    (verifierLayout prog s).placements.getD (pyCol c) default =
      match limbSlot (pyCol c) with
      | some slot =>
        { vars := kappa prog s c, index := pyOffset prog s qflock + slot, low := qflockSlotBits }
      | none => { vars := kappa prog s c, index := pyOffset prog s (pyCol c) } := by
  show (placementsOf (pyKappas prog s)).1.getD (pyCol c) default = _
  have hlt : pyCol c < (pyKappas prog s).zipIdx.length := by
    rw [List.length_zipIdx, length_pyKappas]; exact pyCol_lt c
  rw [placementsOf_pyKappas, List.getD_eq_getElem _ _ (by rw [List.length_map]; exact hlt),
    List.getElem_map, List.getElem_zipIdx]
  have hk := getD_pyKappas prog s c
  rw [List.getD_eq_getElem _ _ (by simpa using hlt)] at hk
  simp only [zero_add, hk]

/-- **A committed column's placement**: its log-size, at its block's offset. -/
theorem placement_committed (prog : Program) (s : Sizes) (c : Col) (h : ¬ IsLimb c) :
    (verifierLayout prog s).placements.getD (pyCol c) default =
      { vars := kappa prog s c, index := (blocks prog s).offset (blockOf c h) } := by
  rw [placements_getD, limbSlot_pyCol]
  simp only [h, ↓reduceDIte]
  rw [pyOffset_pyCol prog s c h]

/-- **A `BLAKE2S` limb's placement**: `τ_BLAKE2S` variables at its deployed slot of the Flock
region, below the region's `8` low coordinates. -/
theorem placement_limb (prog : Program) (s : Sizes) (c : Col) (h : IsLimb c) :
    (verifierLayout prog s).placements.getD (pyCol c) default =
      { vars := s.τ 5,
        index := (blocks prog s).offset (flockBlock prog s) +
          (Blake2sFlock.slots ⟨c.2.val - 9, by have := h.2.2; omega⟩).val,
        low := 8 } := by
  rw [placements_getD, limbSlot_pyCol]
  simp only [h, ↓reduceDIte]
  rw [← pyCol_flockCol, pyOffset_pyCol prog s flockCol not_isLimb_flockCol]
  have hk : kappa prog s c = s.τ 5 := by
    simp only [kappa, h.1]
    rfl
  rw [hk]
  rfl

/-! ## Placed points are lifted points -/

/-- A union of layouts lifts a left column through the left layout. -/
theorem piecewise_extend_inl {μ : ℕ} {ι₁ ι₂ : Type} {κ₁ : ι₁ → ℕ} {κ₂ : ι₂ → ℕ}
    (L₁ : LeanVM.Protocol.Layout μ ι₁ κ₁) (L₂ : LeanVM.Protocol.Layout μ ι₂ κ₂)
    (r : ι₁ ⊕ ι₂) (b : ι₁) (hr : r = .inl b) (v : Vector E (Sum.elim κ₁ κ₂ r)) :
    (L₁.piecewise L₂).extend r v = L₁.extend b (Vector.cast (by subst hr; rfl) v) := by
  subst hr; rfl

/-- A union of layouts lifts a right column through the right layout. -/
theorem piecewise_extend_inr {μ : ℕ} {ι₁ ι₂ : Type} {κ₁ : ι₁ → ℕ} {κ₂ : ι₂ → ℕ}
    (L₁ : LeanVM.Protocol.Layout μ ι₁ κ₁) (L₂ : LeanVM.Protocol.Layout μ ι₂ κ₂)
    (r : ι₁ ⊕ ι₂) (b : ι₂) (hr : r = .inr b) (v : Vector E (Sum.elim κ₁ κ₂ r)) :
    (L₁.piecewise L₂).extend r v = L₂.extend b (Vector.cast (by subst hr; rfl) v) := by
  subst hr; rfl

/-- `boolVec` as a list is the cube point. -/
theorem toList_boolVec {m : ℕ} (x : Fin (2 ^ m)) :
    (boolVec x : Vector E m).toList = boolPoint m x := (boolPoint_eq_toList_boolVec x).symm

/-- The instance lifts a point of a committed column to the point followed by the bits of its
block's selector. -/
theorem extend_committed (prog : Program) (s : Sizes) (slot : Fin 18 → Fin 256) (c : Col)
    (h : ¬ IsLimb c) (z : Vector E (kappa prog s c)) :
    ((LeanIsa.layout prog s slot).extend c z).toList =
      z.toList ++ boolPoint (leanIsaμ prog s - kappa prog s c)
        ((blocks prog s).offset (blockOf c h) / 2 ^ kappa prog s c) := by
  have e : (LeanIsa.layout prog s slot).extend c z =
      (((blocks prog s).layout (blocks_fits prog s)).piecewise
        ((blocks prog s).stridedLayout (blocks_fits prog s) (flockBlock prog s) 8 slot
          (κ := fun _ ↦ s.τ 5) fun _ ↦ size_flockBlock prog s)).extend (route prog s c)
        (Vector.cast (route_kappa prog s c).symm z) := rfl
  have hr : route prog s c = .inl (blockOf c h) := by simp [route, h]
  rw [e, piecewise_extend_inl _ _ _ _ hr]
  simp only [Blocks.layout, Blocks.extendPoint, Vector.toList_cast, Vector.toList_append,
    toList_boolVec, Blocks.selector_val, size_blockOf]

/-- The instance lifts a point of a `BLAKE2S` limb to its slot's bits, the point, and the bits of
the Flock region's selector. -/
theorem extend_limb (prog : Program) (s : Sizes) (slot : Fin 18 → Fin 256) (c : Col)
    (h : IsLimb c) (z : Vector E (kappa prog s c)) :
    ((LeanIsa.layout prog s slot).extend c z).toList =
      boolPoint 8 (slot ⟨c.2.val - 9, by have := h.2.2; omega⟩) ++ z.toList ++
        boolPoint (leanIsaμ prog s - (8 + s.τ 5))
          ((blocks prog s).offset (flockBlock prog s) / 2 ^ (8 + s.τ 5)) := by
  have e : (LeanIsa.layout prog s slot).extend c z =
      (((blocks prog s).layout (blocks_fits prog s)).piecewise
        ((blocks prog s).stridedLayout (blocks_fits prog s) (flockBlock prog s) 8 slot
          (κ := fun _ ↦ s.τ 5) fun _ ↦ size_flockBlock prog s)).extend (route prog s c)
        (Vector.cast (route_kappa prog s c).symm z) := rfl
  have hr : route prog s c = .inr ⟨c.2.val - 9, by have := h.2.2; omega⟩ := by simp [route, h]
  rw [e, piecewise_extend_inr _ _ _ _ hr]
  simp only [Blocks.stridedLayout, Blocks.extendPoint, Vector.toList_cast, Vector.toList_append,
    toList_boolVec, Blocks.selector_val, size_flockBlock]
/-- **A placed point is the instance's lifted point**: for the deployed Flock slots, the
verifier's layout places a point of column `pyCol c` where the instance's layout lifts it. -/
theorem stackPoint_eq_extend (prog : Program) (s : Sizes) (F : FlockSpec)
    (hF : F.slot = Blake2sFlock.slots) (c : Col)
    (z : Vector E (kappa prog s c)) :
    ((verifierLayout prog s).placements.getD (pyCol c) default).stackPoint z.toList
        (verifierLayout prog s).stackLog =
      ((leanIsaInstance F prog s).layout.extend c z).toList := by
  rw [stackLog_verifierLayout]
  show _ = ((LeanIsa.layout prog s F.slot).extend c z).toList
  by_cases h : IsLimb c
  · have hsz := Blocks.size_le _ (blocks_fits prog s) (flockBlock prog s)
    have hdvd := Blocks.pow_size_dvd_offset _ (flockBlock prog s)
    rw [size_flockBlock] at hsz hdvd
    rw [placement_limb prog s c h, extend_limb prog s _ c h, hF,
      stackPoint_strided _ _ _ _ _ (by unfold leanIsaμ at hsz ⊢; omega) hdvd
        (Blake2sFlock.slots _).isLt]
  · rw [placement_committed prog s c h, extend_committed prog s _ c h, stackPoint_aligned]

/-- **A verifier column claim means the instance's column claim**: the claim on global column
`pyCol c` at `z` with value `v`, placed on the stack by the verifier's layout, holds of a stack
exactly when the instance's claim on `c` at `z` with value `v` holds of it. -/
theorem onStack_holds_iff (prog : Program) (s : Sizes) (F : FlockSpec)
    (hF : F.slot = Blake2sFlock.slots) (c : Col)
    (z : Vector E (kappa prog s c)) (v : E) (q : Column (leanIsaμ prog s)) :
    StackClaim.Holds (leanIsaμ prog s)
        ((⟨pyCol c, z.toList, v⟩ : Verifier.ColumnClaim).onStack (verifierLayout prog s)) q ↔
      (⟨c, z, v⟩ : LeanVM.Protocol.ColumnClaim (leanIsaInstance F prog s)).Holds q := by
  unfold Verifier.ColumnClaim.onStack
  simp only
  rw [stackPoint_eq_extend prog s F hF c z, stackClaim_holds_eqEval_iff]
  unfold LeanVM.Protocol.ColumnClaim.Holds M3Instance.column
  rw [(leanIsaInstance F prog s).layout.read_eval]

/-! ## The bytecode fingerprint -/

/-- The bytecode column's extension at `(z, w)` is the eight entry columns' extensions at `z`,
weighted by the Lagrange basis of `w` at slots `3 to 10`: the other slots are zero. -/
theorem bytecodeColumnEval_eq_entries (prog : Program) (z : Vector E prog.logSize)
    (w : Vector E 4) :
    bytecodeColumnEval prog z w =
      ∑ k : Fin 8, (lagrangeBasis w)[k.val + 3] *
        eval₂Mle (entryColumn prog k).values (algebraMap K E) z := by
  unfold bytecodeColumnEval
  let e : Fin 8 → Fin 16 := fun k ↦ ⟨k.val + 3, by omega⟩
  have he : Function.Injective e := fun a b h ↦ by
    simp only [e, Fin.mk.injEq] at h; exact Fin.ext (by omega)
  rw [← Finset.sum_subset (Finset.subset_univ (Finset.univ.image e)), Finset.sum_image
    (fun a _ b _ h ↦ he h)]
  · refine Finset.sum_congr rfl fun k _ ↦ ?_
    simp only [e, eval₂Mle, evalMle_eq_sum]
    refine congrArg₂ (· * ·) rfl (Finset.sum_congr rfl fun i _ ↦ ?_)
    refine congrArg₂ (· * ·) ?_ rfl
    have h := encodeSlots_getElem (prog.code i) (k.val + 3) (by omega)
    simp only [show 3 ≤ k.val + 3 ∧ k.val + 3 < 11 from ⟨by omega, by omega⟩] at h
    simp only [Fin.getElem_fin] at h ⊢
    rw [h]
    simp [CMlPolynomialEval.map, entryColumn]
  · intro s _ hs
    have hs' : ¬ (3 ≤ s.val ∧ s.val < 11) := by
      rintro ⟨h1, h2⟩
      exact hs (Finset.mem_image.mpr ⟨⟨s.val - 3, by omega⟩, Finset.mem_univ _,
        Fin.ext (by simp only [e]; omega)⟩)
    simp [encodeSlots_getElem _ _ s.isLt, hs']

/-- **The bytecode fingerprint**: the Python's `multilinear_eval(bytecode, (*low, *alphas))` is the
sum over the instance's eight entry coordinates (`entryColumn`, coordinates `3 to 10` of the bytecode
boundary blocks) of the fingerprint weight times the column's extension at `low`. Added to the
weighted separator, index and count (slots `0 to 2`), it is the instance's fingerprint of the
bytecode block at `low`. -/
theorem multilinearEval_bytecodeWords (prog : Program) (z : Vector E prog.logSize)
    (w : Vector E 4) :
    multilinearEval ((bytecodeWords prog).map ofK) (z.toList ++ w.toList) =
      ∑ k : Fin 8, (lagrangeBasis w)[k.val + 3] *
        eval₂Mle (entryColumn prog k).values (algebraMap K E) z := by
  rw [← bytecodeColumnEval_eq_entries, ← bytecodeColumn_eval, ← Vector.toList_append]
  have : (bytecodeWords prog).map ofK =
      (CMlPolynomialEval.map (algebraMap K E) (bytecodeColumn prog).values).toList := by
    simp [bytecodeWords_eq_column, CMlPolynomialEval.map, Vector.toList_map]
  rw [this, multilinearEval_eq_evalMle]
  rfl

end
end LeanVM.Protocol.EndToEnd.Front
