/-
  LeanVM.Prover.Complete.StackLayout

  The honest stack holds each committed column at its placement.
-/

module

public import LeanVM.Prover.Complete.Truth
public import LeanVM.Prover.Complete.StackOffsets
public import Statement.Prover.Columns

/-!
# The honest stack's layout

For the honest witness (`witness?`), every column with a placement is the stack's block there
(`stackBlock_witness`): a column with a block of its own is written at its block's offset
(`stackArray`), and the blocks are disjoint (`stackOffsets_spec`); a column `q_keccak` carries is
slot `s` of `q_keccak`'s block, `2^κ` words at `s·2^κ`, which is the column (`qkeccakColumn`).
Hence a claim that holds of the columns holds of the stack (`holdsOn_of_holdsIn`), and slices of a
column give the ring piece at its placement (`sliceValue_witness`). The placements are aligned
and inside the stack (`placement_witness`).
-/

@[expose] public section

namespace LeanVM.Prover

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol.Verifier

/-! ## The witness's parts -/

/-- What `witness?` builds. -/
theorem witness_spec {prog : LeanIsaProgram} {input : PublicInput} {t : Execution prog}
    {W : Witness} (hW : witness? prog input t = some W) :
    ∃ rows tabs, buildLayout (bytecodeWords prog) t.logMemorySize rows = some W.layout ∧
      W.layout.stackLog ≤ Whir.maxLogStack ∧
      W.cols = colsOf t.memory tabs W.layout.tableLogHeights ∧
      W.stack = stackArray W.layout W.cols := by
  unfold witness? at hW
  split_ifs at hW
  dsimp only at hW
  split at hW
  · rename_i steps _
    split at hW
    · rename_i layout hL
      split_ifs at hW with hlog
      split at hW
      · rename_i chunks _
        generalize rowsOf _ steps = tabs at hW
        obtain rfl := Option.some.inj hW
        exact ⟨_, tabs, hL, hlog, by dsimp only, by dsimp only⟩
      · cases hW
    · cases hW
  · cases hW

/-! ## The layout's constants -/

/-- Each table column's opcode, in global order from `NUM_GLOBAL_COLUMNS` on. -/
def columnOpcodes : List ℕ := tables.flatMap fun t ↦ List.replicate t.width t.opcode

/-- The columns with a block of their own, in `stack_blocks()`' order. -/
def blockColumns : List ℕ := stackBlocks.map (·.column)

theorem nColumns_eq : nColumns = 116 := by decide +kernel

theorem columnOpcodes_facts :
    columnOpcodes.length = 113 ∧ ∀ c < 113, columnOpcodes.getD c 0 = tableOf (c + 3) := by
  decide +kernel

theorem blockColumns_facts :
    blockColumns.Nodup ∧ (∀ c ∈ blockColumns, qkeccakSlot c = none ∧ c < 116) ∧
      blockColumns.idxOf qkeccak = 2 ∧ blockColumns.length = 52 := by
  decide +kernel

/-- Where `qkeccakSlot` puts a column: below `64` slots, an input lane at its lane, or a spare
slot's column. -/
theorem qkeccakSlot_cases : ∀ c < 116, (qkeccakSlot c).all (fun s ↦ decide (3 ≤ c ∧
    tableOf c = opKeccak ∧ globalColumnBases.getD opKeccak 0 = 48 ∧ s < 64 ∧
        ((s < keccakStateLanes ∧ c - 48 = keccakIn + s) ∨
          (qkeccakSlots ≤ s ∧ c - 48 = spareLocal (s - qkeccakSlots))))) = true := by
  decide +kernel

theorem qkeccakSlotBits_eq : qkeccakSlotBits = 6 := by decide +kernel

theorem columnKappas_eq_opcodes (κ : ℕ) (hs : List ℕ) :
    columnKappas tables κ hs =
      [κ, κ, hs.getD opKeccak 0 + qkeccakSlotBits] ++ columnOpcodes.map (hs.getD · 0) := by
  simp [columnKappas, columnOpcodes, List.map_flatMap, List.map_replicate]

theorem length_columnKappas (κ : ℕ) (hs : List ℕ) : (columnKappas tables κ hs).length = 116 := by
  rw [columnKappas_eq_opcodes]; simp [columnOpcodes_facts.1]

theorem columnKappas_getD (κ : ℕ) (hs : List ℕ) (c : ℕ) (hc : c < 116) :
    (columnKappas tables κ hs).getD c 0 =
      if c < 2 then κ else if c = 2 then hs.getD opKeccak 0 + qkeccakSlotBits
      else hs.getD (tableOf c) 0 := by
  rw [columnKappas_eq_opcodes]
  rcases (by omega : c = 0 ∨ c = 1 ∨ c = 2 ∨ 3 ≤ c) with rfl | rfl | rfl | h3
  · rfl
  · rfl
  · rfl
  · obtain ⟨d, rfl⟩ : ∃ d, c = d + 3 := ⟨c - 3, by omega⟩
    have hd : d < 113 := by omega
    have h1 : ¬ d + 3 < 2 := by omega
    have h2 : d + 3 ≠ 2 := by omega
    simp only [h1, h2, ↓reduceIte, List.getD_eq_getElem?_getD, List.cons_append, List.getElem?_cons_succ,
      List.nil_append, List.getElem?_map]
    rw [List.getElem?_eq_getElem (by rw [columnOpcodes_facts.1]; exact hd)]
    have := columnOpcodes_facts.2 d hd
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by rw [columnOpcodes_facts.1]; exact hd)]
      at this
    rw [Option.getD_some] at this
    rw [this, Option.map_some, Option.getD_some]

theorem tableOf_lt : ∀ c < 116, tableOf c < nTables := by decide +kernel

theorem paddingRow_keccak_input : ∀ i < keccakOut, (paddingRow opKeccak).getD i 0 = 0 := by
  decide +kernel

/-! ## The columns -/

theorem colsOf_getD {κ : ℕ} (img : MemoryImage κ) (tabs : Array (Array (Array K)))
    (logs : List ℕ) {c : ℕ} (hc : c < 116) :
    (colsOf img tabs logs).getD c #[] =
      if c = memory0 then Array.ofFn (n := 2 ^ κ) fun x ↦ (img x).limb 0
      else if c = memory1 then Array.ofFn (n := 2 ^ κ) fun x ↦ (img x).limb 1
      else if c = qkeccak then qkeccakColumn (tabs.getD opKeccak #[]) (logs.getD opKeccak 0)
      else tableColumn (tabs.getD (tableOf c) #[]) (paddingRow (tableOf c))
        (logs.getD (tableOf c) 0) (c - globalColumnBases.getD (tableOf c) 0) := by
  have hc' : c < nColumns := by rw [nColumns_eq]; exact hc
  have ht := tableOf_lt c hc
  simp only [colsOf, Array.getD_eq_getD_getElem?, Array.getElem?_ofFn, hc', ht, dite_true,
    Option.getD_some]

theorem size_colsOf {κ : ℕ} (img : MemoryImage κ) (tabs : Array (Array (Array K)))
    (logs : List ℕ) {c : ℕ} (hc : c < 116) :
    ((colsOf img tabs logs).getD c #[]).size = 2 ^ (columnKappas tables κ logs).getD c 0 := by
  rw [colsOf_getD img tabs logs hc, columnKappas_getD κ logs c hc]
  rcases (by omega : c = 0 ∨ c = 1 ∨ c = 2 ∨ 3 ≤ c) with rfl | rfl | rfl | h3
  · simp [memory0]
  · simp [memory0, memory1]
  · simp [memory0, memory1, qkeccak, qkeccakColumn, pow_add]
  · have h1 : ¬ c < 2 := by omega
    have h2 : c ≠ 2 := by omega
    simp [memory0, memory1, qkeccak, tableColumn, h1, h2, show c ≠ 0 by omega,
      show c ≠ 1 by omega]

/-- **A column `q_keccak` carries is its slot of `q_keccak`.** -/
theorem colsOf_slot {κ : ℕ} (img : MemoryImage κ) (tabs : Array (Array (Array K)))
    (logs : List ℕ) {c s : ℕ} (hc : c < 116) (hs : qkeccakSlot c = some s) {x : ℕ}
    (hx : x < 2 ^ logs.getD opKeccak 0) :
    ((colsOf img tabs logs).getD qkeccak #[]).getD (s * 2 ^ logs.getD opKeccak 0 + x) 0 =
      ((colsOf img tabs logs).getD c #[]).getD x 0 := by
  have hf := qkeccakSlot_cases c hc
  rw [hs] at hf
  simp only [Option.all_some, decide_eq_true_eq] at hf
  obtain ⟨h3, ht, hb, hs64, hcase⟩ := hf
  rw [colsOf_getD img tabs logs hc, colsOf_getD img tabs logs (by decide : qkeccak < 116)]
  have hn0 : c ≠ memory0 := by simp [memory0]; omega
  have hn1 : c ≠ memory1 := by simp [memory1]; omega
  have hn2 : c ≠ qkeccak := by simp [qkeccak]; omega
  simp only [hn0, hn1, hn2, ↓reduceIte, show qkeccak ≠ memory0 by decide,
    show qkeccak ≠ memory1 by decide, ht, hb]
  set h := logs.getD opKeccak 0
  set R := tabs.getD opKeccak #[]
  have hlt : s * 2 ^ h + x < 2 ^ (h + qkeccakSlotBits) := by
    rw [qkeccakSlotBits_eq, pow_add]
    have : (s + 1) * 2 ^ h ≤ 64 * 2 ^ h := Nat.mul_le_mul_right _ (by omega)
    nlinarith
  have hdiv : (s * 2 ^ h + x) / 2 ^ h = s := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by positivity), Nat.div_eq_of_lt hx, zero_add]
  have hmod : (s * 2 ^ h + x) % 2 ^ h = x := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hx]
  simp only [qkeccakColumn, tableColumn, Array.getD_eq_getD_getElem?, Array.getElem?_ofFn, hlt, hx,
    dite_true, Option.getD_some, hdiv, hmod]
  have h25 : keccakStateLanes = 25 := rfl
  have h50 : qkeccakSlots = 50 := by decide
  rcases hcase with ⟨hs25, hloc⟩ | ⟨hs50, hloc⟩
  · rw [hloc]
    simp only [hs25, ↓reduceIte]
    split_ifs
    · rfl
    · have := paddingRow_keccak_input (keccakIn + s)
        (by simp only [keccakOut, keccakStateLanes] at hs25 ⊢; omega)
      rw [Array.getD_eq_getD_getElem?] at this
      exact this.symm
  · rw [hloc]
    simp only [show ¬ s < keccakStateLanes by omega, show ¬ s < qkeccakSlots by omega,
      ↓reduceIte]

/-! ## The stack's writes -/

/-- The blocks `stackArray` writes: each column with a placement that `q_keccak` does not carry,
at its placement's index. -/
def stackWriteOf : (Option Placement × Array K) × ℕ → Option (ℕ × Array K)
  | ((placement?, col), c) =>
    match placement?, qkeccakSlot c with
    | some placement, none => some (placement.index, col)
    | _, _ => none

/-- The blocks `stackArray` writes, in global column order. -/
def stackWrites (L : Layout) (cols : Array (Array K)) : List (ℕ × Array K) :=
  (L.placements.zip cols.toList).zipIdx.filterMap stackWriteOf

theorem stackArray_eq (L : Layout) (cols : Array (Array K)) :
    stackArray L cols = writeBlocks (Array.replicate (2 ^ L.stackLog) 0) (stackWrites L cols) := by
  unfold stackArray stackWrites writeBlocks
  generalize Array.replicate (2 ^ L.stackLog) (0 : K) = A
  generalize (L.placements.zip cols.toList).zipIdx = l
  induction l generalizing A with
  | nil => rfl
  | cons x l ih =>
    obtain ⟨⟨pl, col⟩, c⟩ := x
    rcases pl with _ | pl <;> rcases hq : qkeccakSlot c with _ | s <;>
      simp only [List.foldl_cons, List.filterMap_cons, stackWriteOf, hq] <;> exact ih _

/-! ## The layout's placements -/

/-- The blocks' offsets at the column log-sizes `kappas`, in `blockColumns`' order. -/
def blockOffsets (kappas : List ℕ) : List ℕ :=
  (stackOffsets (blockColumns.map (kappas.getD · 0))).1

/-- A column's placement at the column log-sizes `kappas` (`buildLayout`). -/
def placementOf (kappas : List ℕ) (c : ℕ) : Option Placement :=
  (match qkeccakSlot c with
    | some slot =>
      ((blockColumns.zip (blockOffsets kappas)).lookup qkeccak).map (· + (slot <<< kappas.getD c 0))
    | none => (blockColumns.zip (blockOffsets kappas)).lookup c).map
    fun index ↦ ({ variableCount := kappas.getD c 0, index := index } : Placement)

theorem stack_eq (kappas : List ℕ) : stack kappas = (blockColumns.zip (blockOffsets kappas),
    max Whir.minLogStack (stackOffsets (blockColumns.map (kappas.getD · 0))).2) := by
  simp only [stack, blockColumns, blockOffsets, List.map_map]
  rfl

/-- What `buildLayout` gives. -/
theorem buildLayout_some {bc : List K} {κ : ℕ} {rows : List ℕ} {L : Layout}
    (h : buildLayout bc κ rows = some L) :
    L.logMemory = κ ∧
      L.stackLog = max Whir.minLogStack
        (stackOffsets (blockColumns.map ((columnKappas tables κ L.tableLogHeights).getD · 0))).2 ∧
      ∀ c, L.placements.getD c none =
        if c < 116 then placementOf (columnKappas tables κ L.tableLogHeights) c else none := by
  unfold buildLayout at h
  split at h
  · cases h
  · split at h
    · simp only [Option.some.injEq] at h
      subst h
      dsimp only
      have hlen := length_columnKappas κ
        (List.zipWith (fun rows floor ↦ max (log2Ceil rows) floor) rows tableLogFloors)
      generalize columnKappas tables κ _ = kappas at hlen ⊢
      simp only [stack_eq]
      refine ⟨trivial, trivial, fun c ↦ ?_⟩
      simp only [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_zipIdx, zero_add]
      by_cases hc : c < 116
      · rw [List.getElem?_eq_getElem (by omega)]
        simp only [Option.map_some, Option.getD_some, hc, ↓reduceIte, placementOf,
          List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (show c < kappas.length by omega)]
        rfl
      · rw [List.getElem?_eq_none (by omega)]
        simp [hc]
    · cases h

theorem lookup_zip_mem {l m : List ℕ} {c x : ℕ} (h : (l.zip m).lookup c = some x) :
    c ∈ l ∧ l.idxOf c < m.length ∧ x = m.getD (l.idxOf c) 0 := by
  induction l generalizing m with
  | nil => simp at h
  | cons a l ih =>
    cases m with
    | nil => simp at h
    | cons b m =>
      simp only [List.zip_cons_cons, List.lookup_cons] at h
      split at h
      · next hx =>
        have hca : c = a := beq_iff_eq.mp hx
        subst hca
        simp only [Option.some.injEq] at h
        simp [h]
      · next hx =>
        have hca : c ≠ a := fun e ↦ by simp [e] at hx
        obtain ⟨h1, h2, h3⟩ := ih h
        refine ⟨List.mem_cons_of_mem _ h1, ?_, ?_⟩
        · rw [List.idxOf_cons_ne _ (Ne.symm hca)]; simpa using h2
        · rw [List.idxOf_cons_ne _ (Ne.symm hca), h3]; simp

theorem length_blockOffsets (kappas : List ℕ) : (blockOffsets kappas).length = 52 := by
  rw [blockOffsets, (stackOffsets_spec _).1, List.length_map, blockColumns_facts.2.2.2]

/-- A block column's block: its size is the column's, it is aligned and inside the stack. -/
theorem block_facts (kappas : List ℕ) {c : ℕ} (hc : c ∈ blockColumns) :
    blockColumns.idxOf c < 52 ∧
      2 ^ kappas.getD c 0 ∣ (blockOffsets kappas).getD (blockColumns.idxOf c) 0 ∧
      (blockOffsets kappas).getD (blockColumns.idxOf c) 0 + 2 ^ kappas.getD c 0 ≤
        2 ^ max Whir.minLogStack (stackOffsets (blockColumns.map (kappas.getD · 0))).2 := by
  have hb : blockColumns.idxOf c < blockColumns.length := List.idxOf_lt_length_iff.mpr hc
  have hsz : (blockColumns.map (kappas.getD · 0)).getD (blockColumns.idxOf c) 0 = kappas.getD c 0 := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hb,
      List.getElem_idxOf hb]
    rfl
  have := (stackOffsets_spec (blockColumns.map (kappas.getD · 0))).2.1 (blockColumns.idxOf c)
    (by simpa using hb)
  rw [hsz] at this
  refine ⟨by rw [blockColumns_facts.2.2.2] at hb; exact hb, this.1, this.2.trans ?_⟩
  exact Nat.pow_le_pow_right (by norm_num) (le_max_right _ _)

/-- Two block columns' blocks do not overlap. -/
theorem block_disjoint (kappas : List ℕ) {c c' : ℕ} (hc : c ∈ blockColumns)
    (hc' : c' ∈ blockColumns) (hne : c ≠ c') :
    (blockOffsets kappas).getD (blockColumns.idxOf c) 0 + 2 ^ kappas.getD c 0 ≤
        (blockOffsets kappas).getD (blockColumns.idxOf c') 0 ∨
      (blockOffsets kappas).getD (blockColumns.idxOf c') 0 + 2 ^ kappas.getD c' 0 ≤
        (blockOffsets kappas).getD (blockColumns.idxOf c) 0 := by
  have hb : blockColumns.idxOf c < blockColumns.length := List.idxOf_lt_length_iff.mpr hc
  have hb' : blockColumns.idxOf c' < blockColumns.length := List.idxOf_lt_length_iff.mpr hc'
  have hsz : ∀ d, d ∈ blockColumns →
      (blockColumns.map (kappas.getD · 0)).getD (blockColumns.idxOf d) 0 = kappas.getD d 0 := by
    intro d hd
    have hbd : blockColumns.idxOf d < blockColumns.length := List.idxOf_lt_length_iff.mpr hd
    rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hbd,
      List.getElem_idxOf hbd]
    rfl
  have hne' : blockColumns.idxOf c ≠ blockColumns.idxOf c' := fun h ↦ hne (by
    rw [← List.getElem_idxOf hb, ← List.getElem_idxOf hb']; simp [h])
  have := (stackOffsets_spec (blockColumns.map (kappas.getD · 0))).2.2 (blockColumns.idxOf c)
    (by simpa using hb) (blockColumns.idxOf c') (by simpa using hb') hne'
  rw [hsz c hc, hsz c' hc'] at this
  exact this

/-- One of `stackArray`'s writes is a block column, at its block. -/
theorem stackWrite_facts {L : Layout} {cols : Array (Array K)} {bc : List K} {κ : ℕ}
    {rows : List ℕ} (hL : buildLayout bc κ rows = some L)
    {a : (Option Placement × Array K) × ℕ} (ha : a ∈ (L.placements.zip cols.toList).zipIdx)
    {w : ℕ × Array K}
    (hf : stackWriteOf a = some w) :
    a.2 ∈ blockColumns ∧ cols.toList[a.2]? = some w.2 ∧
      w.1 = (blockOffsets (columnKappas tables κ L.tableLogHeights)).getD (blockColumns.idxOf a.2) 0 := by
  obtain ⟨-, -, hpl⟩ := buildLayout_some hL
  obtain ⟨⟨pl?, col⟩, c⟩ := a
  rw [List.mem_zipIdx_iff_getElem?, List.getElem?_zip_eq_some] at ha
  obtain ⟨hpc, hcol⟩ := ha
  rcases pl? with _ | pl
  · simp [stackWriteOf] at hf
  rcases hq : qkeccakSlot c with _ | s
  · simp only [stackWriteOf, hq, Option.some.injEq] at hf
    subst hf
    have hp := hpl c
    rw [List.getD_eq_getElem?_getD, hpc, Option.getD_some] at hp
    split_ifs at hp
    simp only [placementOf, hq] at hp
    obtain ⟨index, hidx, rfl⟩ := Option.map_eq_some_iff.mp hp.symm
    obtain ⟨hmem, -, hx⟩ := lookup_zip_mem hidx
    exact ⟨hmem, hcol, hx⟩
  · simp [stackWriteOf, hq] at hf

theorem pairwise_stackWrites {L : Layout} {cols : Array (Array K)} {bc : List K} {κ : ℕ}
    {rows : List ℕ} (hL : buildLayout bc κ rows = some L)
    (hsize : ∀ c < 116,
      (cols.getD c #[]).size = 2 ^ (columnKappas tables κ L.tableLogHeights).getD c 0) :
    (stackWrites L cols).Pairwise BlocksDisjoint := by
  have hz : ((L.placements.zip cols.toList).zipIdx).Pairwise fun a b ↦ a.2 ≠ b.2 := by
    have := List.nodup_range' (s := 0) (n := (L.placements.zip cols.toList).length)
    rw [← List.zipIdx_map_snd] at this
    exact List.pairwise_map.mp this
  refine (List.Pairwise.and_mem.mp hz).filterMap _ ?_
  intro a a' ⟨ha, ha', hne⟩ w hf w' hf'
  obtain ⟨hm, hc, hw⟩ := stackWrite_facts hL ha hf
  obtain ⟨hm', hc', hw'⟩ := stackWrite_facts hL ha' hf'
  have hsz : ∀ d, d ∈ blockColumns → ∀ v : Array K, cols.toList[d]? = some v →
      v.size = 2 ^ (columnKappas tables κ L.tableLogHeights).getD d 0 := by
    intro d hd v hv
    have hd' := (blockColumns_facts.2.1 d hd).2
    rw [← hsize d hd', Array.getD_eq_getD_getElem?, ← Array.getElem?_toList, hv, Option.getD_some]
  have hd := block_disjoint (columnKappas tables κ L.tableLogHeights) hm hm' hne
  rw [← hw, ← hw', ← hsz _ hm _ hc, ← hsz _ hm' _ hc'] at hd
  exact hd

/-- A block read off an array word by word. -/
theorem stackBlock_eq_of_getD {S col : Array K} {p : Placement}
    (hsize : col.size = 2 ^ p.variableCount) (hin : p.index + 2 ^ p.variableCount ≤ S.size)
    (h : ∀ i < 2 ^ p.variableCount, S.getD (p.index + i) 0 = col.getD i 0) :
    stackBlock S p = col := by
  unfold stackBlock
  apply Array.ext
  · simp only [Array.size_extract, hsize]; omega
  · intro i h1 h2
    have hi : i < 2 ^ p.variableCount := by simp only [Array.size_extract] at h1; omega
    have := h i hi
    simp only [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem (by omega : p.index + i < S.size),
      Array.getElem?_eq_getElem (by omega : i < col.size), Option.getD_some] at this
    simp [Array.getElem_extract, this]

section Witness

variable {prog : LeanIsaProgram} {input : PublicInput} {t : Execution prog} {W : Witness}

/-- **The honest stack at a placement**, every fact at once: the column has the placement's
size, the placement is aligned and inside the stack, and the stack holds the column there. -/
theorem placement_witness (hW : witness? prog input t = some W) {c : ℕ} {p : Placement}
    (hp : W.layout.placements.getD c none = some p) :
    c < 116 ∧ (W.cols.getD c #[]).size = 2 ^ p.variableCount ∧ 2 ^ p.variableCount ∣ p.index ∧
      p.index + 2 ^ p.variableCount ≤ 2 ^ W.layout.stackLog ∧
      W.stack.size = 2 ^ W.layout.stackLog ∧
      ∀ i < 2 ^ p.variableCount, W.stack.getD (p.index + i) 0 = (W.cols.getD c #[]).getD i 0 := by
  obtain ⟨rows, tabs, hL, -, hcols, hstack⟩ := witness_spec hW
  obtain ⟨-, hlogeq, hpl⟩ := buildLayout_some hL
  set K := columnKappas tables t.logMemorySize W.layout.tableLogHeights with hK
  have hc : c < 116 := by
    by_contra h
    rw [hpl c] at hp
    simp [h] at hp
  have hpK : placementOf K c = some p := by rw [hpl c] at hp; simpa [hc] using hp
  have hsizeAll : ∀ d < 116, (W.cols.getD d #[]).size = 2 ^ K.getD d 0 := fun d hd ↦ by
    rw [hcols]; exact size_colsOf t.memory tabs _ hd
  have hS : W.stack.size = 2 ^ W.layout.stackLog := by
    rw [hstack, stackArray_eq, size_writeBlocks, Array.size_replicate]
  have hcolsz : W.cols.size = 116 := by rw [hcols]; simp [colsOf, nColumns_eq]
  have htoList : ∀ d < 116, W.cols.toList[d]? = some (W.cols.getD d #[]) := fun d hd ↦ by
    rw [Array.getElem?_toList, Array.getD_eq_getD_getElem?,
      Array.getElem?_eq_getElem (by omega), Option.getD_some]
  have hwrites : ∀ d < 116, ∀ q : Placement, W.layout.placements.getD d none = some q →
      qkeccakSlot d = none → (q.index, W.cols.getD d #[]) ∈ stackWrites W.layout W.cols := by
    intro d hd q hq hslot
    refine List.mem_filterMap.mpr ⟨((some q, W.cols.getD d #[]), d), ?_, by
      simp [stackWriteOf, hslot]⟩
    rw [List.mem_zipIdx_iff_getElem?, List.getElem?_zip_eq_some]
    refine ⟨?_, htoList d hd⟩
    rw [List.getD_eq_getElem?_getD] at hq
    rcases h : W.layout.placements[d]? with _ | x
    · rw [h] at hq; cases hq
    · rw [h, Option.getD_some] at hq; rw [hq]
  have hstackD : ∀ d < 116, ∀ q : Placement, W.layout.placements.getD d none = some q →
      qkeccakSlot d = none → q.index + (W.cols.getD d #[]).size ≤ 2 ^ W.layout.stackLog →
      ∀ i < (W.cols.getD d #[]).size,
        W.stack.getD (q.index + i) 0 = (W.cols.getD d #[]).getD i 0 := by
    intro d hd q hq hslot hin i hi
    rw [hstack, stackArray_eq]
    exact getD_writeBlocks _ _ (pairwise_stackWrites hL hsizeAll) _ (hwrites d hd q hq hslot)
      (by simpa using hin) i hi
  have hv : p.variableCount = K.getD c 0 := by
    unfold placementOf at hpK
    obtain ⟨index, -, rfl⟩ := Option.map_eq_some_iff.mp hpK
    rfl
  rcases hq : qkeccakSlot c with _ | s
  · simp only [placementOf, hq] at hpK
    obtain ⟨index, hidx, rfl⟩ := Option.map_eq_some_iff.mp hpK
    obtain ⟨hmem, -, hx⟩ := lookup_zip_mem hidx
    obtain ⟨-, hdvd, hin⟩ := block_facts K hmem
    rw [← hlogeq] at hin
    dsimp only
    rw [← hx] at hdvd hin
    refine ⟨hc, hsizeAll c hc, hdvd, hin, hS, fun i hi ↦ ?_⟩
    exact hstackD c hc _ hp hq (by rw [hsizeAll c hc]; exact hin) i (by rw [hsizeAll c hc]; exact hi)
  · simp only [placementOf, hq] at hpK
    obtain ⟨index, hidx, rfl⟩ := Option.map_eq_some_iff.mp hpK
    obtain ⟨o, ho, rfl⟩ := Option.map_eq_some_iff.mp hidx
    obtain ⟨hmem, -, hx⟩ := lookup_zip_mem ho
    have hqmem : qkeccak ∈ blockColumns := hmem
    obtain ⟨-, hdvd, hin⟩ := block_facts K hqmem
    rw [← hlogeq, ← hx] at hin
    rw [← hx] at hdvd
    have hf := qkeccakSlot_cases c hc
    rw [hq] at hf
    simp only [Option.all_some, decide_eq_true_eq] at hf
    obtain ⟨h3, ht, -, hs64, -⟩ := hf
    set h := W.layout.tableLogHeights.getD opKeccak 0
    have hKc : K.getD c 0 = h := by
      rw [hK, columnKappas_getD _ _ c hc]
      simp only [show ¬ c < 2 by omega, show c ≠ 2 by omega, ↓reduceIte, ht, h]
    have hKq : K.getD qkeccak 0 = h + 6 := by
      rw [hK, columnKappas_getD _ _ qkeccak (by decide), qkeccakSlotBits_eq]; rfl
    rw [hKq] at hdvd hin
    dsimp only
    rw [hKc, Nat.shiftLeft_eq]
    have h64 : (s + 1) * 2 ^ h ≤ 2 ^ (h + 6) := by
      rw [pow_add, mul_comm (2 ^ h)]; exact Nat.mul_le_mul_right _ (by norm_num; omega)
    have hqp : W.layout.placements.getD qkeccak none = some ⟨K.getD qkeccak 0, o⟩ := by
      rw [hpl qkeccak]
      simp only [show qkeccak < 116 by decide, ↓reduceIte, placementOf, show qkeccakSlot qkeccak = none by decide, ho, Option.map_some]
    refine ⟨hc, by rw [hsizeAll c hc, hKc], ?_, ?_, hS, fun i hi ↦ ?_⟩
    · exact Nat.dvd_add ((Nat.pow_dvd_pow 2 (by omega)).trans hdvd) (dvd_mul_left _ _)
    · nlinarith
    · have hqsize : (W.cols.getD qkeccak #[]).size = 2 ^ (h + 6) := by
        rw [hsizeAll qkeccak (by decide), hKq]
      have := hstackD qkeccak (by decide) _ hqp (by decide) (by rw [hqsize]; exact hin)
        (s * 2 ^ h + i) (by rw [hqsize]; nlinarith)
      rw [Nat.add_assoc, this, hcols]
      exact colsOf_slot t.memory tabs _ hc hq hi

/-- **The stack's block at a column's placement is the column.** -/
theorem stackBlock_witness (hW : witness? prog input t = some W) {c : ℕ} {p : Placement}
    (hp : W.layout.placements.getD c none = some p) :
    stackBlock W.stack p = W.cols.getD c #[] := by
  obtain ⟨-, hsize, -, hin, hS, hget⟩ := placement_witness hW hp
  exact stackBlock_eq_of_getD hsize (by rw [hS]; exact hin) hget

/-- **A column claim that holds of the columns holds of the stack.** -/
theorem holdsOn_of_holdsIn (hW : witness? prog input t = some W) {cl : ColumnClaim}
    (h : cl.HoldsIn W.cols) : cl.HoldsOn W.layout W.stack := by
  intro p hp
  rw [stackBlock_witness hW hp]
  exact h

/-- **Slices of a column give the ring piece at its placement.** -/
theorem sliceValue_witness (hW : witness? prog input t = some W) {c : ℕ} {p : Placement}
    (hp : W.layout.placements.getD c none = some p) {point slices : List E}
    (hs : SlicesHoldIn (W.cols.getD c #[]) point slices) (scale : E) {i : ℕ} (hi : i < 64) :
    RingPiece.sliceValue W.stack ⟨some p, point, scale⟩ i = scale * slices.getD i 0 := by
  simp only [RingPiece.sliceValue, RingPiece.column, stackBlock_witness hW hp, hs.2 i hi]

/-- **The Keccak reduction's ring claim holds of the stack** when its slices hold of
`q_keccak`. -/
theorem keccakRingClaim_holdsOn (hW : witness? prog input t = some W) {p : Placement}
    (hp : W.layout.placements.getD qkeccak none = some p) {point slices : List E}
    (hs : SlicesHoldIn (W.cols.getD qkeccak #[]) point slices) :
    (keccakRingClaim p point slices).HoldsOn W.stack := by
  refine ⟨hs.1, fun i hi ↦ ?_⟩
  simp only [keccakRingClaim, List.map_cons, List.map_nil, sumE, List.foldl_cons, List.foldl_nil,
    zero_add]
  rw [sliceValue_witness hW hp hs 1 hi, one_mul]

/-- **The link's memory term holds of the stack** when it holds of the two memory columns. -/
theorem memoryHoldsOn_witness (hW : witness? prog input t = some W) {link : LinkEnd}
    (hmem : link.memoryValue =
      link.memoryScales.1 * mleK (W.cols.getD memory0 #[]) link.memoryPoint +
        link.memoryScales.2 * mleK (W.cols.getD memory1 #[]) link.memoryPoint) :
    link.MemoryHoldsOn W.layout W.stack := by
  intro p0 p1 h0 h1
  rw [stackBlock_witness hW h0, stackBlock_witness hW h1]
  exact hmem

end Witness

end LeanVM.Prover

end
