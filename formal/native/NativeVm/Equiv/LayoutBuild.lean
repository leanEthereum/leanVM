module

public import NativeVm.Equiv.StackOffsets
public import NativeVm.Equiv.LayoutSpec
public import NativeVm.Equiv.Field

/-!
# `build_layout`: the model's is the statement's

`buildLayout_toSpec`: the model's `buildLayout` (`NativeVm/Model/Layout.lean`) is the statement's
through `LayoutW.toSpec`, `none` where it is `none`. Its parts:

* the constant tables: `tablesW` is `tables` with every form's coefficients as lanes
  (`tablesW_toList`, `FormW.toForm_ofForm`), each table at its opcode (`zip_tables`, the tables'
  opcodes being their indices, read off the list's structure, no table evaluated), and the tabulated
  `keccakSlot` and `keccakOutputColumns` read as the functions inside the global columns
  (`keccakSlotTable_get`, `keccakOutputTable_get`; `columnCount_eq`);
* `columnKappas_toSpec`, `busBlocks_toSpec`;
* `placementsOf_toSpec`: the block columns are the statement's, laid by `stackOffsets_toSpec`, and
  the offsets the model scatters into an array by column (`offsets_getD`, by `foldl_set_getD`) are
  the statement's offsets looked up by the column's place among the block columns.
-/

@[expose] public section

namespace NativeVm.Model

open LeanVM.Protocol.Verifier NativeVm.Equiv

/-- `N_TABLES`. -/
theorem nTables_eq : nTables = tables.length := rfl

/-- The tables zipped with one entry each, by position, are each table with its opcode's entry:
a table's opcode is its index. -/
theorem zip_tables {β γ : Type} (hs : List β) (ns : List γ) (dh : β) (dn : γ)
    (h1 : hs.length = 6) (h2 : ns.length = 6) :
    List.zip tables (List.zip hs ns) =
      tables.map fun t ↦ (t, hs.getD t.opcode dh, ns.getD t.opcode dn) := by
  match hs, ns, h1, h2 with
  | [_, _, _, _, _, _], [_, _, _, _, _, _], _, _ => rfl

/-- `tablesW`: the statement's tables as data. -/
theorem tablesW_toList : tablesW.toList = tables.map TableW.ofTable := by simp [tablesW]

/-- The global columns. -/
theorem columnCount_eq : columnCount = globalColumnCount + (tables.map Table.width).sum := rfl

/-- `keccakSlotTable` reads `keccakSlot` inside the global columns. -/
theorem keccakSlotTable_get {c : ℕ} (h : c < columnCount) :
    (keccakSlotTable[c]?).getD none = keccakSlot c := by
  simp [keccakSlotTable, h]

/-- `keccakOutputTable` reads membership of `keccakOutputColumns` inside the global columns. -/
theorem keccakOutputTable_get {c : ℕ} (h : c < columnCount) :
    (keccakOutputTable[c]?).getD false = decide (c ∈ keccakOutputColumns) := by
  simp [keccakOutputTable, h]

/-- Values set at distinct positions in turn: each position holds its own value. -/
theorem foldl_set_getD (cols offs acc : List ℕ) (hnd : cols.Nodup)
    (hlt : ∀ c ∈ cols, c < acc.length)
    (hlen : offs.length = cols.length) (c : ℕ) :
    ((cols.zip offs).foldl (fun acc p ↦ acc.set p.1 p.2) acc).getD c 0 =
      if c ∈ cols then offs.getD (cols.idxOf c) 0 else acc.getD c 0 := by
  induction cols generalizing offs acc with
  | nil => simp
  | cons c0 cs ih =>
    obtain _ | ⟨o0, os⟩ := offs
    · simp at hlen
    simp only [List.zip_cons_cons, List.foldl_cons]
    rw [List.nodup_cons] at hnd
    rw [ih os _ hnd.2 (fun c hc ↦ by simpa using hlt c (by simp [hc])) (by simpa using hlen)]
    by_cases hc : c = c0
    · subst hc
      have := hlt c (by simp)
      simp [hnd.1, List.getD_eq_getElem?_getD, this]
    · simp [hc, List.idxOf_cons_ne _ (Ne.symm hc), List.getD_eq_getElem?_getD, Ne.symm hc]

theorem length_stackOffsets (sizes : List ℕ) :
    (LeanVM.Protocol.Verifier.stackOffsets sizes).1.length = sizes.length := by
  unfold LeanVM.Protocol.Verifier.stackOffsets
  suffices ∀ (sz : ℕ → ℕ) (order : List ℕ) (acc : List ℕ × ℕ),
      (order.foldl (fun (acc : List ℕ × ℕ) i ↦ (acc.1.set i acc.2, acc.2 + 2 ^ sz i))
        acc).1.length = acc.1.length from
    (this _ _ _).trans (List.length_replicate ..)
  intro sz order
  induction order with
  | nil => intro; rfl
  | cons i order ih => intro acc; rw [List.foldl_cons, ih, List.length_set]

/-- The offsets array the model lays out reads, at every column, the statement's offset. -/
theorem offsets_getD (n : ℕ) (bw ow : Array ℕ) (os : List ℕ) (h1 : ow.toList = os)
    (hnd : bw.toList.Nodup) (hlt : ∀ c ∈ bw.toList, c < n) (hlen : os.length = bw.size) (c : ℕ) :
    (Array.foldl (fun acc (x : ℕ × ℕ) ↦ acc.set! x.1 x.2) (Array.replicate n 0)
      (bw.zip ow)).getD c 0 =
      os.getD (bw.toList.idxOf c) 0 := by
  rw [← Array.foldl_toList, Array.getD_eq_getD_getElem?, ← Array.getElem?_toList,
    ← List.getD_eq_getElem?_getD]
  have := foldl_hom Array.toList id (f := fun acc (x : ℕ × ℕ) ↦ acc.set! x.1 x.2)
    (g := fun acc x ↦ acc.set x.1 x.2) (fun a b ↦ by simp) (bw.zip ow).toList (Array.replicate n 0)
  rw [List.map_id] at this
  rw [this, Array.toList_zip, h1,
    foldl_set_getD _ _ _ hnd (by simpa using hlt) (by simpa using hlen)]
  split
  · rfl
  · rename_i hc
    have h0 : os.getD bw.toList.length 0 = 0 := by simp [List.getD_eq_getElem?_getD, hlen]
    rw [List.idxOf_eq_length hc, h0, Array.toList_replicate]
    rcases Nat.lt_or_ge c n with hcn | hcn <;>
      simp [List.getD_eq_getElem?_getD, hcn]

/-- `placementsOf`, on a column count within the global columns. -/
theorem placementsOf_toSpec (kappas : Array ℕ) (h : kappas.size ≤ columnCount) :
    (placementsOf kappas).1.toList = (LeanVM.Protocol.Verifier.placementsOf kappas.toList).1 ∧
      (placementsOf kappas).2 = (LeanVM.Protocol.Verifier.placementsOf kappas.toList).2 := by
  have hsize : kappas.toList.length = kappas.size := Array.length_toList
  have hb : (Array.filter (fun c ↦ (keccakSlotTable[c]?.getD none).isNone &&
        !keccakOutputTable[c]?.getD false) (Array.range kappas.size)).toList =
      List.filter (fun c ↦ decide ((keccakSlot c).isNone = true ∧ c ∉ keccakOutputColumns))
        (List.range kappas.toList.length) := by
    rw [Array.toList_filter, Array.toList_range, hsize]
    refine List.filter_congr fun c hc ↦ ?_
    have hc' : c < columnCount := by simp at hc; omega
    rw [keccakSlotTable_get hc', keccakOutputTable_get hc']
    cases keccakSlot c <;> simp
  have hnd : (List.filter (fun c ↦ decide ((keccakSlot c).isNone = true ∧
      c ∉ keccakOutputColumns)) (List.range kappas.toList.length)).Nodup :=
    List.nodup_range.filter _
  have hlt : ∀ c ∈ List.filter (fun c ↦ decide ((keccakSlot c).isNone = true ∧
      c ∉ keccakOutputColumns)) (List.range kappas.toList.length), c < kappas.size := by
    intro c hc; have := (List.mem_filter.1 hc).1; simp at this; omega
  unfold placementsOf LeanVM.Protocol.Verifier.placementsOf
  simp only []
  generalize Array.filter (fun c ↦ (keccakSlotTable[c]?.getD none).isNone &&
        !keccakOutputTable[c]?.getD false) (Array.range kappas.size) = bw at hb ⊢
  generalize List.filter (fun c ↦ decide ((keccakSlot c).isNone = true ∧ c ∉ keccakOutputColumns))
    (List.range kappas.toList.length) = bs at hb hnd hlt ⊢
  subst hb
  obtain ⟨h1, h2⟩ := stackOffsets_toSpec (bw.map fun x ↦ kappas.getD x 0)
  have hlen := length_stackOffsets (bw.toList.map fun x ↦ kappas.toList.getD x 0)
  have hm : (bw.map fun x ↦ kappas.getD x 0).toList =
      bw.toList.map fun x ↦ kappas.toList.getD x 0 := by
    simp [List.getD_eq_getElem?_getD]
  rw [hm] at h1 h2
  rw [List.length_map, Array.length_toList] at hlen
  generalize stackOffsets (bw.map fun x ↦ kappas.getD x 0) = sw at h1 h2 ⊢
  generalize LeanVM.Protocol.Verifier.stackOffsets
    (bw.toList.map fun x ↦ kappas.toList.getD x 0) = ss at h1 h2 hlen ⊢
  obtain ⟨ow, tw⟩ := sw
  obtain ⟨os, ts⟩ := ss
  simp only at h1 h2 hlen ⊢
  refine ⟨?_, by rw [h2]⟩
  simp only [offsets_getD kappas.size bw ow os h1 hnd hlt hlen, Array.toList_map,
    Array.toList_zipIdx]
  refine List.map_congr_left fun x hx ↦ ?_
  have hx' : x.2 < columnCount := by
    have := List.snd_lt_of_mem_zipIdx hx; simp at this; omega
  rw [keccakSlotTable_get hx', keccakOutputTable_get hx']
  rcases keccakSlot x.2 with _ | s
  · by_cases hm : x.2 ∈ keccakOutputColumns <;> simp [hm, List.getD_eq_getElem?_getD]
  · simp [List.getD_eq_getElem?_getD]

/-- A form of the statement as lanes, read back. -/
theorem FormW.toForm_ofForm (f : Form) : (FormW.ofForm f).toForm = f := by
  rcases f with ⟨terms⟩
  simp [FormW.ofForm, FormW.toForm, TermW.toSpec, Function.comp_def]

/-- `columnKappas`. -/
theorem columnKappas_toSpec (logMemory logBytecode : ℕ) (heights : Array ℕ) :
    (columnKappas logMemory logBytecode heights).toList =
      LeanVM.Protocol.Verifier.columnKappas logMemory logBytecode heights.toList := by
  simp [columnKappas, LeanVM.Protocol.Verifier.columnKappas, tablesW_toList, Array.toList_flatMap,
    List.flatMap_map, TableW.ofTable, List.getD_eq_getElem?_getD, Table.width]

/-- `busBlocks`, on six heights and row counts. -/
theorem busBlocks_toSpec (heights rows : Array ℕ) (hh : heights.size = 6) (hr : rows.size = 6) :
    (busBlocks heights rows).1.toList.map BusBlockW.toSpec =
        (LeanVM.Protocol.Verifier.busBlocks heights.toList rows.toList).1 ∧
      (busBlocks heights rows).2.1.toList.map BusBlockW.toSpec =
        (LeanVM.Protocol.Verifier.busBlocks heights.toList rows.toList).2.1 ∧
      (busBlocks heights rows).2.2.toList.map BusBlockW.toSpec =
        (LeanVM.Protocol.Verifier.busBlocks heights.toList rows.toList).2.2 := by
  unfold busBlocks LeanVM.Protocol.Verifier.busBlocks
  rw [zip_tables heights.toList rows.toList 0 0 (by simpa using hh) (by simpa using hr)]
  simp [tablesW_toList, Array.toList_flatMap, List.flatMap_map, List.map_flatMap, TableW.ofTable,
    BusBlockW.toSpec, Function.comp_def, FormW.toForm_ofForm, List.getD_eq_getElem?_getD]

/-- The columns' log-sizes are one per global column. -/
theorem columnKappas_size (logMemory logBytecode : ℕ) (heights : Array ℕ) :
    (columnKappas logMemory logBytecode heights).size = columnCount := by
  rw [← Array.length_toList, columnKappas_toSpec, columnCount_eq]
  simp [LeanVM.Protocol.Verifier.columnKappas, List.length_flatMap, globalColumnCount,
    Table.width]
  rw [show (fun a : Table ↦ a.columns.length) = Table.width from rfl]
  omega

/-- **`buildLayout`** is the statement's, through `LayoutW.toSpec`. -/
theorem buildLayout_toSpec (bytecode : Array UInt64) (logMemory : ℕ) (tableRows : Array ℕ) :
    (buildLayout bytecode logMemory tableRows).map LayoutW.toSpec =
      LeanVM.Protocol.Verifier.buildLayout (bytecode.toList.map LeanVM.Parameters.K.ofLane)
        logMemory tableRows.toList := by
  unfold buildLayout LeanVM.Protocol.Verifier.buildLayout
  rw [List.length_map, Array.length_toList]
  rcases log2Strict bytecode.size with _ | logLength
  · rfl
  simp only []
  have hcond : (busBits ≤ logLength ∧ 1 ≤ logMemory ∧ logMemory ≤ 30 ∧
      tableRows.all (· ≤ 2 ^ 30) ∧ logLength - busBits ≤ 30 ∧ tableRows.size = nTables) ↔
      (busBits ≤ logLength ∧ 1 ≤ logMemory ∧ logMemory ≤ 30 ∧
      tableRows.toList.all (· ≤ 2 ^ 30) ∧ logLength - busBits ≤ 30 ∧
      tableRows.toList.length = tables.length) := by
    simp [nTables_eq]
  by_cases hc : busBits ≤ logLength ∧ 1 ≤ logMemory ∧ logMemory ≤ 30 ∧
      tableRows.all (· ≤ 2 ^ 30) ∧ logLength - busBits ≤ 30 ∧ tableRows.size = nTables
  · have hc' := hcond.1 hc
    split_ifs
    have hrows : tableRows.size = 6 := hc.2.2.2.2.2
    have hh : (Array.zipWith (fun rows floor ↦ max (log2Ceil rows) floor) tableRows
        tableLogFloors.toArray).toList =
        List.zipWith (fun rows floor ↦ max (log2Ceil rows) floor) tableRows.toList
          tableLogFloors := by
      simp [Array.toList_zipWith]
    have hhs : (Array.zipWith (fun rows floor ↦ max (log2Ceil rows) floor) tableRows
        tableLogFloors.toArray).size = 6 := by
      simp [hrows, tableLogFloors]
    obtain ⟨hb1, hb2, hb3⟩ := busBlocks_toSpec _ _ hhs hrows
    obtain ⟨hp1, hp2⟩ := placementsOf_toSpec (columnKappas logMemory (logLength - busBits)
      (Array.zipWith (fun rows floor ↦ max (log2Ceil rows) floor) tableRows tableLogFloors.toArray))
      (columnKappas_size .. ).le
    rw [columnKappas_toSpec, hh] at hp1 hp2
    rw [hh] at hb1 hb2 hb3
    simp only [Option.map_some, LayoutW.toSpec, hb1, hb2, hb3, hp1, hp2, hh]
  · have hc' := mt hcond.2 hc
    split_ifs
    rfl

end NativeVm.Model
