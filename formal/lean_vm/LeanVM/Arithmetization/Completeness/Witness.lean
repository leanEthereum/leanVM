/-
  LeanVM.Arithmetization.Completeness.Witness

  The witness of a list of skeletons: the prover data of an image, the eight tables, and what the
  bus carries.
-/

module

public import LeanVM.Arithmetization.Completeness.Bus

@[expose] public section

/-!
# The witness of a list of skeletons

Given the program, the public input, the image `img` and a list of skeletons `S` (the states stepped
from and the instructions fetched there: the run's), `skelWitness prog input img S` is Clean's
`EnsembleWitness` of the leanISA ensemble:

* the six opcode tables hold the rows of the skeletons of their opcode (`opTable`): `skelRows img S`
  are the rows of `S` with their counts, threaded through `S` (`Completeness.Bus`), and a table
  holds those whose instruction has its opcode;
* the memory block holds one row per cell, `(the word at i, g^i, g^(finalizes of i))`, and the
  bytecode block one row per slot of the program, with the finalize counts the reads leave; both
  agree with their fixed columns (`memBlock`, `bcBlock`);
* the prover data is Clean's, derived from the tables (`Air.Flat.withDerivedData`): its `"mem"`
  table is the memory block's limbs, so the image it names is `img` (`imageOf_skelWitness`).

The tables are built while `κ ≤ maxLogMem` and every opcode has at most `2^maxLogRows` rows (the
hypotheses `hκ` and `hrows`), which bound every table by `UInt64.size` rows (Clean's `length_le`).

What the bus carries (`skelWitness_sends`, `messagesOn_skelWitness` in `Completeness.Satisfied`) is
the verifier's two messages, then each table's, in the ensemble's order, as the list of
`(channel, message)` pairs the rows send. The witness is never evaluated: the memory block has
`2^κ` rows, and every statement about it is about its rows generically.

## Wrong readings excluded

* The tables are filtered from one list of rows, not built one at a time: the numbers of a cell's
  reads run across all six tables, so that the memory pair balances (`Completeness.Balance`).
* The memory block's finalize count of a cell is `g` to the number of reads of it, never the
  number: `cntFin = g^(readBump …)`, the count a read of the cell would carry next.
-/

namespace LeanVM.Arithmetization

open LeanVM.Parameters LeanVM.Semantics
open Air.Flat (Component EnsembleWitness)

/-! ## The image a `"mem"` table names -/

/-- The `"mem"` table of an image: its words, one row of three limbs each. -/
def imageRows {κ : ℕ} (img : MemoryImage κ) : Array (Vector K 3) :=
  Array.ofFn fun i : Fin (2 ^ κ) ↦ #v[(img i).limb 0, (img i).limb 1, (img i).limb 2]

section Image

variable {κ : ℕ} {img : MemoryImage κ} {data : ProverData K}

/-- The memory log-size data names is the image's, when its `"mem"` table is the image's. -/
theorem imageOf_fst_of_memRows (h : memRows data = imageRows img) (hκ : κ ≤ maxLogMem) :
    (imageOf data).1 = κ := by
  show min (Nat.log 2 (memRows data).size) maxLogMem = κ
  rw [h, imageRows, Array.size_ofFn, Nat.log_pow (by norm_num)]
  exact Nat.min_eq_left hκ

/-- Such data is well shaped. -/
theorem wellShaped_of_memRows (h : memRows data = imageRows img) (hκ : κ ≤ maxLogMem) :
    WellShapedData data :=
  ⟨by rw [imageOf_fst_of_memRows h hκ, h, imageRows, Array.size_ofFn]⟩

/-- Row `k` of the table, through `getElem?`: a `getElem` with a bound on the `2^κ`-row table
makes both the elaborator and the kernel unroll it. -/
theorem memRows_row_of (h : memRows data = imageRows img) (k : ℕ) (hk : k < 2 ^ κ) :
    (memRows data)[k]? =
      some #v[(img ⟨k, hk⟩).limb 0, (img ⟨k, hk⟩).limb 1, (img ⟨k, hk⟩).limb 2] := by
  rw [h, imageRows, Array.getElem?_ofFn, dite_eq_left hk]

/-- Every word such data names is the image's. -/
theorem imageOf_apply_of_memRows (h : memRows data = imageRows img) (hκ : κ ≤ maxLogMem) (k : ℕ)
    (hk : k < 2 ^ (imageOf data).1) :
    (imageOf data).2 ⟨k, hk⟩ =
      img ⟨k, by rw [imageOf_fst_of_memRows h hκ] at hk; exact hk⟩ := by
  have hk' : k < 2 ^ κ := by rw [imageOf_fst_of_memRows h hκ] at hk; exact hk
  conv_rhs => rw [← ofLimbs_limb (img ⟨k, hk'⟩)]
  refine imageOf_apply (wellShaped_of_memRows h hκ) ⟨k, hk⟩
    (v := #v[(img ⟨k, hk'⟩).limb 0, (img ⟨k, hk'⟩).limb 1, (img ⟨k, hk'⟩).limb 2]) ?_
  rw [Array.getElem_eq_iff]
  exact memRows_row_of h k hk'

/-- The image such data names, as one equality of dependent pairs: what every conjunct over
`imageOf w.data` is rewritten with, so that nothing compares the data's log-size against `κ`
definitionally (which would unroll the `2^κ` rows). -/
theorem imageOf_of_memRows (h : memRows data = imageRows img) (hκ : κ ≤ maxLogMem) :
    imageOf data = ⟨κ, img⟩ := by
  have hκ' : (imageOf data).1 = κ := imageOf_fst_of_memRows h hκ
  have hpow : 2 ^ (imageOf data).1 = 2 ^ κ := by rw [hκ']
  have hf : ∀ i, (imageOf data).2 i = img (Fin.cast hpow i) := fun i ↦
    imageOf_apply_of_memRows h hκ i i.isLt
  revert hκ' hpow hf
  generalize imageOf data = s
  obtain ⟨κ', img'⟩ := s
  intro hκ' hpow hf
  dsimp only at hκ' hpow hf
  subst hκ'
  exact congrArg _ (funext fun i ↦ (hf i).trans (congrArg img (Fin.ext rfl)))

end Image

/-! ## The rows of a list of skeletons -/

/-- The rows of a list of skeletons over the image `img`, numbered from zero. -/
noncomputable def skelRows {κ : ℕ} (img : MemoryImage κ) (S : List Skel) : List PRow :=
  mkRows img (fun _ ↦ 0) (fun _ ↦ 0) S

/-- How many times each memory cell is read by the rows of `S`: the exponent of its finalize
count. -/
noncomputable def skelMemFin {κ : ℕ} (img : MemoryImage κ) (S : List Skel) : K → ℕ :=
  readBump (fun _ ↦ 0) (S.flatMap fun sk ↦ readAddrs img sk.fp sk.ins)

/-- How many times each bytecode slot is read by the rows of `S`. -/
noncomputable def skelBcFin (S : List Skel) : K → ℕ :=
  readBump (fun _ ↦ 0) (S.map (·.pc))

/-- A row of the rows of `S` is a row of a skeleton of `S`. -/
theorem mem_mkRows_sk {κ : ℕ} {img : MemoryImage κ} {sm sb : K → ℕ} {S : List Skel} {r : PRow}
    (h : r ∈ mkRows img sm sb S) : r.sk ∈ S := by
  rw [← mkRows_sk img sm sb S]
  exact List.mem_map_of_mem h

/-- The rows of a table of the witness are the skeletons of its opcode. -/
theorem length_filter_mkRows {κ : ℕ} (img : MemoryImage κ) (sm sb : K → ℕ) (S : List Skel)
    (op : Opcode) :
    ((mkRows img sm sb S).filter fun r ↦ r.sk.ins.opcode = op).length = Skel.count op S := by
  unfold Skel.count Skel.onTable
  conv_rhs => rw [← mkRows_sk img sm sb S]
  rw [List.filter_map, List.length_map]
  rfl

/-! ## The tables -/

/-- A table of the component `c` holding `rows`, whose prover data is its own inputs: the form
Clean's `Air.Flat.withDerivedData` takes, which replaces the data by the whole witness's. -/
def ownTable (c : Component K) (rows : List (Array K)) (hw : ∀ row ∈ rows, row.size = c.width)
    (hlen : rows.length ≤ UInt64.size) (hfix : c.FixedRowsMatch rows) : Air.Flat.Table K where
  component := c
  table := rows
  data name n :=
    if c.circuit.name = name then (rows.map (Air.Flat.rowPrefix n)).toArray else #[]
  uniform_width := hw
  length_le := hlen
  fixed_rows_match := hfix
  data_consistent := by simp

/-- An opcode's table has the width of its raw rows. -/
theorem opComponent_width (op : Opcode) : (opComponent op).width = opWidth op := by
  cases op <;> rfl

/-- `2^maxLogRows` rows fit the `u64` row indices. -/
theorem pow_maxLogRows_le : 2 ^ maxLogRows ≤ UInt64.size := by decide

/-- The raw rows of the rows of `R` whose instruction has the opcode. -/
noncomputable def opRows {κ : ℕ} (img : MemoryImage κ) (R : List PRow) (op : Opcode) :
    List (Array K) :=
  (R.filter fun r ↦ r.sk.ins.opcode = op).map (PRow.raw img)

/-- The table of an opcode: the raw rows of the rows of `R` whose instruction has the opcode,
at most `2^maxLogRows` of them. -/
noncomputable def opTable {κ : ℕ} (img : MemoryImage κ) (R : List PRow) (op : Opcode)
    (hrows : (opRows img R op).length ≤ 2 ^ maxLogRows) : Air.Flat.Table K :=
  ownTable (opComponent op) (opRows img R op)
    (by
      intro row hrow
      obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hrow
      have h := (List.mem_filter.mp hr).2
      simp only [decide_eq_true_eq] at h
      simp only [PRow.raw, rowOf_size, h, opComponent_width])
    (hrows.trans pow_maxLogRows_le)
    (by cases op <;> trivial)

/-- A raw row cut at its type's width is the row. -/
theorem rowPrefix_rawRow {Row : TypeMap} [ProvableType Row] (r : Row K) :
    Air.Flat.rowPrefix (size Row) (rawRow r) = toElements r := by
  exact Vector.toArray_inj.mp (rowPrefix_toArray (rawRow_size r))

/-- A raw row read back at its type is the row. -/
theorem fromElements_rowPrefix_rawRow {Row : TypeMap} [ProvableType Row] (r : Row K) :
    (fromElements (Air.Flat.rowPrefix (size Row) (rawRow r)) : Row K) = r := by
  rw [rowPrefix_rawRow, ProvableType.fromElements_toElements]

/-- The memory block's rows: one per cell, `(the word at i, g^i, g^(fin (g^i)))`. -/
noncomputable def memBlockRaw {κ : ℕ} (img : MemoryImage κ) (fin : K → ℕ) : List (Array K) :=
  List.ofFn fun i : Fin (2 ^ κ) ↦ rawRow (memRowOf img i (g ^ fin (addressOfIndex i)))

/-- The memory block's rows agree with its fixed index column. -/
theorem memBlockRaw_fixed {κ : ℕ} (img : MemoryImage κ) (fin : K → ℕ) (hκ : κ ≤ maxLogMem) :
    (memComponent κ).FixedRowsMatch (memBlockRaw img fin) := by
  show (memBlockRaw img fin).length = (UInt64.ofNat (2 ^ κ)).toNat ∧
    ∀ i (hi : i < (memBlockRaw img fin).length), (memMode κ).FixedAt (UInt64.ofNat i)
      (fromElements (Air.Flat.rowPrefix (size MemRow) (memBlockRaw img fin)[i]))
  have h64 : 2 ^ κ < 2 ^ 64 := Nat.pow_lt_pow_right (by norm_num) (lt_of_le_of_lt hκ (by decide))
  refine ⟨by rw [memBlockRaw, List.length_ofFn, UInt64.toNat_ofNat_of_lt' h64], fun i hi ↦ ?_⟩
  have hi' : i < 2 ^ κ := by rwa [memBlockRaw, List.length_ofFn] at hi
  have hnat : (UInt64.ofNat i).toNat = i := UInt64.toNat_ofNat_of_lt' (lt_trans hi' h64)
  refine (memMode_fixedAt (by rw [hnat]; exact hi') _).mpr ?_
  rw [List.getElem_of_eq (memBlockRaw.eq_1 img fin) hi, List.getElem_ofFn,
    fromElements_rowPrefix_rawRow, hnat]
  rfl

/-- The memory block, of a memory within the address space: its index column fixed. -/
noncomputable def memBlock {κ : ℕ} (img : MemoryImage κ) (fin : K → ℕ) (hκ : κ ≤ maxLogMem) :
    Air.Flat.Table K :=
  ownTable (memComponent κ) (memBlockRaw img fin)
    (by
      intro r hr
      rw [memBlockRaw, List.mem_ofFn] at hr
      obtain ⟨i, rfl⟩ := hr
      exact rawRow_size _)
    (by
      rw [memBlockRaw, List.length_ofFn]
      exact (Nat.pow_le_pow_right (by norm_num) (hκ.trans (by decide))).trans pow_maxLogRows_le)
    (memBlockRaw_fixed img fin hκ)

/-- The bytecode block's rows: one per slot of the program. -/
noncomputable def bcBlockRaw (prog : LeanIsaProgram) (fin : K → ℕ) : List (Array K) :=
  List.ofFn fun i : Fin (2 ^ prog.logSize) ↦
    rawRow (bytecodeRowOf prog i (g ^ fin (addressOfIndex i)))

/-- The bytecode block's rows agree with its fixed counter and entry columns. -/
theorem bcBlockRaw_fixed (prog : LeanIsaProgram) (fin : K → ℕ) :
    (bytecodeComponent prog).FixedRowsMatch (bcBlockRaw prog fin) := by
  show (bcBlockRaw prog fin).length = (UInt64.ofNat (2 ^ prog.logSize)).toNat ∧
    ∀ i (hi : i < (bcBlockRaw prog fin).length), (bytecodeMode prog).FixedAt (UInt64.ofNat i)
      (fromElements (Air.Flat.rowPrefix (size BytecodeRow) (bcBlockRaw prog fin)[i]))
  have h64 : 2 ^ prog.logSize < 2 ^ 64 :=
    Nat.pow_lt_pow_right (by norm_num) (lt_of_le_of_lt prog.logSize_le (by decide))
  refine ⟨by rw [bcBlockRaw, List.length_ofFn, UInt64.toNat_ofNat_of_lt' h64], fun i hi ↦ ?_⟩
  have hi' : i < 2 ^ prog.logSize := by rwa [bcBlockRaw, List.length_ofFn] at hi
  have hnat : (UInt64.ofNat i).toNat = i := UInt64.toNat_ofNat_of_lt' (lt_trans hi' h64)
  refine (bytecodeMode_fixedAt prog (by rw [hnat]; exact hi') _).mpr ?_
  rw [List.getElem_of_eq (bcBlockRaw.eq_1 prog fin) hi, List.getElem_ofFn,
    fromElements_rowPrefix_rawRow]
  congr 1
  exact Fin.ext hnat.symm

/-- The bytecode block: its counter and entry columns fixed to the program's. -/
noncomputable def bcBlock (prog : LeanIsaProgram) (fin : K → ℕ) : Air.Flat.Table K :=
  ownTable (bytecodeComponent prog) (bcBlockRaw prog fin)
    (by
      intro r hr
      rw [bcBlockRaw, List.mem_ofFn] at hr
      obtain ⟨i, rfl⟩ := hr
      exact rawRow_size _)
    (by
      rw [bcBlockRaw, List.length_ofFn]
      exact (Nat.pow_le_pow_right (by norm_num) (prog.logSize_le.trans (by decide))).trans
        pow_maxLogRows_le)
    (bcBlockRaw_fixed prog fin)

/-- The eight tables of a list of skeletons, each with its own data. -/
noncomputable def skelTables (prog : LeanIsaProgram) {κ : ℕ} (img : MemoryImage κ) (S : List Skel)
    (hκ : κ ≤ maxLogMem) (hrows : ∀ op, Skel.count op S ≤ 2 ^ maxLogRows) :
    List (Air.Flat.Table K) :=
  have h : ∀ op, (opRows img (skelRows img S) op).length ≤ 2 ^ maxLogRows := fun op ↦ by
    rw [opRows, List.length_map, skelRows, length_filter_mkRows]; exact hrows op
  [opTable img (skelRows img S) .xor (h _), opTable img (skelRows img S) .mulNative (h _),
    opTable img (skelRows img S) .setConstant (h _), opTable img (skelRows img S) .deref (h _),
    opTable img (skelRows img S) .jump (h _), opTable img (skelRows img S) .keccak (h _),
    memBlock img (skelMemFin img S) hκ, bcBlock prog (skelBcFin S)]

/-- The eight tables' components are the ensemble's. -/
theorem skelTables_components (prog : LeanIsaProgram) {κ : ℕ} (img : MemoryImage κ)
    (S : List Skel) (hκ : κ ≤ maxLogMem) (hrows : ∀ op, Skel.count op S ≤ 2 ^ maxLogRows) :
    (skelTables prog img S hκ hrows).map (·.component) = (leanIsaEnsemble prog κ).tables := rfl

/-- The eight tables' names are distinct. -/
theorem skelTables_names (prog : LeanIsaProgram) {κ : ℕ} (img : MemoryImage κ) (S : List Skel)
    (hκ : κ ≤ maxLogMem) (hrows : ∀ op, Skel.count op S ≤ 2 ^ maxLogRows) :
    ((skelTables prog img S hκ hrows).map fun t ↦ t.component.circuit.name).Nodup := by
  have h := (leanIsaEnsemble prog κ).unique_names
  rw [← skelTables_components prog img S hκ hrows, List.map_map] at h
  exact h

/-- The tables of the witness: the eight tables with Clean's derived data. -/
noncomputable def skelWitnessTables (prog : LeanIsaProgram) {κ : ℕ} (img : MemoryImage κ)
    (S : List Skel) (hκ : κ ≤ maxLogMem) (hrows : ∀ op, Skel.count op S ≤ 2 ^ maxLogRows) :
    List (Air.Flat.Table K) :=
  Air.Flat.withDerivedData (skelTables prog img S hκ hrows) (skelTables_names prog img S hκ hrows)

/-- The witness's tables are the eight tables but for their data. -/
theorem skelWitnessTables_map (prog : LeanIsaProgram) {κ : ℕ} (img : MemoryImage κ)
    (S : List Skel) (hκ : κ ≤ maxLogMem) (hrows : ∀ op, Skel.count op S ≤ 2 ^ maxLogRows) :
    (skelWitnessTables prog img S hκ hrows).map (fun t ↦ (t.component, t.table)) =
      (skelTables prog img S hκ hrows).map (fun t ↦ (t.component, t.table)) :=
  Air.Flat.withDerivedData_map _ _

/-- The witness's tables' components are the ensemble's. -/
theorem skelWitnessTables_components (prog : LeanIsaProgram) {κ : ℕ} (img : MemoryImage κ)
    (S : List Skel) (hκ : κ ≤ maxLogMem) (hrows : ∀ op, Skel.count op S ≤ 2 ^ maxLogRows) :
    (skelWitnessTables prog img S hκ hrows).map (·.component) = (leanIsaEnsemble prog κ).tables := by
  rw [skelWitnessTables, Air.Flat.withDerivedData_map_component]
  rfl

/-- **The witness of a list of skeletons.** -/
noncomputable def skelWitness (prog : LeanIsaProgram) (input : PublicInput) {κ : ℕ}
    (img : MemoryImage κ) (S : List Skel) (hκ : κ ≤ maxLogMem)
    (hrows : ∀ op, Skel.count op S ≤ 2 ^ maxLogRows) :
    EnsembleWitness (leanIsaEnsemble prog κ) where
  tables := skelWitnessTables prog img S hκ hrows
  publicInput := PublicIO.ofInput input
  same_length := by
    rw [← skelWitnessTables_components prog img S hκ hrows, List.length_map]
  same_circuits := by
    intro i hi
    rw [List.getElem_of_eq (skelWitnessTables_components prog img S hκ hrows).symm hi,
      List.getElem_map]
  same_data := Air.Flat.withDerivedData_data _ _

/-! ## Reading the witness back

The witness's tables are the eight tables with the derived data: the same components and rows
(`skelWitnessTables_map`), so everything a table's rows send or satisfy, which Clean's row
semantics computes from the component and the row, is read off the eight tables. -/

/-- The eight tables. -/
theorem skelTables_length (prog : LeanIsaProgram) {κ : ℕ} (img : MemoryImage κ) (S : List Skel)
    (hκ : κ ≤ maxLogMem) (hrows : ∀ op, Skel.count op S ≤ 2 ^ maxLogRows) :
    (skelTables prog img S hκ hrows).length = 8 := rfl

/-- A function of the components and rows, summed over the witness's tables, is summed over the
eight tables. -/
theorem skelWitness_flatMap (prog : LeanIsaProgram) (input : PublicInput) {κ : ℕ}
    (img : MemoryImage κ) (S : List Skel) (hκ : κ ≤ maxLogMem)
    (hrows : ∀ op, Skel.count op S ≤ 2 ^ maxLogRows) {α : Type}
    (F : Component K → List (Array K) → List α) :
    (skelWitness prog input img S hκ hrows).tables.flatMap (fun t ↦ F t.component t.table) =
      (skelTables prog img S hκ hrows).flatMap (fun t ↦ F t.component t.table) := by
  have h := skelWitnessTables_map prog img S hκ hrows
  calc _ = ((skelWitnessTables prog img S hκ hrows).map fun t ↦ (t.component, t.table)).flatMap
          (fun p ↦ F p.1 p.2) := by rw [List.flatMap_map]; rfl
    _ = _ := by rw [h, List.flatMap_map]

/-- A table of the witness has the component and the rows of one of the eight tables. -/
theorem mem_skelWitness_tables {prog : LeanIsaProgram} {input : PublicInput} {κ : ℕ}
    {img : MemoryImage κ} {S : List Skel} {hκ : κ ≤ maxLogMem}
    {hrows : ∀ op, Skel.count op S ≤ 2 ^ maxLogRows} {t : Air.Flat.Table K}
    (ht : t ∈ (skelWitness prog input img S hκ hrows).tables) :
    ∃ t₀ ∈ skelTables prog img S hκ hrows, t.component = t₀.component ∧ t.table = t₀.table := by
  have hm : (t.component, t.table) ∈
      (skelWitnessTables prog img S hκ hrows).map fun t ↦ (t.component, t.table) :=
    List.mem_map_of_mem (f := fun t : Air.Flat.Table K ↦ (t.component, t.table)) ht
  rw [skelWitnessTables_map, List.mem_map] at hm
  obtain ⟨t₀, ht₀, he⟩ := hm
  exact ⟨t₀, ht₀, (congrArg Prod.fst he).symm, (congrArg Prod.snd he).symm⟩

/-- The rows of the witness's table `j` are the `j`-th of the eight tables'. -/
theorem skelWitness_tableAt_table (prog : LeanIsaProgram) (input : PublicInput) {κ : ℕ}
    (img : MemoryImage κ) (S : List Skel) (hκ : κ ≤ maxLogMem)
    (hrows : ∀ op, Skel.count op S ≤ 2 ^ maxLogRows) (j : Fin 8) :
    (tableAt (skelWitness prog input img S hκ hrows) j).table =
      ((skelTables prog img S hκ hrows)[(j : ℕ)]'(by
        rw [skelTables_length]; exact j.isLt)).table := by
  have hj : (j : ℕ) < ((skelWitnessTables prog img S hκ hrows).map
      fun t ↦ (t.component, t.table)).length := by
    rw [List.length_map, ← List.length_map (f := (·.component)), skelWitnessTables_components]
    exact j.isLt
  have e := List.getElem_of_eq (skelWitnessTables_map prog img S hκ hrows) hj
  rw [List.getElem_map, List.getElem_map] at e
  exact congrArg Prod.snd e

/-- The memory block of the witness. -/
theorem skelWitness_memBlockRows (prog : LeanIsaProgram) (input : PublicInput) {κ : ℕ}
    (img : MemoryImage κ) (S : List Skel) (hκ : κ ≤ maxLogMem)
    (hrows : ∀ op, Skel.count op S ≤ 2 ^ maxLogRows) :
    memBlockRows (skelWitness prog input img S hκ hrows) = memBlockRaw img (skelMemFin img S) :=
  skelWitness_tableAt_table prog input img S hκ hrows 6

/-- A memory row's first three cells are its limbs. -/
theorem rowPrefix_three_rawRow {prog : LeanIsaProgram} {κ : ℕ}
    (w : EnsembleWitness (leanIsaEnsemble prog κ)) (r : MemRow K) :
    Air.Flat.rowPrefix 3 (rawRow r) = r.m :=
  (memRowAt_m w (rawRow r)).symm.trans (congrArg MemRow.m (memRowAt_toElements w r))

/-- **The `"mem"` table of the witness's data is the image**: Clean derives it from the memory
block, whose limbs are the image's words. -/
theorem memRows_skelWitness (prog : LeanIsaProgram) (input : PublicInput) {κ : ℕ}
    (img : MemoryImage κ) (S : List Skel) (hκ : κ ≤ maxLogMem)
    (hrows : ∀ op, Skel.count op S ≤ 2 ^ maxLogRows) :
    memRows (skelWitness prog input img S hκ hrows).data = imageRows img := by
  rw [memRows_data, skelWitness_memBlockRows, memBlockRaw, List.map_ofFn, imageRows,
    List.toArray_ofFn]
  congr 1
  funext i
  exact rowPrefix_three_rawRow (skelWitness prog input img S hκ hrows) _

/-- **The image the witness names is `img`.** -/
theorem imageOf_skelWitness (prog : LeanIsaProgram) (input : PublicInput) {κ : ℕ}
    (img : MemoryImage κ) (S : List Skel) (hκ : κ ≤ maxLogMem)
    (hrows : ∀ op, Skel.count op S ≤ 2 ^ maxLogRows) :
    imageOf (skelWitness prog input img S hκ hrows).data = ⟨κ, img⟩ :=
  imageOf_of_memRows (memRows_skelWitness prog input img S hκ hrows) hκ

end LeanVM.Arithmetization
