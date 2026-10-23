/-
  LeanVM.Arithmetization.Soundness.Bus

  What a satisfying witness sends on the bus: the verifier's two states, the rows of the six
  opcode tables in their shared shape, the memory block's seed and finalize of the image, and the
  bytecode block's seed and finalize of the program.
-/

module

public import LeanVM.Arithmetization.Soundness.Rows
public import LeanVM.Arithmetization.Completeness.Satisfied

@[expose] public section

/-!
# The bus of a satisfying witness

At leanVM pin `127510d14c98ade4e8a97646c44fa7f1ff5e752d` and Clean pin `42fe4b26`. Specification
§6 (`doc/leanvm/body/06-bus-interactions.tex`; the state boundary §6.1, the seed and finalize
flushes of §6.2, the bytecode blocks of §6.4): the messages a witness of `SatisfiedBy` puts on
each channel. No balance is used here. Of the constraint statement `SatisfiedBy`, the three
hypotheses Clean cannot yet express (`IndexColumnsAreRowIndices`,
`SeedRowsAreTheImage`, `BytecodeRowsAreTheProgram`) pin the two blocks' rows.

**The rows.** `opPairs w` lists the rows of the six opcode tables, each with its table. Every
such row has the shape of `Soundness.Rows` (`OpRow`), so a choice of records `f` describes all
of them at once (`exists_opRecs`): row `p` sends `(f p).sends`, reads at most nine cells, and is a
step under its table's assumptions, constraints and pull guarantees.

**The sends** (`allSends_eq`). Everything the witness sends, in the ensemble's order: the
verifier's push of `(1, 1)` and pull of `(g^(N_prog - 1), 1)` (`verifierSends`), the rows'
records, the memory block's seed push `(g^i, 1, m_i)` and finalize pull `(g^i, c_i, m_i)` for
every word `m_i` of the image the data names (`memSeedSends`), and the bytecode block's seed push
and finalize pull of every entry of the program (`bcSeedSends`). The finalize counts `c_i` are the
prover's and nothing constrains them; the balance does.

**The counts** (`opRecs_counts_nonzero`). The nonzero count product (`CountsNonzero`) makes every
read count and every bytecode count of the six tables nonzero.

## Wrong readings excluded

* The verifier is a table of the witness's interactions (`allTables`): its pull of the final
  registers is on the state pull channel like any row's.
* The blocks' rows are not read off the prover data: they are the hypotheses' rows, the memory
  block's index column the row index (§6.5) and its words the image's, the bytecode block's
  entries the public program's.
-/

namespace LeanVM.Arithmetization

open LeanVM.Parameters LeanVM.Semantics
open Air.Flat (Component EnsembleWitness)

variable {prog : Program}

/-! ## Messages by channel name -/

/-- The messages named `n` of a list of interactions. -/
theorem chanOf_map_interactions (l : List (Interaction K)) (n : String) :
    chanOf n (l.map fun i ↦ (i.channel.name, i.msg)) =
      (l.filter (·.channel.name = n)).map (·.msg) := by
  induction l with
  | nil => rfl
  | cons i l ih =>
    simp only [chanOf] at ih ⊢
    by_cases h : i.channel.name = n <;> simp [h, ih]

/-- The messages named `n` a table sends are its interactions named `n`. -/
theorem chanOf_table (t : Air.Flat.Table K) (n : String) :
    chanOf n (t.table.flatMap fun row ↦ rowSends t.component (t.environment row)) =
      (t.interactions.filter (·.channel.name = n)).map (·.msg) := by
  have : (t.table.flatMap fun row ↦ rowSends t.component (t.environment row)) =
      t.interactions.map fun i ↦ (i.channel.name, i.msg) := by
    unfold Air.Flat.Table.interactions
    rw [List.map_flatMap]
    refine List.flatMap_congr fun row _ ↦ ?_
    rw [Component.interactionsValues_eq]
    unfold rowSends Operations.interactionValues
    rw [List.map_map]
  rw [this, chanOf_map_interactions]

/-- A message on the channel named `n` of a table's sends is an interaction of the table. -/
theorem mem_interactions_of_chanOf {t : Air.Flat.Table K} {n : String} {msg : Array K}
    (h : msg ∈ chanOf n (t.table.flatMap fun row ↦ rowSends t.component (t.environment row))) :
    ∃ i ∈ t.interactions, i.channel.name = n ∧ i.msg = msg := by
  rw [chanOf_table] at h
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp h
  obtain ⟨hi, hn⟩ := List.mem_filter.mp hi
  exact ⟨i, hi, of_decide_eq_true hn, rfl⟩

/-- Everything a witness sends, table by table and row by row, the verifier first. -/
def allSends (w : EnsembleWitness (leanIsaEnsemble prog)) : List (String × Array K) :=
  w.allTables.flatMap fun t ↦ t.table.flatMap fun row ↦ rowSends t.component (t.environment row)

/-- The messages on a channel are those of the sends with its name. -/
theorem messagesOn_eq_chanOf (w : EnsembleWitness (leanIsaEnsemble prog)) (c : RawChannel K) :
    messagesOn w c = chanOf c.name (allSends w) :=
  messagesOn_eq_sends w c

/-- A message of a channel is the message of an interaction on a channel of that name. -/
theorem mem_messagesOn {w : EnsembleWitness (leanIsaEnsemble prog)} {c : RawChannel K}
    {i : Interaction K} (hi : i ∈ w.interactions) (hc : i.channel.name = c.name) :
    i.msg ∈ messagesOn w c :=
  List.mem_map.mpr ⟨i, List.mem_filter.mpr ⟨hi, decide_eq_true hc⟩, rfl⟩

/-! ## The tables of a witness -/

/-- The witness's tables are the six opcode tables, then the two blocks. -/
theorem tables_eq (w : EnsembleWitness (leanIsaEnsemble prog)) :
    w.tables = w.tables.take 6 ++ [tableAt w 6, tableAt w 7] := by
  have hlen : w.tables.length = 8 := w.same_length.symm
  conv_lhs => rw [← List.take_append_drop 6 w.tables]
  congr 1
  apply List.ext_getElem (by simp [hlen])
  intro i h1 h2
  simp only [List.length_drop, hlen] at h1
  interval_cases i <;> simp [tableAt]

/-- A table among the first six is the table of an index below six. -/
theorem mem_take_six {w : EnsembleWitness (leanIsaEnsemble prog)} {t : Air.Flat.Table K}
    (ht : t ∈ w.tables.take 6) : ∃ j : Fin 8, (j : ℕ) < 6 ∧ tableAt w j = t := by
  have hlen : w.tables.length = 8 := w.same_length.symm
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem ht
  simp only [List.length_take, hlen] at hi
  refine ⟨⟨i, by omega⟩, by simp; omega, ?_⟩
  simp [tableAt]

/-- The rows of the six opcode tables, each with its table. -/
def opPairs (w : EnsembleWitness (leanIsaEnsemble prog)) : List (Air.Flat.Table K × Array K) :=
  (w.tables.take 6).flatMap fun t ↦ t.table.map fun row ↦ (t, row)

/-- A row of `opPairs` is a row of a table among the first six. -/
theorem mem_opPairs {w : EnsembleWitness (leanIsaEnsemble prog)}
    {p : Air.Flat.Table K × Array K} (hp : p ∈ opPairs w) :
    p.1 ∈ w.tables.take 6 ∧ p.2 ∈ p.1.table := by
  obtain ⟨t, ht, hp⟩ := List.mem_flatMap.mp hp
  obtain ⟨row, hrow, rfl⟩ := List.mem_map.mp hp
  exact ⟨ht, hrow⟩

/-- The environment of a row of a witness's table reads the witness's data. -/
theorem environment_data {w : EnsembleWitness (leanIsaEnsemble prog)} {t : Air.Flat.Table K}
    (ht : t ∈ w.tables) (row : Array K) : (t.environment row).data = w.data :=
  w.same_data t ht

/-! ## The records of the rows -/

/-- What the rows of the six tables are: each sends its record, reads at most nine cells, emits
on the six channels only, and is a step under its table's assumptions, constraints and pull
guarantees. -/
def OpRecs (w : EnsembleWitness (leanIsaEnsemble prog)) (f : Air.Flat.Table K × Array K → RowRec) :
    Prop :=
  ∀ p ∈ opPairs w,
    rowSends p.1.component (p.1.environment p.2) = (f p).sends ∧ (f p).reads.length ≤ 9 ∧
      (∀ a ∈ p.1.component.operations.interactions, ChannelOk a.channel) ∧
      (p.1.component.Assumptions (p.1.environment p.2) →
        p.1.component.operations.ConstraintsHold (p.1.environment p.2) →
        p.1.component.operations.FullGuarantees (p.1.environment p.2) →
        ∃ ins, (f p).e = entry ins ∧ execute (imageOf w.data).2 (f p).src ins = some (f p).next ∧
          (ins.opcode ≠ .jump → (f p).next = ⟨g * (f p).pc, (f p).fp⟩))

/-- Every witness has records for its rows. -/
theorem exists_opRecs (w : EnsembleWitness (leanIsaEnsemble prog)) : ∃ f, OpRecs w f := by
  classical
  have hrow : ∀ p ∈ opPairs w, OpRow p.1.component (p.1.environment p.2) ∧
      ∀ a ∈ p.1.component.operations.interactions, ChannelOk a.channel := by
    intro p hp
    obtain ⟨ht, -⟩ := mem_opPairs hp
    obtain ⟨j, hj, hjt⟩ := mem_take_six ht
    rw [← hjt]
    exact ⟨(tableAt_opRow w j hj).1 _, (tableAt_opRow w j hj).2⟩
  refine ⟨fun p ↦ if h : OpRow p.1.component (p.1.environment p.2) then h.choose else default,
    fun p hp ↦ ?_⟩
  obtain ⟨h, hch⟩ := hrow p hp
  have hdata := environment_data (List.mem_of_mem_take (mem_opPairs hp).1) p.2
  simp only [h, ↓reduceDIte]
  obtain ⟨hs, hl, hstep⟩ := h.choose_spec
  refine ⟨hs, hl, hch, fun ha hc hg ↦ ?_⟩
  rw [← hdata]
  exact hstep ha hc hg

/-! ## The sends of the verifier and the blocks -/

/-- A row written from a typed row sends what the row circuit sends at that row. -/
theorem rowSends_toElements {Input Output : TypeMap} [ProvableType Input] [ProvableType Output]
    (c : GeneralFormalCircuit K Input Output) (data : ProverData K) (r : Input K) :
    rowSends ⟨c⟩ (Environment.fromArray (toElements r).toArray data) =
      (((c.main (varFromOffset Input 0)).operations (size Input)).interactionValues
        (Environment.fromArray (rawRow r) data)).map (fun i ↦ (i.channel.name, i.msg)) := rfl

/-- What the verifier sends: the push of the initial registers and the pull of the final ones. -/
def verifierSends (prog : Program) : List (String × Array K) :=
  [(StatePush.name, #[1, 1]), (StatePull.name, #[prog.finalPc, 1])]

/-- The limbs of word `i` of an image. -/
def limbsOf {κ : ℕ} (img : MemImage κ) (i : Fin (2 ^ κ)) : Vector K 3 :=
  #v[(img i).limb 0, (img i).limb 1, (img i).limb 2]

/-- What the memory block sends for the image `img` and the finalize counts `fin`: per word the
seed push `(g^i, 1, m_i)` and the finalize pull `(g^i, fin i, m_i)`. -/
def memSeedSends {κ : ℕ} (img : MemImage κ) (fin : Fin (2 ^ κ) → K) :
    List (String × Array K) :=
  (List.finRange (2 ^ κ)).flatMap fun i : Fin (2 ^ κ) ↦
    [(MemPush.name, memMsgOf (gpow i) 1 (limbsOf img i)),
      (MemPull.name, memMsgOf (gpow i) (fin i) (limbsOf img i))]

/-- What the bytecode block sends for the program and the finalize counts `fin`: per slot the seed
push `(g^i, 1, entry)` and the finalize pull `(g^i, fin i, entry)`. -/
def bcSeedSends (prog : Program) (fin : Fin (2 ^ prog.logSize) → K) : List (String × Array K) :=
  (List.finRange (2 ^ prog.logSize)).flatMap fun i : Fin (2 ^ prog.logSize) ↦
    [(BytecodePush.name, bcMsgOf (gpow i) 1 (entry (prog.code i))),
      (BytecodePull.name, bcMsgOf (gpow i) (fin i) (entry (prog.code i)))]

/-- The sends of a table's rows. -/
def tableSends (t : Air.Flat.Table K) : List (String × Array K) :=
  t.table.flatMap fun row ↦ rowSends t.component (t.environment row)

/-- The memory block of a satisfying witness sends the seed and the finalize of every word of the
image the data names, with some finalize counts. -/
theorem memBlock_sends_eq {input : PublicInput} {w : EnsembleWitness (leanIsaEnsemble prog)}
    (h : SatisfiedBy prog input w) :
    ∃ mfin : Fin (2 ^ (imageOf w.data).1) → K,
      tableSends (tableAt w 6) = memSeedSends (imageOf w.data).2 mfin := by
  obtain ⟨idx, mfin, hmem⟩ := h.seed_rows
  refine ⟨mfin, ?_⟩
  have hlen : (memBlockRows w).length = 2 ^ (imageOf w.data).1 := by rw [hmem]; simp
  have hidx : ∀ i, idx i = gpow i := fun i ↦ by
    have := h.index_columns i (by rw [hlen]; exact i.isLt)
    simp only [hmem, List.getElem_ofFn, memRowAt_toElements] at this
    exact this
  have hc : (tableAt w 6).component = ⟨memTable⟩ := tableAt_component w 6
  show (memBlockRows w).flatMap _ = _
  rw [hmem, List.ofFn_eq_map, List.flatMap_map]
  refine List.flatMap_congr fun i _ ↦ ?_
  rw [hc, Air.Flat.Table.environment, rowSends_toElements,
    mem_sends_gen _ _ _ _ (eval_rowVar _ _)]
  simp [memMsgOf, limbsOf, hidx]

/-- The bytecode block of a satisfying witness sends the seed and the finalize of every entry of
the program, with some finalize counts. -/
theorem bcBlock_sends_eq {input : PublicInput} {w : EnsembleWitness (leanIsaEnsemble prog)}
    (h : SatisfiedBy prog input w) :
    ∃ bfin : Fin (2 ^ prog.logSize) → K, tableSends (tableAt w 7) = bcSeedSends prog bfin := by
  obtain ⟨bfin, hbc⟩ := h.bytecode_rows
  refine ⟨bfin, ?_⟩
  have hc : (tableAt w 7).component = ⟨bytecodeTable⟩ := tableAt_component w 7
  show (bytecodeBlockRows w).flatMap _ = _
  rw [hbc, List.ofFn_eq_map, List.flatMap_map]
  refine List.flatMap_congr fun i _ ↦ ?_
  rw [hc, Air.Flat.Table.environment, rowSends_toElements,
    bytecode_sends_gen _ _ _ _ (eval_rowVar _ _)]
  simp [bcMsgOf, bytecodeRowOf]

/-- **Everything a satisfying witness sends**: the verifier's two states, the records of the rows
of the six tables, the memory block's seed and finalize of the image the data names, and the
bytecode block's seed and finalize of the program. -/
theorem allSends_eq {input : PublicInput} {w : EnsembleWitness (leanIsaEnsemble prog)}
    (h : SatisfiedBy prog input w) {f : Air.Flat.Table K × Array K → RowRec} (hf : OpRecs w f) :
    ∃ (mfin : Fin (2 ^ (imageOf w.data).1) → K) (bfin : Fin (2 ^ prog.logSize) → K),
      allSends w = verifierSends prog ++ (opPairs w).flatMap (fun p ↦ (f p).sends) ++
        memSeedSends (imageOf w.data).2 mfin ++ bcSeedSends prog bfin := by
  obtain ⟨mfin, hmem⟩ := memBlock_sends_eq h
  obtain ⟨bfin, hbc⟩ := bcBlock_sends_eq h
  refine ⟨mfin, bfin, ?_⟩
  unfold allSends EnsembleWitness.allTables
  rw [List.flatMap_cons, tables_eq w, List.flatMap_append, List.flatMap_cons, List.flatMap_cons,
    List.flatMap_nil, List.append_nil, ← List.append_assoc, ← List.append_assoc]
  congr 1
  · congr 1
    · congr 1
      · -- The verifier.
        rw [EnsembleWitness.verifierTable_table, List.flatMap_singleton]
        exact verifier_sends prog _
      · -- The six tables.
        unfold opPairs
        rw [List.flatMap_assoc]
        refine List.flatMap_congr fun t ht ↦ ?_
        rw [List.flatMap_map]
        refine List.flatMap_congr fun row hrow ↦ ?_
        exact (hf (t, row) (List.mem_flatMap.mpr ⟨t, ht, List.mem_map_of_mem hrow⟩)).1

/-! ## The messages of each piece -/

/-- The messages of a `flatMap` over any universe (`chanOf_flatMap` takes `α : Type`; a table
lives in `Type 1`). -/
theorem chanOf_flatMap' {α : Type*} (n : String) (l : List α) (F : α → List (String × Array K)) :
    chanOf n (l.flatMap F) = l.flatMap fun a ↦ chanOf n (F a) := by
  simp only [chanOf, List.filter_flatMap, List.map_flatMap]

/-- The messages on a channel are those of each piece of `allSends_eq`. -/
theorem chanOf_allSends {w : EnsembleWitness (leanIsaEnsemble prog)} (n : String)
    {f : Air.Flat.Table K × Array K → RowRec} {mfin : Fin (2 ^ (imageOf w.data).1) → K}
    {bfin : Fin (2 ^ prog.logSize) → K}
    (h : allSends w = verifierSends prog ++ (opPairs w).flatMap (fun p ↦ (f p).sends) ++
      memSeedSends (imageOf w.data).2 mfin ++ bcSeedSends prog bfin) :
    chanOf n (allSends w) = chanOf n (verifierSends prog) ++
      (opPairs w).flatMap (fun p ↦ chanOf n (f p).sends) ++
      chanOf n (memSeedSends (imageOf w.data).2 mfin) ++ chanOf n (bcSeedSends prog bfin) := by
  rw [h]
  simp only [chanOf_append, chanOf_flatMap']

/-- The verifier pushes `(1, 1)` and nothing else. -/
theorem chanOf_verifier_statePush : chanOf StatePush.name (verifierSends prog) = [#[1, 1]] := by
  simp [chanOf, verifierSends, StatePull, StatePush]

/-- The verifier pulls the final registers and nothing else. -/
theorem chanOf_verifier_statePull :
    chanOf StatePull.name (verifierSends prog) = [#[prog.finalPc, 1]] := by
  simp [chanOf, verifierSends, StatePull, StatePush]

/-- The verifier sends nothing on a channel other than the state pair. -/
theorem chanOf_verifier_eq_nil {n : String} (h1 : n ≠ StatePull.name) (h2 : n ≠ StatePush.name) :
    chanOf n (verifierSends prog) = [] := by
  simp only [chanOf, verifierSends]
  simp [Ne.symm h1, Ne.symm h2]

/-- The memory block pushes the seeds. -/
theorem chanOf_memSeed_push {κ : ℕ} (img : MemImage κ) (fin : Fin (2 ^ κ) → K) :
    chanOf MemPush.name (memSeedSends img fin) =
      (List.finRange (2 ^ κ)).map fun i : Fin (2 ^ κ) ↦ memMsgOf (gpow i) 1 (limbsOf img i) := by
  rw [memSeedSends, chanOf_flatMap, ← flatMap_singleton_eq_map]
  refine List.flatMap_congr fun i _ ↦ ?_
  simp [chanOf, MemPull, MemPush]

/-- The memory block pulls the finalizes. -/
theorem chanOf_memSeed_pull {κ : ℕ} (img : MemImage κ) (fin : Fin (2 ^ κ) → K) :
    chanOf MemPull.name (memSeedSends img fin) =
      (List.finRange (2 ^ κ)).map fun i : Fin (2 ^ κ) ↦
        memMsgOf (gpow i) (fin i) (limbsOf img i) := by
  rw [memSeedSends, chanOf_flatMap, ← flatMap_singleton_eq_map]
  refine List.flatMap_congr fun i _ ↦ ?_
  simp [chanOf, MemPull, MemPush]

/-- The memory block sends nothing on a channel other than the memory pair. -/
theorem chanOf_memSeed_eq_nil {κ : ℕ} (img : MemImage κ) (fin : Fin (2 ^ κ) → K) {n : String}
    (h1 : n ≠ MemPull.name) (h2 : n ≠ MemPush.name) : chanOf n (memSeedSends img fin) = [] := by
  rw [memSeedSends, chanOf_flatMap]
  simp [chanOf, Ne.symm h1, Ne.symm h2]

/-- The bytecode block pushes the program's entries. -/
theorem chanOf_bcSeed_push (fin : Fin (2 ^ prog.logSize) → K) :
    chanOf BytecodePush.name (bcSeedSends prog fin) =
      (List.finRange (2 ^ prog.logSize)).map fun i : Fin (2 ^ prog.logSize) ↦
        bcMsgOf (gpow i) 1 (entry (prog.code i)) := by
  rw [bcSeedSends, chanOf_flatMap, ← flatMap_singleton_eq_map]
  refine List.flatMap_congr fun i _ ↦ ?_
  simp [chanOf, BytecodePull, BytecodePush]

/-- The bytecode block pulls the program's entries with the finalize counts. -/
theorem chanOf_bcSeed_pull (fin : Fin (2 ^ prog.logSize) → K) :
    chanOf BytecodePull.name (bcSeedSends prog fin) =
      (List.finRange (2 ^ prog.logSize)).map fun i : Fin (2 ^ prog.logSize) ↦
        bcMsgOf (gpow i) (fin i) (entry (prog.code i)) := by
  rw [bcSeedSends, chanOf_flatMap, ← flatMap_singleton_eq_map]
  refine List.flatMap_congr fun i _ ↦ ?_
  simp [chanOf, BytecodePull, BytecodePush]

/-- The bytecode block sends nothing on a channel other than the bytecode pair. -/
theorem chanOf_bcSeed_eq_nil (fin : Fin (2 ^ prog.logSize) → K) {n : String}
    (h1 : n ≠ BytecodePull.name) (h2 : n ≠ BytecodePush.name) :
    chanOf n (bcSeedSends prog fin) = [] := by
  rw [bcSeedSends, chanOf_flatMap]
  simp [chanOf, Ne.symm h1, Ne.symm h2]

/-! ## The read counts -/

/-- **The nonzero count product, per row**: every memory read count and the bytecode count of a
row of the six tables is nonzero (`CountsNonzero`). -/
theorem opRecs_counts_nonzero {input : PublicInput} {w : EnsembleWitness (leanIsaEnsemble prog)}
    (h : SatisfiedBy prog input w) {f : Air.Flat.Table K × Array K → RowRec} (hf : OpRecs w f)
    {p : Air.Flat.Table K × Array K} (hp : p ∈ opPairs w) :
    (∀ x ∈ (f p).reads, x.2.1 ≠ 0) ∧ (f p).rbc ≠ 0 := by
  obtain ⟨ht, hrow⟩ := mem_opPairs hp
  have hsends := (hf p hp).1
  have hsub : ∀ n, ∀ msg ∈ chanOf n (f p).sends,
      msg ∈ chanOf n (p.1.table.flatMap fun row ↦ rowSends p.1.component (p.1.environment row)) :=
    fun n msg hm ↦ by
      rw [chanOf_flatMap]
      exact List.mem_flatMap.mpr ⟨p.2, hrow, by rw [hsends]; exact hm⟩
  constructor
  · intro x hx
    have hm : memMsgOf x.1 x.2.1 x.2.2 ∈ chanOf MemPull.name (f p).sends := by
      rw [RowRec.sends, chanOf, sendsOf_memPull]
      exact List.mem_map_of_mem hx
    obtain ⟨i, hi, hn, hmsg⟩ := mem_interactions_of_chanOf (hsub _ _ hm)
    have := h.counts_nonzero p.1 ht i hi (Or.inl hn) (by rw [hmsg]; simp [memMsgOf])
    simpa [hmsg, memMsgOf] using this
  · have hm : bcMsgOf (f p).pc (f p).rbc (f p).e ∈ chanOf BytecodePull.name (f p).sends := by
      rw [RowRec.sends, chanOf, sendsOf_bcPull]
      exact List.mem_singleton_self _
    obtain ⟨i, hi, hn, hmsg⟩ := mem_interactions_of_chanOf (hsub _ _ hm)
    have := h.counts_nonzero p.1 ht i hi (Or.inr hn) (by rw [hmsg]; simp [bcMsgOf])
    simpa [hmsg, bcMsgOf] using this

/-- The caps bound the rows of the six tables: at most `6 · 2^32` (`Caps.heights`). -/
theorem opPairs_length_le {input : PublicInput} {w : EnsembleWitness (leanIsaEnsemble prog)}
    (h : SatisfiedBy prog input w) : (opPairs w).length ≤ 6 * 2 ^ 32 := by
  unfold opPairs
  rw [List.length_flatMap]
  have hb : ∀ x ∈ (w.tables.take 6).map fun t ↦ (t.table.map fun row ↦ (t, row)).length,
      x ≤ 2 ^ 32 := by
    intro x hx
    obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hx
    rw [List.length_map]
    exact h.caps.heights t (List.mem_of_mem_take ht)
  have hsum := List.sum_le_length_nsmul _ _ hb
  rw [List.length_map, smul_eq_mul] at hsum
  have h6 : (w.tables.take 6).length ≤ 6 := List.length_take_le _ _
  calc _ ≤ (w.tables.take 6).length * 2 ^ 32 := hsum
    _ ≤ 6 * 2 ^ 32 := Nat.mul_le_mul_right _ h6

/-- The rows of the six tables read at most `9 · 6 · 2^32` cells, fewer than `2^64 - 1`: the read
bound of specification Lemma 6.3, derived from the caps. -/
theorem opReads_length_lt {input : PublicInput} {w : EnsembleWitness (leanIsaEnsemble prog)}
    (h : SatisfiedBy prog input w) {f : Air.Flat.Table K × Array K → RowRec} (hf : OpRecs w f) :
    ((opPairs w).flatMap fun p ↦ (f p).reads).length < 2 ^ 64 - 1 := by
  rw [List.length_flatMap]
  have hb : ∀ x ∈ (opPairs w).map fun p ↦ (f p).reads.length, x ≤ 9 := by
    intro x hx
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hx
    exact (hf p hp).2.1
  have hsum := List.sum_le_length_nsmul _ _ hb
  rw [List.length_map, smul_eq_mul] at hsum
  have := opPairs_length_le h
  omega

end LeanVM.Arithmetization
