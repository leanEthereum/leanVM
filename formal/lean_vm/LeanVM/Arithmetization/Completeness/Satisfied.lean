/-
  LeanVM.Arithmetization.Completeness.Satisfied

  The witness of a list of skeletons satisfies the constraint statement: the three balances, the
  caps, the blocks' rows, the compression, and the public words.
-/

module

public import LeanVM.Arithmetization.Completeness.Witness

@[expose] public section

/-!
# The witness satisfies the statement

`skelWitness prog input img S hκ hrows` satisfies every conjunct of `SatisfiedBy prog input`
(`skelWitness_satisfiedBy`) when the skeletons `S` are sound for the program and the image
(`SkelOk`: fetched, and they execute), the state pair balances (the hypothesis `hstate`, proved from
the run in `Completeness.Theorem`), every table has at most `2^maxLogRows` rows, and the image has
the public words.

The proof is the bus computation. `messagesOn_skelWitness` says what each channel carries: the
verifier's messages, then the rows of each table, then the blocks'. A table's rows send what Clean's
row semantics computes from its component and its row, whatever the prover data
(`opRows_sends`, `memBlock_sends`, `bcBlock_sends`), so the witness's tables, which carry the
derived data, send what the eight tables they were built from send (`skelWitness_flatMap`). For the memory pair and the
bytecode pair the rows are the reads of one list of skeletons, numbered by the chain
(`Completeness.Bus`), so `chain_balance` (`Completeness.Balance`) balances them against the blocks'
seeds and finalizes; the six tables hold the rows in another order than the list, which is a
permutation (`regroup_perm`). The state pair is the hypothesis `hstate` regrouped the same way.
The `JUMP` table is the one component with constraints, and its two residuals hold of the honest
witnesses (`flags_complete`).

## Wrong readings excluded

* The balance is of the messages the rows send, never of the rows: a row that does not execute
  sends a message the image does not hold, and the chain lemma needs every read to be a message of
  the image (`readAddrs_valid`).
* The finalize count of a cell is `g^(reads of the cell)`, which is `1` for a cell nobody reads:
  the finalize pull of an unread cell is its seed push, and the two cancel.
-/

open scoped List

namespace LeanVM.Arithmetization

open LeanVM.Parameters LeanVM.Semantics
open Air.Flat (Component EnsembleWitness)

/-! ## What the bus carries -/

/-- The messages on a channel of a list of interactions, as the filter of their name and message
pairs. -/
theorem msgs_eq_sends (l : List (Interaction K)) (c : RawChannel K) :
    (l.filter (·.channel.name = c.name)).map (·.msg) =
      (((l.map fun i ↦ (i.channel.name, i.msg)).filter (·.1 = c.name)).map (·.2)) := by
  induction l with
  | nil => rfl
  | cons i l ih => by_cases h : i.channel.name = c.name <;> simp [h, ih]

/-- The messages a witness sends on a channel: the filter of the verifier's two sends, then of the
sends of every row of every table. -/
theorem messagesOn_eq_sends {prog : LeanIsaProgram} {κ : ℕ}
    (w : EnsembleWitness (leanIsaEnsemble prog κ)) (c : RawChannel K) :
    messagesOn w c =
      ((([(StatePush.name, #[1, 1]), (StatePull.name, #[prog.pcFinal, 1])] ++
        w.tables.flatMap fun t ↦ t.table.flatMap fun row ↦
          rowSends t.component (t.environment row)).filter (·.1 = c.name)).map (·.2)) := by
  unfold messagesOn
  rw [msgs_eq_sends]
  congr 2
  unfold EnsembleWitness.interactions
  rw [List.map_append, List.map_flatMap]
  congr 1
  · exact verifier_sends prog _
  · refine List.flatMap_congr fun t _ ↦ ?_
    unfold Air.Flat.Table.interactions
    rw [List.map_flatMap]
    refine List.flatMap_congr fun row _ ↦ ?_
    rw [Component.interactionsValues_eq]
    rfl

/-- The sends of the rows of a witness's tables, each table's rows read over the witness's data,
which every table carries. -/
theorem tables_sends_data {prog : LeanIsaProgram} {κ : ℕ}
    (w : EnsembleWitness (leanIsaEnsemble prog κ)) :
    (w.tables.flatMap fun t ↦ t.table.flatMap fun row ↦ rowSends t.component (t.environment row)) =
      w.tables.flatMap fun t ↦ t.table.flatMap fun row ↦
        rowSends t.component (Environment.fromArray row w.data) := by
  refine List.flatMap_congr fun t ht ↦ ?_
  simp only [Air.Flat.Table.environment, w.same_data t ht]
  rfl

/-- The sends of an opcode's rows, over any data, are those of the rows of `R`, when their
instructions execute. -/
theorem opRows_sends {κ : ℕ} (img : MemoryImage κ) (R : List PRow) (op : Opcode)
    (data : ProverData K) (hR : ∀ r ∈ R, ∃ next, execute img r.sk.regs r.sk.ins = some next) :
    (opRows img R op).flatMap
        (fun row ↦ rowSends (opComponent op) (Environment.fromArray row data)) =
      (R.filter fun r ↦ r.sk.ins.opcode = op).flatMap (PRow.sends img) := by
  rw [opRows, List.flatMap_map]
  refine List.flatMap_congr fun r hr ↦ ?_
  obtain ⟨hr1, hr2⟩ := List.mem_filter.mp hr
  simp only [decide_eq_true_eq] at hr2
  subst hr2
  exact PRow.rowSends_raw (hR r hr1) data

/-- The sends of the memory block: per cell, the seed push and the finalize pull. -/
def memBlockSends {κ : ℕ} (img : MemoryImage κ) (fin : K → ℕ) : List (String × Array K) :=
  (List.finRange (2 ^ κ)).flatMap fun i : Fin (2 ^ κ) ↦
    [(MemPush.name, #[addressOfIndex i, 1, (img i).limb 0, (img i).limb 1, (img i).limb 2]),
      (MemPull.name,
        #[addressOfIndex i, g ^ fin (addressOfIndex i), (img i).limb 0, (img i).limb 1, (img
            i).limb 2])]

/-- The sends of the memory block's rows, over any data, are `memBlockSends`. -/
theorem memBlock_sends {κ : ℕ} (img : MemoryImage κ) (fin : K → ℕ) (data : ProverData K) :
    (memBlockRaw img fin).flatMap
        (fun row ↦ rowSends (memComponent κ) (Environment.fromArray row data)) =
      memBlockSends img fin := by
  rw [memBlockRaw, List.ofFn_eq_map, List.flatMap_map]
  refine List.flatMap_congr fun i _ ↦ ?_
  rw [rowSends_memComponent, mem_sends_gen _ _ _ _ (eval_rowVar _ data)]
  rfl

/-- The sends of the bytecode block: per slot, the seed push and the finalize pull. -/
def bcBlockSends (prog : LeanIsaProgram) (fin : K → ℕ) : List (String × Array K) :=
  (List.finRange (2 ^ prog.logSize)).flatMap fun i : Fin (2 ^ prog.logSize) ↦
    [(BytecodePush.name, bcMsgOf (addressOfIndex i) 1 (busEntry (prog.instructions i))),
      (BytecodePull.name, bcMsgOf (addressOfIndex i) (g ^ fin (addressOfIndex i)) (busEntry
          (prog.instructions i)))]

/-- The sends of the bytecode block's rows, over any data, are `bcBlockSends`. -/
theorem bcBlock_sends (prog : LeanIsaProgram) (fin : K → ℕ) (data : ProverData K) :
    (bcBlockRaw prog fin).flatMap
        (fun row ↦ rowSends (bytecodeComponent prog) (Environment.fromArray row data)) =
      bcBlockSends prog fin := by
  rw [bcBlockRaw, List.ofFn_eq_map, List.flatMap_map]
  refine List.flatMap_congr fun i _ ↦ ?_
  rw [rowSends_bytecodeComponent, bytecode_sends_gen _ _ _ _ (eval_rowVar _ data)]
  simp [bytecodeRowOf, bcMsgOf]

/-! ## What each channel carries -/

/-- The messages of the channel named `n` among a list of sends. -/
def chanOf (n : String) (l : List (String × Array K)) : List (Array K) :=
  (l.filter (·.1 = n)).map (·.2)

/-- The messages of a concatenation. -/
theorem chanOf_append (n : String) (l₁ l₂ : List (String × Array K)) :
    chanOf n (l₁ ++ l₂) = chanOf n l₁ ++ chanOf n l₂ := by
  simp only [chanOf, List.filter_append, List.map_append]

/-- The messages of a `flatMap`. -/
theorem chanOf_flatMap {α : Type} (n : String) (l : List α) (F : α → List (String × Array K)) :
    chanOf n (l.flatMap F) = l.flatMap fun a ↦ chanOf n (F a) := by
  simp only [chanOf, List.filter_flatMap, List.map_flatMap]

/-- Everything the witness sends, in the ensemble's order: the verifier's two messages, the
rows of the six tables, the memory block, the bytecode block. -/
noncomputable def skelSends (prog : LeanIsaProgram) {κ : ℕ} (img : MemoryImage κ) (S : List Skel) :
    List (String × Array K) :=
  [(StatePush.name, #[1, 1]), (StatePull.name, #[prog.pcFinal, 1])] ++
    (tableOpcodes.flatMap fun op ↦
      ((skelRows img S).filter fun r ↦ r.sk.ins.opcode = op).flatMap (PRow.sends img)) ++
    memBlockSends img (skelMemFin img S) ++ bcBlockSends prog (skelBcFin S)

/-- **The sends of the witness.** -/
theorem skelWitness_sends (prog : LeanIsaProgram) (input : PublicInput) {κ : ℕ}
    (img : MemoryImage κ) (S : List Skel) (hκ : κ ≤ maxLogMem)
    (hrows : ∀ op, Skel.count op S ≤ 2 ^ maxLogRows)
    (hS : ∀ sk ∈ S, ∃ next, execute img sk.regs sk.ins = some next) :
    [(StatePush.name, #[1, 1]), (StatePull.name, #[prog.pcFinal, 1])] ++
      ((skelWitness prog input img S hκ hrows).tables.flatMap fun t ↦ t.table.flatMap fun row ↦
        rowSends t.component (t.environment row)) = skelSends prog img S := by
  have hR : ∀ r ∈ skelRows img S, ∃ next, execute img r.sk.regs r.sk.ins = some next :=
    fun r hr ↦ hS _ (mem_mkRows_sk hr)
  rw [tables_sends_data, skelWitness_flatMap (F := fun c rows ↦ rows.flatMap fun row ↦
    rowSends c (Environment.fromArray row (skelWitness prog input img S hκ hrows).data))]
  simp only [skelTables, opTable, memBlock, bcBlock, ownTable, List.flatMap_cons, List.flatMap_nil,
    List.append_nil, opRows_sends _ _ _ _ hR, memBlock_sends, bcBlock_sends, skelSends,
    tableOpcodes, List.append_assoc]

/-- **The six tables hold the rows of `R` regrouped by opcode**: on every channel their messages
are a permutation of those of the rows in order. -/
theorem chanOf_tables_perm {κ : ℕ} (img : MemoryImage κ) (n : String) (R : List PRow) :
    (chanOf n (tableOpcodes.flatMap fun op ↦
      (R.filter fun r ↦ r.sk.ins.opcode = op).flatMap (PRow.sends img))).Perm
      (R.flatMap fun r ↦ chanOf n (r.sends img)) := by
  rw [chanOf_flatMap]
  have h : (tableOpcodes.flatMap fun op ↦ chanOf n
      ((R.filter fun r ↦ r.sk.ins.opcode = op).flatMap (PRow.sends img))) =
      (tableOpcodes.flatMap fun op ↦ R.filter fun r ↦ r.sk.ins.opcode = op).flatMap
        fun r ↦ chanOf n (r.sends img) := by
    rw [List.flatMap_assoc]
    refine List.flatMap_congr fun op _ ↦ ?_
    rw [chanOf_flatMap]
  rw [h]
  exact (regroup_perm tableOpcodes (fun r : PRow ↦ r.sk.ins.opcode) R (by decide)
    fun r _ ↦ mem_tableOpcodes _).flatMap_right _

/-- A channel no send of the list names carries nothing. -/
theorem chanOf_eq_nil {n : String} {l : List (String × Array K)} (h : ∀ x ∈ l, x.1 ≠ n) :
    chanOf n l = [] := by
  unfold chanOf
  rw [List.filter_eq_nil_iff.mpr (fun x hx ↦ by simpa using h x hx)]
  rfl

/-- The witness's messages on a channel: the verifier's, the rows' of the six tables in
order, the memory block's, the bytecode block's, up to the regrouping of the rows. -/
theorem chanOf_skelSends_perm (prog : LeanIsaProgram) {κ : ℕ} (img : MemoryImage κ) (S : List Skel)
    (n : String) :
    (chanOf n (skelSends prog img S)).Perm
      (chanOf n [(StatePush.name, #[1, 1]), (StatePull.name, #[prog.pcFinal, 1])] ++
        (skelRows img S).flatMap (fun r ↦ chanOf n (r.sends img)) ++
        chanOf n (memBlockSends img (skelMemFin img S)) ++
        chanOf n (bcBlockSends prog (skelBcFin S))) := by
  unfold skelSends
  simp only [chanOf_append]
  exact (((chanOf_tables_perm img n (skelRows img S)).append_left _).append_right _).append_right _

/-! ### The blocks' channels -/

/-- The word at the address of an index, as a memory message. -/
theorem memMsg_gpow {κ : ℕ} (hκ : κ < 64) (img : MemoryImage κ) (i : Fin (2 ^ κ)) (e : ℕ) :
    memMsg img (addressOfIndex i) e =
      #[addressOfIndex i, g ^ e, (img i).limb 0, (img i).limb 1, (img i).limb 2] := by
  have h := MemImage.limbsAt_eq_of_read (MemoryImage.read_gpow hκ img i)
  simp [memMsg, memMsgOf, h]

/-- The memory block sends only on the memory pair. -/
theorem memBlockSends_names {κ : ℕ} (img : MemoryImage κ) (fin : K → ℕ) :
    ∀ x ∈ memBlockSends img fin, x.1 = MemPush.name ∨ x.1 = MemPull.name := by
  intro x hx
  simp only [memBlockSends, List.mem_flatMap, List.mem_cons, List.not_mem_nil, or_false] at hx
  obtain ⟨i, -, rfl | rfl⟩ := hx <;> simp

/-- The bytecode block sends only on the bytecode pair. -/
theorem bcBlockSends_names (prog : LeanIsaProgram) (fin : K → ℕ) :
    ∀ x ∈ bcBlockSends prog fin, x.1 = BytecodePush.name ∨ x.1 = BytecodePull.name := by
  intro x hx
  simp only [bcBlockSends, List.mem_flatMap, List.mem_cons, List.not_mem_nil, or_false] at hx
  obtain ⟨i, -, rfl | rfl⟩ := hx <;> simp

/-- The memory block's seed pushes: the word of each cell with the count `g^0`. -/
theorem memBlock_push {κ : ℕ} (hκ : κ < 64) (img : MemoryImage κ) (fin : K → ℕ) :
    chanOf MemPush.name (memBlockSends img fin) =
      (List.finRange (2 ^ κ)).map fun i : Fin (2 ^ κ) ↦ memMsg img (addressOfIndex i) 0 := by
  unfold memBlockSends
  rw [chanOf_flatMap, ← flatMap_singleton_eq_map]
  refine List.flatMap_congr fun i _ ↦ ?_
  simp [chanOf, MemPush, MemPull, memMsg_gpow hκ]

/-- The memory block's finalize pulls: the word of each cell with the count its row holds. -/
theorem memBlock_pull {κ : ℕ} (hκ : κ < 64) (img : MemoryImage κ) (fin : K → ℕ) :
    chanOf MemPull.name (memBlockSends img fin) =
      (List.finRange (2 ^ κ)).map fun i : Fin (2 ^ κ) ↦ memMsg img (addressOfIndex i) (fin
          (addressOfIndex i)) := by
  unfold memBlockSends
  rw [chanOf_flatMap, ← flatMap_singleton_eq_map]
  refine List.flatMap_congr fun i _ ↦ ?_
  simp [chanOf, MemPush, MemPull, memMsg_gpow hκ]

/-- The bytecode block's seed pushes. -/
theorem bcBlock_push (prog : LeanIsaProgram) (fin : K → ℕ) :
    chanOf BytecodePush.name (bcBlockSends prog fin) =
      (List.finRange (2 ^ prog.logSize)).map fun i : Fin (2 ^ prog.logSize) ↦
        bcMsg prog (addressOfIndex i) 0 := by
  unfold bcBlockSends
  rw [chanOf_flatMap, ← flatMap_singleton_eq_map]
  refine List.flatMap_congr fun i _ ↦ ?_
  simp [chanOf, BytecodePush, BytecodePull, bcMsg, entryAt, LeanIsaProgram.fetch_gpow]

/-- The bytecode block's finalize pulls. -/
theorem bcBlock_pull (prog : LeanIsaProgram) (fin : K → ℕ) :
    chanOf BytecodePull.name (bcBlockSends prog fin) =
      (List.finRange (2 ^ prog.logSize)).map fun i : Fin (2 ^ prog.logSize) ↦
        bcMsg prog (addressOfIndex i) (fin (addressOfIndex i)) := by
  unfold bcBlockSends
  rw [chanOf_flatMap, ← flatMap_singleton_eq_map]
  refine List.flatMap_congr fun i _ ↦ ?_
  simp [chanOf, BytecodePush, BytecodePull, bcMsg, entryAt, LeanIsaProgram.fetch_gpow]

/-! ## The three balances -/

/-- The addresses of the `2^k` rows of a block are distinct, for `k ≤ 32`. -/
theorem gpow_keys_nodup (k : ℕ) (hk : k ≤ 32) :
    ((List.finRange (2 ^ k)).map fun i : Fin (2 ^ k) ↦ addressOfIndex (i : ℕ)).Nodup := by
  refine List.Nodup.map_on (fun x _ y _ h ↦ ?_) (List.nodup_finRange _)
  have h32 : 2 ^ k ≤ 2 ^ 32 := Nat.pow_le_pow_right (by norm_num) hk
  have hx : (x : ℕ) ∈ Set.Iio (2 ^ 64 - 1) := by
    simp only [Set.mem_Iio]; have := x.isLt; omega
  have hy : (y : ℕ) ∈ Set.Iio (2 ^ 64 - 1) := by
    simp only [Set.mem_Iio]; have := y.isLt; omega
  exact Fin.ext (gpow_injOn hx hy h)

/-- A block's seeds and finalizes against the reads of the rows, for any messages indexed by the
address and the number. -/
theorem block_balance {ι α : Type} [DecidableEq ι] (keys : List ι) (hnd : keys.Nodup)
    (mk : ι → ℕ → α) (L : List ι) (hL : ∀ a ∈ L, a ∈ keys) :
    (List.zipWith (fun a e ↦ mk a (e + 1)) L (readExps (fun _ ↦ 0) L) ++
        keys.map fun a ↦ mk a 0).Perm
      (List.zipWith (fun a e ↦ mk a e) L (readExps (fun _ ↦ 0) L) ++
        keys.map fun a ↦ mk a (readBump (fun _ ↦ 0) L a)) :=
  List.perm_append_comm.trans
    ((chain_balance keys hnd mk L hL fun _ ↦ 0).trans List.perm_append_comm)

/-- A permutation survives the same list inserted in the middle of both sides. -/
theorem perm_append_mid {α : Type} {a b c x y : List α} (h : (a ++ x).Perm (b ++ y)) :
    ((a ++ c) ++ x).Perm ((b ++ c) ++ y) := by
  have hc : ∀ u v : List α, ((u ++ c) ++ v).Perm ((u ++ v) ++ c) := fun u v ↦ by
    rw [List.append_assoc, List.append_assoc]
    exact List.Perm.append_left _ List.perm_append_comm
  exact (hc a x).trans ((h.append_right c).trans (hc b y).symm)

/-- **The memory pair balances**: the rows' reads, numbered by the chain, against the block's seeds
and finalizes. -/
theorem mem_pair_perm (prog : LeanIsaProgram) {κ : ℕ} (hκ : κ ≤ maxLogMem) (img : MemoryImage κ)
    (S : List Skel) (hS : ∀ sk ∈ S, ∃ next, execute img sk.regs sk.ins = some next) :
    (chanOf MemPush.name (skelSends prog img S)).Perm
      (chanOf MemPull.name (skelSends prog img S)) := by
  have hκ64 : κ < 64 := by unfold maxLogMem at hκ; omega
  have hmem : ∀ a ∈ S.flatMap (fun sk ↦ readAddrs img sk.fp sk.ins),
      a ∈ (List.finRange (2 ^ κ)).map fun i : Fin (2 ^ κ) ↦ addressOfIndex (i : ℕ) := by
    intro a ha
    obtain ⟨sk, hsk, ha⟩ := List.mem_flatMap.mp ha
    obtain ⟨next, hn⟩ := hS sk hsk
    obtain ⟨w, hw⟩ := readAddrs_valid (pc := sk.pc) (fp := sk.fp) hn a ha
    obtain ⟨i, rfl, -⟩ := (MemoryImage.read_eq_some_iff hκ64 img).mp hw
    exact List.mem_map.mpr ⟨i, List.mem_finRange _, rfl⟩
  have hb := block_balance _ (gpow_keys_nodup κ hκ) (memMsg img) _ hmem
  -- The rows' pulls and pushes: the chained reads, and the cancelled pairs `C`, alike on both
  -- sides.
  set C := (skelRows img S).flatMap (PRow.skipMsgs img) with hC
  have h1 : ((skelRows img S).flatMap (fun r ↦ chanOf MemPush.name (r.sends img))).Perm
      (List.zipWith (fun a e ↦ memMsg img a (e + 1))
        (S.flatMap fun sk ↦ readAddrs img sk.fp sk.ins)
        (readExps (fun _ ↦ 0) (S.flatMap fun sk ↦ readAddrs img sk.fp sk.ins)) ++ C) :=
    mkRows_memPushes img (fun _ ↦ 0) (fun _ ↦ 0) S
  have h2 : ((skelRows img S).flatMap (fun r ↦ chanOf MemPull.name (r.sends img))).Perm
      (List.zipWith (fun a e ↦ memMsg img a e)
        (S.flatMap fun sk ↦ readAddrs img sk.fp sk.ins)
        (readExps (fun _ ↦ 0) (S.flatMap fun sk ↦ readAddrs img sk.fp sk.ins)) ++ C) :=
    mkRows_memPulls img (fun _ ↦ 0) (fun _ ↦ 0) S
  have hv1 : chanOf MemPush.name
      [(StatePush.name, #[1, 1]), (StatePull.name, #[prog.pcFinal, 1])] = [] :=
    chanOf_eq_nil (by simp [StatePush, StatePull, MemPush])
  have hv2 : chanOf MemPull.name
      [(StatePush.name, #[1, 1]), (StatePull.name, #[prog.pcFinal, 1])] = [] :=
    chanOf_eq_nil (by simp [StatePush, StatePull, MemPull])
  have hc1 : chanOf MemPush.name (bcBlockSends prog (skelBcFin S)) = [] :=
    chanOf_eq_nil fun x hx ↦ by
      rcases bcBlockSends_names prog _ x hx with h | h <;> simp [h, MemPush, BytecodePush,
        BytecodePull]
  have hc2 : chanOf MemPull.name (bcBlockSends prog (skelBcFin S)) = [] :=
    chanOf_eq_nil fun x hx ↦ by
      rcases bcBlockSends_names prog _ x hx with h | h <;> simp [h, MemPull, BytecodePush,
        BytecodePull]
  refine (chanOf_skelSends_perm prog img S _).trans
    (List.Perm.trans ?_ (chanOf_skelSends_perm prog img S _).symm)
  rw [hv1, hv2, hc1, hc2, memBlock_push hκ64, memBlock_pull hκ64]
  simp only [List.nil_append, List.append_nil]
  have hb' := hb
  simp only [List.map_map, Function.comp_def] at hb'
  refine (h1.append_right _).trans (List.Perm.trans ?_ (h2.append_right _).symm)
  -- The cancelled pairs ride along on both sides.
  exact perm_append_mid hb'

/-- **The bytecode pair balances**: the rows' fetches, numbered by the chain, against the block's
seeds and finalizes. -/
theorem bc_pair_perm (prog : LeanIsaProgram) {κ : ℕ} (img : MemoryImage κ) (S : List Skel)
    (hS : ∀ sk ∈ S, SkelOk prog img sk) :
    (chanOf BytecodePush.name (skelSends prog img S)).Perm
      (chanOf BytecodePull.name (skelSends prog img S)) := by
  have hmem : ∀ a ∈ S.map (·.pc),
      a ∈ (List.finRange (2 ^ prog.logSize)).map fun i : Fin (2 ^ prog.logSize) ↦
        addressOfIndex (i : ℕ) := by
    intro a ha
    obtain ⟨sk, hsk, rfl⟩ := List.mem_map.mp ha
    obtain ⟨i, hi, -⟩ := LeanIsaProgram.fetch_eq_some_iff prog |>.mp (hS sk hsk).1
    exact List.mem_map.mpr ⟨i, List.mem_finRange _, hi.symm⟩
  have hb := block_balance _ (gpow_keys_nodup prog.logSize prog.logSize_le) (bcMsg prog) _ hmem
  have hF : ∀ sk ∈ S, prog.fetch sk.pc = some sk.ins := fun sk h ↦ (hS sk h).1
  have h1 : (skelRows img S).flatMap (fun r ↦ chanOf BytecodePush.name (r.sends img)) =
      List.zipWith (fun pc e ↦ bcMsg prog pc (e + 1)) (S.map (·.pc))
        (readExps (fun _ ↦ 0) (S.map (·.pc))) :=
    mkRows_bcPushes img (fun _ ↦ 0) (fun _ ↦ 0) S hF
  have h2 : (skelRows img S).flatMap (fun r ↦ chanOf BytecodePull.name (r.sends img)) =
      List.zipWith (fun pc e ↦ bcMsg prog pc e) (S.map (·.pc))
        (readExps (fun _ ↦ 0) (S.map (·.pc))) :=
    mkRows_bcPulls img (fun _ ↦ 0) (fun _ ↦ 0) S hF
  have hv1 : chanOf BytecodePush.name
      [(StatePush.name, #[1, 1]), (StatePull.name, #[prog.pcFinal, 1])] = [] :=
    chanOf_eq_nil (by simp [StatePush, StatePull, BytecodePush])
  have hv2 : chanOf BytecodePull.name
      [(StatePush.name, #[1, 1]), (StatePull.name, #[prog.pcFinal, 1])] = [] :=
    chanOf_eq_nil (by simp [StatePush, StatePull, BytecodePull])
  have hc1 : chanOf BytecodePush.name (memBlockSends img (skelMemFin img S)) = [] :=
    chanOf_eq_nil fun x hx ↦ by
      rcases memBlockSends_names img _ x hx with h | h <;> simp [h, MemPush, MemPull,
        BytecodePush]
  have hc2 : chanOf BytecodePull.name (memBlockSends img (skelMemFin img S)) = [] :=
    chanOf_eq_nil fun x hx ↦ by
      rcases memBlockSends_names img _ x hx with h | h <;> simp [h, MemPush, MemPull,
        BytecodePull]
  refine (chanOf_skelSends_perm prog img S _).trans
    (List.Perm.trans ?_ (chanOf_skelSends_perm prog img S _).symm)
  rw [hv1, hv2, hc1, hc2, h1, h2, bcBlock_push, bcBlock_pull]
  simp only [List.nil_append, List.append_nil]
  simpa only [List.map_map, Function.comp_def, skelBcFin] using hb

/-- **The state pair balances**, from the hypothesis that the skeletons' states and successors
balance with the initial and final states: the rows' pulls and pushes are those states, regrouped
by the six tables. -/
theorem state_pair_perm (prog : LeanIsaProgram) {κ : ℕ} (img : MemoryImage κ) (S : List Skel)
    (hstate : (#[1, 1] :: S.map fun sk ↦ #[(nextOf img sk).pc, (nextOf img sk).fp]).Perm
      (#[prog.pcFinal, 1] :: S.map fun sk ↦ #[sk.pc, sk.fp])) :
    (chanOf StatePush.name (skelSends prog img S)).Perm
      (chanOf StatePull.name (skelSends prog img S)) := by
  have h1 : (skelRows img S).flatMap (fun r ↦ chanOf StatePush.name (r.sends img)) =
      S.map fun sk ↦ #[(nextOf img sk).pc, (nextOf img sk).fp] :=
    mkRows_statePushes img (fun _ ↦ 0) (fun _ ↦ 0) S
  have h2 : (skelRows img S).flatMap (fun r ↦ chanOf StatePull.name (r.sends img)) =
      S.map fun sk ↦ #[sk.pc, sk.fp] :=
    mkRows_statePulls img (fun _ ↦ 0) (fun _ ↦ 0) S
  have hv1 : chanOf StatePush.name
      [(StatePush.name, #[1, 1]), (StatePull.name, #[prog.pcFinal, 1])] = [#[1, 1]] := by
    simp [chanOf, StatePush, StatePull]
  have hv2 : chanOf StatePull.name
      [(StatePush.name, #[1, 1]), (StatePull.name, #[prog.pcFinal, 1])] =
      [#[prog.pcFinal, 1]] := by
    simp [chanOf, StatePush, StatePull]
  have hc : ∀ n, (n = StatePush.name ∨ n = StatePull.name) →
      chanOf n (memBlockSends img (skelMemFin img S)) = [] ∧
        chanOf n (bcBlockSends prog (skelBcFin S)) = [] := by
    intro n hn
    refine ⟨chanOf_eq_nil fun x hx ↦ ?_, chanOf_eq_nil fun x hx ↦ ?_⟩
    · rcases memBlockSends_names img _ x hx with h | h <;>
        rcases hn with rfl | rfl <;> simp [h, StatePush, StatePull, MemPush, MemPull]
    · rcases bcBlockSends_names prog _ x hx with h | h <;>
        rcases hn with rfl | rfl <;> simp [h, StatePush, StatePull, BytecodePush, BytecodePull]
  obtain ⟨hm1, hb1⟩ := hc _ (Or.inl rfl)
  obtain ⟨hm2, hb2⟩ := hc _ (Or.inr rfl)
  refine (chanOf_skelSends_perm prog img S _).trans
    (List.Perm.trans ?_ (chanOf_skelSends_perm prog img S _).symm)
  rw [hv1, hv2, hm1, hb1, hm2, hb2, h1, h2]
  simpa only [List.append_nil, List.singleton_append] using hstate

/-! ## The constraints -/

/-- The `JUMP` row circuit's constraints, generically: they are exactly the two residuals of the
local witnesses `w` and `b`, at slots `n` and `n + 1`. -/
theorem jump_constraints_iff (x : Var JumpRow K) (env : Environment K) (n : ℕ) (r : JumpRow K)
    (hx : eval env x = r) (w b : K) (hw : env.get n = w) (hb : env.get (n + 1) = b) :
    ((jumpTable.main x).operations n).ConstraintsHold env ↔
      b + r.vcond * w = 0 ∧ r.vcond * (b + 1) = 0 := by
  subst hx
  obtain ⟨pc, fp, oc, od, of, vcond, vpc, vfp, rc, rd, rf, rbc⟩ := x
  dsimp only [jumpTable]
  simp only [circuit_norm, memRead, bytecodeRead, -BitVec.reduceNeg]
  constructor
  · intro h
    have h1 := h _ (Or.inl rfl)
    have h2 := h _ (Or.inr rfl)
    simp only [Expression.eval, hw, hb] at h1 h2
    exact ⟨h1, h2⟩
  · rintro ⟨h1, h2⟩ e (rfl | rfl)
    · simp only [Expression.eval, hw, hb, h1]
    · simp only [Expression.eval, hb, h2]

/-- The witness slot of a `JUMP` raw row is its first witness. -/
theorem jumpRaw_get_witness (r : JumpRow K) (w b : K) (data : ProverData K) :
    (Environment.fromArray (jumpRaw r w b) data).get (size JumpRow) = w := by
  show ((rawRow r ++ #[w, b])[size JumpRow]?).getD 0 = w
  rw [Array.getElem?_append_right (by rw [rawRow_size]), rawRow_size]
  simp

/-- A `JUMP` raw row satisfies the table's constraints exactly when its witnesses satisfy the two
residuals. -/
theorem jumpRaw_constraints_iff (r : JumpRow K) (w b : K) (data : ProverData K) :
    (opcodeComponent jumpTable).operations.ConstraintsHold
        (Environment.fromArray (jumpRaw r w b) data) ↔
      b + r.vcond * w = 0 ∧ r.vcond * (b + 1) = 0 := by
  rw [Component.constraintsHold_iff]
  exact jump_constraints_iff (varFromOffset JumpRow 0) _ (size JumpRow) r
    (eval_rowVar_append r #[w, b] data) w b (jumpRaw_get_witness r w b data)
    (jumpRaw_get_indicator r w b data)

/-- A `JUMP` raw row whose witnesses satisfy the two residuals satisfies the table's
constraints. -/
theorem jumpRaw_constraints (r : JumpRow K) (w b : K) (h1 : b + r.vcond * w = 0)
    (h2 : r.vcond * (b + 1) = 0) (data : ProverData K) :
    (opcodeComponent jumpTable).operations.ConstraintsHold
      (Environment.fromArray (jumpRaw r w b) data) :=
  (jumpRaw_constraints_iff r w b data).mpr ⟨h1, h2⟩

/-- **Every table of the witness satisfies its constraints**: only the `JUMP` table
asserts anything, and its rows carry the honest inverse and indicator. -/
theorem skelWitness_constraints (prog : LeanIsaProgram) (input : PublicInput) {κ : ℕ}
    (img : MemoryImage κ) (S : List Skel) (hκ : κ ≤ maxLogMem)
    (hrows : ∀ op, Skel.count op S ≤ 2 ^ maxLogRows) :
    (skelWitness prog input img S hκ hrows).Constraints := by
  intro t ht row hrow
  obtain ⟨t₀, ht₀, hc, htab⟩ := mem_skelWitness_tables ht
  rw [htab] at hrow
  rw [Air.Flat.Table.environment, hc]
  generalize t.data = data
  simp only [skelTables, List.mem_cons, List.not_mem_nil, or_false] at ht₀
  rcases ht₀ with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact xor_constraints _
  · exact mul_constraints _
  · exact set_constraints _
  · exact deref_constraints _
  · obtain ⟨⟨⟨pc, fp, ins⟩, exps, bc⟩, hr, rfl⟩ := List.mem_map.mp hrow
    have h := (List.mem_filter.mp hr).2
    simp only [decide_eq_true_eq] at h
    cases ins with
    | jump oc od of =>
      obtain ⟨h1, h2⟩ := flags_complete ((img.limbsAt (fp * oc))[0])
      exact jumpRaw_constraints (jumpRowOf img pc fp oc od of _ _ _ _)
        (if (img.limbsAt (fp * oc))[0] = 0 then 0 else ((img.limbsAt (fp * oc))[0])⁻¹)
        (if (img.limbsAt (fp * oc))[0] = 0 then 0 else 1) h1 h2 _
    | xor _ _ _ => simp [LeanIsaInstruction.opcode] at h
    | mulNative _ _ _ => simp [LeanIsaInstruction.opcode] at h
    | setConstant _ _ => simp [LeanIsaInstruction.opcode] at h
    | deref _ _ _ _ => simp [LeanIsaInstruction.opcode] at h
    | keccak _ _ _ _ _ _ _ => simp [LeanIsaInstruction.opcode] at h
  · exact keccak_constraints _
  · exact mem_constraints κ _
  · exact bytecode_constraints prog _

/-! ## The verifier's checks -/

/-- Every pull of a row's read carries a nonzero count, when the row's counts are nonzero. -/
theorem sendsOf_counts_ne_zero {pc fp : K} {next : Registers K} {rbc : K} {e : Vector K 13}
    {reads : List (K × K × Vector K 3)} (hb : rbc ≠ 0) (hr : ∀ x ∈ reads, x.2.1 ≠ 0) :
    ∀ y ∈ sendsOf pc fp next rbc e reads,
      (y.1 = MemPull.name ∨ y.1 = BytecodePull.name) → ∃ h : 1 < y.2.size, y.2[1] ≠ 0 := by
  intro y hy hn
  simp only [sendsOf, List.mem_append, List.mem_cons, List.not_mem_nil, or_false,
    List.mem_flatMap] at hy
  rcases hy with (rfl | rfl | rfl | rfl) | ⟨x, hx, rfl | rfl⟩
  · simp [StatePull, MemPull, BytecodePull] at hn
  · simp [StatePush, MemPull, BytecodePull] at hn
  · exact ⟨by simp [bcMsgOf], by simpa [bcMsgOf] using hb⟩
  · simp [BytecodePush, MemPull, BytecodePull] at hn
  · exact ⟨by simp [memMsgOf], by simpa [memMsgOf] using hr x hx⟩
  · simp [MemPush, MemPull, BytecodePull] at hn

/-- A row of the witness has nonzero counts: they are powers of `g`. -/
theorem PRow.sends_counts_ne_zero {κ : ℕ} (img : MemoryImage κ) (r : PRow) :
    ∀ y ∈ r.sends img,
      (y.1 = MemPull.name ∨ y.1 = BytecodePull.name) → ∃ h : 1 < y.2.size, y.2[1] ≠ 0 := by
  intro y hy hn
  rcases List.mem_append.mp hy with hy | hy
  · refine sendsOf_counts_ne_zero (pow_ne_zero _ g_ne_zero) (fun x hx ↦ ?_) y hy hn
    simp only [readsOf, List.mem_mapIdx] at hx
    obtain ⟨j, -, rfl⟩ := hx
    exact pow_ne_zero _ g_ne_zero
  · -- A cancelled pair's count is a count of the row, a power of `g`.
    have hcnt : ∀ x ∈ skipsOf img r.sk.fp r.cnt r.sk.ins, x.2.1 ≠ 0 := by
      intro x hx
      cases hins : r.sk.ins <;> rw [hins] at hx <;> simp only [skipsOf, List.not_mem_nil] at hx
      obtain ⟨c, -, rfl⟩ := List.mem_map.mp hx
      exact pow_ne_zero _ g_ne_zero
    simp only [skipSends, List.mem_flatMap, List.mem_cons, List.not_mem_nil, or_false] at hy
    obtain ⟨x, hx, rfl | rfl⟩ := hy
    · exact ⟨by simp [memMsgOf], by simpa [memMsgOf] using hcnt x hx⟩
    · simp [MemPush, MemPull, BytecodePull] at hn

/-- An interaction of a table is among the sends of its rows. -/
theorem mem_interactions_sends (t : Air.Flat.Table K) {i : Interaction K}
    (hi : i ∈ t.interactions) :
    (i.channel.name, i.msg) ∈ t.table.flatMap fun row ↦
      rowSends t.component (t.environment row) := by
  unfold Air.Flat.Table.interactions at hi
  obtain ⟨row, hrow, hi⟩ := List.mem_flatMap.mp hi
  rw [Component.interactionsValues_eq] at hi
  exact List.mem_flatMap.mpr ⟨row, hrow,
    List.mem_map_of_mem (f := fun i : Interaction K ↦ (i.channel.name, i.msg)) hi⟩

/-- **Every read pull of the six tables carries a nonzero count.** -/
theorem skelWitness_counts_nonzero (prog : LeanIsaProgram) (input : PublicInput) {κ : ℕ}
    (img : MemoryImage κ) (S : List Skel) (hκ : κ ≤ maxLogMem)
    (hrows : ∀ op, Skel.count op S ≤ 2 ^ maxLogRows)
    (hS : ∀ sk ∈ S, ∃ next, execute img sk.regs sk.ins = some next) :
    CountsNonzero (skelWitness prog input img S hκ hrows) := by
  have hR : ∀ r ∈ skelRows img S, ∃ next, execute img r.sk.regs r.sk.ins = some next :=
    fun r hr ↦ hS _ (mem_mkRows_sk hr)
  intro t ht i hi hn h
  -- The first six tables of the witness are the opcode tables, but for their data.
  have hm : (t.component, t.table) ∈
      ((skelWitness prog input img S hκ hrows).tables.take 6).map
        fun t ↦ (t.component, t.table) := List.mem_map_of_mem ht
  rw [List.map_take] at hm
  change (t.component, t.table) ∈ ((skelWitnessTables prog img S hκ hrows).map
    fun t ↦ (t.component, t.table)).take 6 at hm
  rw [skelWitnessTables_map, ← List.map_take, List.mem_map] at hm
  obtain ⟨t₀, ht₀, he⟩ := hm
  have hop : ∃ op, t₀.component = opComponent op ∧ t₀.table = opRows img (skelRows img S) op := by
    simp only [skelTables, List.take, List.mem_cons, List.not_mem_nil, or_false] at ht₀
    rcases ht₀ with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [⟨.xor, rfl, rfl⟩, ⟨.mulNative, rfl, rfl⟩, ⟨.setConstant, rfl, rfl⟩,
      ⟨.deref, rfl, rfl⟩, ⟨.jump, rfl, rfl⟩, ⟨.keccak, rfl, rfl⟩]
  obtain ⟨op, hc, htab⟩ := hop
  have hmem := mem_interactions_sends _ hi
  obtain ⟨hc', htab'⟩ := Prod.mk.inj he
  rw [← hc', ← htab'] at hmem
  simp only [Air.Flat.Table.environment] at hmem
  rw [hc, htab, opRows_sends img _ op _ hR] at hmem
  obtain ⟨r, -, hr⟩ := List.mem_flatMap.mp hmem
  obtain ⟨h', hne⟩ := PRow.sends_counts_ne_zero img _ _ hr hn
  exact hne

/-! ## The blocks, the compression and the words -/

/-- **Every `KECCAK` row permutes**: the row of an executing instruction satisfies the relation
its execution checks. -/
theorem skelWitness_keccak_valid (prog : LeanIsaProgram) (input : PublicInput) {κ : ℕ}
    (img : MemoryImage κ) (S : List Skel) (hκ : κ ≤ maxLogMem)
    (hrows : ∀ op, Skel.count op S ≤ 2 ^ maxLogRows)
    (hS : ∀ sk ∈ S, ∃ next, execute img sk.regs sk.ins = some next) :
    KeccakRowsValid (skelWitness prog input img S hκ hrows) := by
  intro row hrow
  have hrow' : row ∈ opRows img (skelRows img S) .keccak := by
    rw [keccakRows, skelWitness_tableAt_table prog input img S hκ hrows 5] at hrow
    exact hrow
  obtain ⟨⟨⟨pc, fp, ins⟩, exps, bc⟩, hr, rfl⟩ := List.mem_map.mp hrow'
  obtain ⟨hr1, hr2⟩ := List.mem_filter.mp hr
  simp only [decide_eq_true_eq] at hr2
  obtain ⟨next, hn⟩ := hS _ (mem_mkRows_sk hr1)
  cases ins with
  | keccak om otail ob8 ocap oout inOdd outOdd outCells =>
    simp only [PRow.raw, rowOf, rawRow]
    rw [keccakRowAt_toElements]
    exact keccakRowOf_relation ..
  | xor _ _ _ => simp [LeanIsaInstruction.opcode] at hr2
  | mulNative _ _ _ => simp [LeanIsaInstruction.opcode] at hr2
  | setConstant _ _ => simp [LeanIsaInstruction.opcode] at hr2
  | deref _ _ _ _ => simp [LeanIsaInstruction.opcode] at hr2
  | jump _ _ _ => simp [LeanIsaInstruction.opcode] at hr2

/-- **The public words are the image's first two words.** -/
theorem skelWitness_words (prog : LeanIsaProgram) (input : PublicInput) {κ : ℕ}
    (img : MemoryImage κ) (S : List Skel) (hκ : κ ≤ maxLogMem)
    (hrows : ∀ op, Skel.count op S ≤ 2 ^ maxLogRows)
    (hw0 : img.read (addressOfIndex 0) = some input.word0)
    (hw1 : img.read (addressOfIndex 1) = some input.word1) :
    (imageOf (skelWitness prog input img S hκ hrows).data).2.read (addressOfIndex 0) =
        some input.word0 ∧
      (imageOf (skelWitness prog input img S hκ hrows).data).2.read (addressOfIndex 1) =
        some input.word1 := by
  rw [imageOf_skelWitness]
  exact ⟨hw0, hw1⟩

/-! ## The caps -/

/-- **The announced sizes are within the caps**: the memory window and every table within the row
cap. -/
theorem skelWitness_caps (prog : LeanIsaProgram) (input : PublicInput) {κ : ℕ}
    (img : MemoryImage κ) (S : List Skel) (hκmin : minLogMem ≤ κ) (hκ : κ ≤ maxLogMem)
    (hrows : ∀ op, Skel.count op S ≤ 2 ^ maxLogRows) :
    Caps (skelWitness prog input img S hκ hrows) where
  minLogMem_le_logMem := hκmin
  logMem_le_maxLogMem := hκ
  heights := by
    intro t ht
    obtain ⟨t₀, ht₀, -, htab⟩ := mem_skelWitness_tables ht
    rw [htab]
    have hop : ∀ op, (opRows img (skelRows img S) op).length ≤ 2 ^ maxLogRows := fun op ↦ by
      rw [opRows, List.length_map, skelRows, length_filter_mkRows]
      exact hrows op
    simp only [skelTables, List.mem_cons, List.not_mem_nil, or_false] at ht₀
    rcases ht₀ with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hop _
    · exact hop _
    · exact hop _
    · exact hop _
    · exact hop _
    · exact hop _
    · show (memBlockRaw img _).length ≤ _
      rw [memBlockRaw, List.length_ofFn]
      exact Nat.pow_le_pow_right (by norm_num) (hκ.trans (by decide))
    · show (bcBlockRaw prog _).length ≤ _
      rw [bcBlockRaw, List.length_ofFn]
      exact Nat.pow_le_pow_right (by norm_num) (prog.logSize_le.trans (by decide))

/-! ## The witness satisfies the statement -/

/-- The messages the witness sends on a channel. -/
theorem messagesOn_skelWitness (prog : LeanIsaProgram) (input : PublicInput) {κ : ℕ}
    (img : MemoryImage κ) (S : List Skel) (hκ : κ ≤ maxLogMem)
    (hrows : ∀ op, Skel.count op S ≤ 2 ^ maxLogRows)
    (hS : ∀ sk ∈ S, ∃ next, execute img sk.regs sk.ins = some next) (c : RawChannel K) :
    messagesOn (skelWitness prog input img S hκ hrows) c = chanOf c.name (skelSends prog img S) := by
  rw [messagesOn_eq_sends, skelWitness_sends prog input img S hκ hrows hS]
  rfl

/-- **The witness of a list of skeletons satisfies the constraint statement.** When the skeletons
`S` are sound for the program and the image, their state pulls and pushes balance with the
initial and final states, every table has at most `2^maxLogRows` rows, the memory log-size is in
the window and the image has the two public words, `skelWitness prog input img S hκ hrows`
satisfies every conjunct of `SatisfiedBy`. -/
theorem skelWitness_satisfiedBy (prog : LeanIsaProgram) (input : PublicInput) {κ : ℕ}
    (img : MemoryImage κ) (S : List Skel) (hκmin : minLogMem ≤ κ) (hκ : κ ≤ maxLogMem)
    (hS : ∀ sk ∈ S, SkelOk prog img sk)
    (hstate : (#[1, 1] :: S.map fun sk ↦ #[(nextOf img sk).pc, (nextOf img sk).fp]).Perm
      (#[prog.pcFinal, 1] :: S.map fun sk ↦ #[sk.pc, sk.fp]))
    (hrows : ∀ op, Skel.count op S ≤ 2 ^ maxLogRows)
    (hw0 : img.read (addressOfIndex 0) = some input.word0)
    (hw1 : img.read (addressOfIndex 1) = some input.word1) :
    SatisfiedBy prog input (skelWitness prog input img S hκ hrows) := by
  have hex : ∀ sk ∈ S, ∃ next, execute img sk.regs sk.ins = some next := fun sk h ↦ (hS sk h).2
  obtain ⟨hwa, hwb⟩ := skelWitness_words prog input img S hκ hrows hw0 hw1
  have hm := messagesOn_skelWitness prog input img S hκ hrows hex
  exact
    { public_input_eq := rfl
      constraints := skelWitness_constraints prog input img S hκ hrows
      state_balanced := by
        unfold BalancedPair
        rw [hm, hm]
        exact state_pair_perm prog img S hstate
      mem_balanced := by
        unfold BalancedPair
        rw [hm, hm]
        exact mem_pair_perm prog hκ img S hex
      bytecode_balanced := by
        unfold BalancedPair
        rw [hm, hm]
        exact bc_pair_perm prog img S hS
      counts_nonzero := skelWitness_counts_nonzero prog input img S hκ hrows hex
      caps := skelWitness_caps prog input img S hκmin hκ hrows
      keccak_valid := skelWitness_keccak_valid prog input img S hκ hrows hex
      word0_eq := hwa
      word1_eq := hwb }

end LeanVM.Arithmetization
