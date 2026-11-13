import LeanVMTests.Arithmetization.Statement

/-!
# Tests: the constraint statement, rejections

The rejections, each the honest witness of `Statement.lean` with one thing changed, and each failing exactly the
conjunct named. A wrong finalize count unbalances the memory pair (§6.2 "Nothing checks the
finalize counts"): cell `4`'s finalize count `1` instead of `g`. A read count of `0` that
*balances* fails `CountsNonzero` alone (§6.2 "The count product"): the first `SET_CONSTANT`
row reads `x` with count `0`, a pull and a push of one tuple, the product row then reads `x`
first, and every other conjunct still holds (`zero_count_witness`). A wrong output lane, written
consistently in the `KECCAK` row and in the image, fails `KeccakRowsValid` alone
(`wrong_lane_witness`): the bus binds the lanes to the cells, not the permutation, and the table
has no constraint; the permutation is the Keccak reduction's. A memory block whose index column
is shifted fails `IndexColumnsAreRowIndices` (§6.5). A wrong public word fails `word0_eq`
(§8.2). A three-row table and a four-row `KECCAK` table are within `Caps`: a table's row count
need not be a power of two, and there is no `KECCAK` floor (`Caps` bounds the memory log-size and
each table's rows by `2^MAX_LOG_ROWS` only; the protocol pads every table with public padding
rows, `doc/leanvm` §`sec:e2e-pad`).
-/

-- The kernel decisions one at a time, as in `Statement.lean`.
set_option Elab.async false

namespace LeanVMTests.Arithmetization.Statement

open LeanVM.Parameters LeanVM.Semantics LeanVM.Arithmetization
open Air.Flat (Component EnsembleWitness)

/-! ## Rejections -/

/-- A wrong finalize count: cell `4` is read once, its finalize count `1` instead of `g`. -/
def wrongCnt (i : ℕ) : K := if i = 4 then 1 else memCnt i

theorem wrongCnt_of_ge {i : ℕ} (h : 44 ≤ i) : wrongCnt i = 1 := by
  unfold wrongCnt
  rw [ite_eq_right (by omega), memCnt_of_ge h]

/-- Nothing checks the finalize counts (§6.2): the block accepts the row, and the bus does not
balance. -/
example : ¬ BalancedPair (walkW kLout 1 g wrongCnt) MemPull.toRaw MemPush.toRaw := by
  rw [mem_balanced_iff kLout 1 g wrongCnt fun _ ↦ wrongCnt_of_ge]
  keccak_sends_closed
  decide +kernel

/-- The finalize counts of a read count `0` at cell `2`: the first `SET_CONSTANT` row's read
pulls and pushes `(g^2, 0, x)`, the product row's read is then the first, and the cell is
finalized at `g`. -/
def zeroCnt (i : ℕ) : K := if i = 2 then g else memCnt i

theorem zeroCnt_of_ge {i : ℕ} (h : 44 ≤ i) : zeroCnt i = 1 := by
  unfold zeroCnt
  rw [ite_eq_right (by omega), memCnt_of_ge h]

/-- The zero-count witness balances the memory pair: a pull and a push of one tuple cancel,
which is what the count product exists to reject (§6.2 "The count product", Theorem 6.4). -/
theorem zero_mem_balanced :
    BalancedPair (walkW kLout 0 1 zeroCnt) MemPull.toRaw MemPush.toRaw := by
  rw [mem_balanced_iff kLout 0 1 zeroCnt fun _ ↦ zeroCnt_of_ge]
  keccak_sends_closed
  decide +kernel

theorem zero_state_balanced :
    BalancedPair (walkW kLout 0 1 zeroCnt) StatePull.toRaw StatePush.toRaw := by
  unfold BalancedPair
  simp only [messagesOn_walkW, List.flatMap_cons, List.flatMap_nil, List.append_nil,
    List.filter_append, List.map_append,
    memT_filter _ _ _ StatePush.toRaw.name (by decide) (by decide),
    memT_filter _ _ _ StatePull.toRaw.name (by decide) (by decide),
    bcT_filter _ StatePush.toRaw.name (by decide) (by decide),
    bcT_filter _ StatePull.toRaw.name (by decide) (by decide)]
  keccak_sends_closed
  decide +kernel

theorem zero_bytecode_balanced :
    BalancedPair (walkW kLout 0 1 zeroCnt) BytecodePull.toRaw BytecodePush.toRaw := by
  unfold BalancedPair
  simp only [messagesOn_walkW, List.flatMap_cons, List.flatMap_nil, List.append_nil,
    List.filter_append, List.map_append,
    memT_filter _ _ _ BytecodePush.toRaw.name (by decide) (by decide),
    memT_filter _ _ _ BytecodePull.toRaw.name (by decide) (by decide)]
  keccak_sends_closed
  bytecode_sends_closed
  decide +kernel

/-- The count product is load-bearing: the zero-count witness satisfies every other conjunct
of `SatisfiedBy` and fails `CountsNonzero` (§6.2 "The count product"). -/
theorem zero_count_witness :
    (walkW kLout 0 1 zeroCnt).publicInput = PublicIO.ofInput mulInput ∧
    (walkW kLout 0 1 zeroCnt).Constraints ∧
    BalancedPair (walkW kLout 0 1 zeroCnt) StatePull.toRaw StatePush.toRaw ∧
    BalancedPair (walkW kLout 0 1 zeroCnt) MemPull.toRaw MemPush.toRaw ∧
    BalancedPair (walkW kLout 0 1 zeroCnt) BytecodePull.toRaw BytecodePush.toRaw ∧
    Caps (walkW kLout 0 1 zeroCnt) ∧ IndexColumnsAreRowIndices (walkW kLout 0 1 zeroCnt) ∧
    SeedRowsAreTheImage (walkW kLout 0 1 zeroCnt) ∧
    BytecodeRowsAreTheProgram walkProg (walkW kLout 0 1 zeroCnt) ∧
    KeccakRowsValid (walkW kLout 0 1 zeroCnt) ∧
    (imageOf (walkW kLout 0 1 zeroCnt).data).2.read (addressOfIndex 0) = some mulInput.word0 ∧
    (imageOf (walkW kLout 0 1 zeroCnt).data).2.read (addressOfIndex 1) = some mulInput.word1 ∧
    ¬ CountsNonzero (walkW kLout 0 1 zeroCnt) :=
  ⟨rfl, walk_constraints kLout 0 1 zeroCnt, zero_state_balanced, zero_mem_balanced,
    zero_bytecode_balanced, walk_caps kLout 0 1 zeroCnt, walk_indexColumns kLout 0 1 zeroCnt,
    walk_seedRows kLout 0 1 zeroCnt, walk_bytecodeRows kLout 0 1 zeroCnt,
    walk_keccakValid 0 1 zeroCnt, walk_word0 kLout 0 1 zeroCnt, walk_word1 kLout 0 1 zeroCnt,
    fun h ↦ by
      have hmem : tableAt (walkW kLout 0 1 zeroCnt) 2 ∈ (walkW kLout 0 1 zeroCnt).tables.take 6 := by
        rw [List.mem_take_iff_getElem]
        exact ⟨2, by rw [← (walkW kLout 0 1 zeroCnt).same_length]; decide, rfl⟩
      have h2 := h _ hmem
      rw [table_interactions_eq, walk_table2, tableAt_component] at h2
      revert h2
      decide +kernel⟩

/-- A wrong output lane: lane `0` plus one, a canonical word, written consistently in the
`KECCAK` row and in its output cell `0` of the image (cell `25`). -/
def wrongLout : Vector K 25 := kLout.set 0 (kLout[0] + 1)

/-- The wrong row fails the relation: its lane `0` is not Keccak-f[1600]'s. -/
theorem kRow_wrong_no_relation : ¬ KeccakRelation (kRow wrongLout) := by
  intro h
  exact absurd ((congrFun h 0).trans (keccak_lanes 0)) (by decide +kernel)

/-- The permutation is checked (§8.6): the wrong output lane fails `KeccakRowsValid`. -/
theorem wrong_lane_not_valid : ¬ KeccakRowsValid (walkW wrongLout 1 g memCnt) := fun h ↦
  kRow_wrong_no_relation (by
    have hrel := h (rawRow (kRow wrongLout)) (by
      rw [keccakRows, walk_table5]
      exact List.mem_cons_self)
    rwa [rawRow, keccakRowAt_toElements] at hrel)

theorem wrong_mem_balanced :
    BalancedPair (walkW wrongLout 1 g memCnt) MemPull.toRaw MemPush.toRaw := by
  rw [mem_balanced_iff wrongLout 1 g memCnt fun _ ↦ memCnt_of_ge]
  keccak_sends_closed
  decide +kernel

theorem wrong_state_balanced :
    BalancedPair (walkW wrongLout 1 g memCnt) StatePull.toRaw StatePush.toRaw := by
  unfold BalancedPair
  simp only [messagesOn_walkW, List.flatMap_cons, List.flatMap_nil, List.append_nil,
    List.filter_append, List.map_append,
    memT_filter _ _ _ StatePush.toRaw.name (by decide) (by decide),
    memT_filter _ _ _ StatePull.toRaw.name (by decide) (by decide),
    bcT_filter _ StatePush.toRaw.name (by decide) (by decide),
    bcT_filter _ StatePull.toRaw.name (by decide) (by decide)]
  keccak_sends_closed
  decide +kernel

theorem wrong_bytecode_balanced :
    BalancedPair (walkW wrongLout 1 g memCnt) BytecodePull.toRaw BytecodePush.toRaw := by
  unfold BalancedPair
  simp only [messagesOn_walkW, List.flatMap_cons, List.flatMap_nil, List.append_nil,
    List.filter_append, List.map_append,
    memT_filter _ _ _ BytecodePush.toRaw.name (by decide) (by decide),
    memT_filter _ _ _ BytecodePull.toRaw.name (by decide) (by decide)]
  keccak_sends_closed
  bytecode_sends_closed
  decide +kernel

/-- The permutation is the Keccak reduction's alone (§8.6): the witness with the wrong output
lane, consistent in the row and in the image, satisfies every other conjunct of `SatisfiedBy`
and fails `KeccakRowsValid`. It fails no constraint: the table has none (`keccak_constraints`),
and the bus binds the lanes to the cells, which hold the wrong lane too. -/
theorem wrong_lane_witness :
    (walkW wrongLout 1 g memCnt).publicInput = PublicIO.ofInput mulInput ∧
    (walkW wrongLout 1 g memCnt).Constraints ∧
    BalancedPair (walkW wrongLout 1 g memCnt) StatePull.toRaw StatePush.toRaw ∧
    BalancedPair (walkW wrongLout 1 g memCnt) MemPull.toRaw MemPush.toRaw ∧
    BalancedPair (walkW wrongLout 1 g memCnt) BytecodePull.toRaw BytecodePush.toRaw ∧
    CountsNonzero (walkW wrongLout 1 g memCnt) ∧
    Caps (walkW wrongLout 1 g memCnt) ∧ IndexColumnsAreRowIndices (walkW wrongLout 1 g memCnt) ∧
    SeedRowsAreTheImage (walkW wrongLout 1 g memCnt) ∧
    BytecodeRowsAreTheProgram walkProg (walkW wrongLout 1 g memCnt) ∧
    (imageOf (walkW wrongLout 1 g memCnt).data).2.read (addressOfIndex 0) = some mulInput.word0 ∧
    (imageOf (walkW wrongLout 1 g memCnt).data).2.read (addressOfIndex 1) = some mulInput.word1 ∧
    ¬ KeccakRowsValid (walkW wrongLout 1 g memCnt) :=
  ⟨rfl, walk_constraints wrongLout 1 g memCnt, wrong_state_balanced, wrong_mem_balanced,
    wrong_bytecode_balanced, mkW_countsNonzero _ _ (by
      simp only [List.take_succ_cons, List.take_zero, List.forall_mem_cons, List.not_mem_nil,
        IsEmpty.forall_iff, implies_true, and_true]
      keccak_sends_closed
      decide +kernel),
    walk_caps wrongLout 1 g memCnt, walk_indexColumns wrongLout 1 g memCnt,
    walk_seedRows wrongLout 1 g memCnt, walk_bytecodeRows wrongLout 1 g memCnt,
    walk_word0 wrongLout 1 g memCnt, walk_word1 wrongLout 1 g memCnt, wrong_lane_not_valid⟩

/-- The memory block with its index column shifted by one row. -/
def memRowArrShift (i : Fin (2 ^ 16)) : Array K :=
  rawRow (⟨#v[(walkImage kLout i).limb 0, (walkImage kLout i).limb 1],
    addressOfIndex (i + 1), memCnt i⟩ : MemRow K)

/-- The index column is fixed (§6.5): rows whose row `0` carries `g^1` disagree with the memory
block's fixed column, so they are the rows of no witness's memory block (Clean's
`fixed_rows_match`; a hypothesis of the statement, `IndexColumnsAreRowIndices`, before Clean's
fixed columns). -/
example : ¬ (memComponent 16).FixedRowsMatch (List.ofFn memRowArrShift) := fun h ↦ by
  have h0 := (show (List.ofFn memRowArrShift).length = (UInt64.ofNat (2 ^ 16)).toNat ∧
    ∀ i (hi : i < (List.ofFn memRowArrShift).length), (memMode 16).FixedAt
      (UInt64.ofNat i) (fromElements (Air.Flat.rowPrefix (size MemRow)
        (List.ofFn memRowArrShift)[i])) from h).2 0 (by rw [List.length_ofFn]; decide)
  rw [memMode_fixedAt (by decide), List.getElem_ofFn, memRowArrShift,
    fromElements_rowPrefix_rawRow] at h0
  revert h0
  decide +kernel

/-- The bytecode block with slot `1`'s row in slot `0`. -/
def bcRowsWrong : List (Array K) :=
  List.ofFn fun i : Fin (2 ^ walkProg.logSize) ↦
    rawRow (bytecodeRowOf walkProg (if (i : ℕ) = 0 then 1 else i) (bcCntFin i))

/-- The bytecode block is fixed to the program (§8.6): a block whose slot `0` holds slot `1`'s
entry disagrees with the fixed counter and entry columns (a hypothesis of the statement,
`BytecodeRowsAreTheProgram`, before Clean's fixed columns). -/
example : ¬ (bytecodeComponent walkProg).FixedRowsMatch bcRowsWrong := fun h ↦ by
  have h0 := (show bcRowsWrong.length = (UInt64.ofNat (2 ^ walkProg.logSize)).toNat ∧
    ∀ i (hi : i < bcRowsWrong.length), (bytecodeMode walkProg).FixedAt (UInt64.ofNat i)
      (fromElements (Air.Flat.rowPrefix (size BytecodeRow) bcRowsWrong[i])) from h).2 0
    (by rw [bcRowsWrong, List.length_ofFn]; decide)
  rw [bytecodeMode_fixedAt walkProg (by decide)] at h0
  have e : bcRowsWrong[0]'(by rw [bcRowsWrong, List.length_ofFn]; decide) =
      rawRow (bytecodeRowOf walkProg 1 (bcCntFin 0)) := by
    simp only [bcRowsWrong, List.getElem_ofFn]
    rfl
  rw [e, fromElements_rowPrefix_rawRow] at h0
  have := congrArg BytecodeRow.idx h0
  revert this
  decide +kernel

/-- The public words are checked (§8.2): `input₀ = 3` in place of `1` fails `word0_eq`. -/
example : ¬ SatisfiedBy walkProg ⟨![K.ofBits 3, 0, K.ofBits 2, 0]⟩ (walkW kLout 1 g memCnt) :=
  fun h ↦ by
    have h0 := h.word0_eq
    rw [walk_word0] at h0
    have h1 := congrArg (fun o : Option E ↦ (o.getD 0).limb 0) h0
    revert h1
    decide +kernel

/-- A three-row `SET_CONSTANT` table, not a power of two. -/
def setT3 : Air.Flat.Table K :=
  opT setTable ([setRow0 1, setRow1, setRow1].map rawRow) (rawRows_size [setRow0 1, setRow1, setRow1])

def heightW : EnsembleWitness (leanIsaEnsemble walkProg 16) :=
  mkW [xorT, mulT g, setT3, derefT, jumpT, kT kLout, memT kLout memCnt, bcT]

/-- A row count that is not a power of two is within the caps (`crates/verifier/src/layout.rs`,
`build_layout`, at `3a37fb6e1`: a table's height is the least power of two holding its rows):
`Caps` bounds each table's rows by `2^MAX_LOG_ROWS` and nothing else. -/
example : Caps heightW := by
  refine mkW_caps _ _ fun t ht ↦ ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · rw [memT_table, List.length_ofFn]; decide
  · rw [show bcT.table = bcRows by dsimp only [bcT, ownTable], bcRows, List.length_ofFn]; decide

/-- Four `KECCAK` rows, the honest row repeated. -/
def kT4 : Air.Flat.Table K :=
  opT keccakTable ((List.replicate 4 (kRow kLout)).map rawRow)
    (rawRows_size (List.replicate 4 (kRow kLout)))

def floorW : EnsembleWitness (leanIsaEnsemble walkProg 16) :=
  mkW [xorT, mulT g, setT 1, derefT, jumpT, kT4, memT kLout memCnt, bcT]

/-- There is no `KECCAK` floor: four rows are within the caps. -/
example : Caps floorW := by
  refine mkW_caps _ _ fun t ht ↦ ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · rw [memT_table, List.length_ofFn]; decide
  · rw [show bcT.table = bcRows by dsimp only [bcT, ownTable], bcRows, List.length_ofFn]; decide

end LeanVMTests.Arithmetization.Statement
