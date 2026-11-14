/-
  LeanVM.Arithmetization.Boundary

  The three bus blocks owned by no table: the memory seed/finalize block, the bytecode
  seed/finalize block, and the verifier's state boundary, each a Clean component, sound and
  complete for what its interactions say.
-/

module

public import LeanVM.Arithmetization.Tables.Basic
public import LeanVM.Semantics.Lemmas
public import Clean.Circuit.Formal
public import Clean.Air.FlatComponent
public import Clean.Air.Verifier
public import Clean.Utils.Tactics.CircuitProofStart

@[expose] public section

/-!
# The boundary blocks

At leanVM pin `127510d14c98ade4e8a97646c44fa7f1ff5e752d` and Clean pin `b41c196b`. The three
blocks are `crates/leanvm_core/src/cpu/layout.rs` (the "shared blocks" of `layout`),
matching specification §6.1 (`doc/leanvm/body/06-bus-interactions.tex`, the state boundary),
§6.2 "Flush rules" (seed and finalize), §6.4 (the bytecode array), §6.5 (the
index column), and §8.6 (`08-end-to-end-protocol.tex`: "three blocks per side belong to no
table"). The committed
columns are `MEM_LO, MEM_HI, MFCNT` and `BFCNT` (`layout.rs`); the bytecode entry
rides eight *public* columns (`bytecode_columns`, `layout.rs`, `Bytecode`'s `entry`); the
sentinel counter `g^(N_prog - 1)` is derived from the public program's length and written into the
state block as a constant (`layout.rs`, `final_pc`, `Const(g_pow(final_pc))`).

**The three blocks.** Every row of an opcode table pulls its state and pushes its successor,
and reads its cells and its instruction through the counted lookup of §6.2. What closes the
three channel pairs are the boundary blocks: the *memory block* pushes each word of the image
once, as `(g^i, 1, mem[i])`, and pulls it back with its final count, `(g^i, g^(A[i]), mem[i])`;
the *bytecode block* does the same for each slot of the public program; the *verifier* pushes
the initial state `(1, 1)` and pulls the final state `(g^(N_prog - 1), 1)`. None has a
constraint: each is its two flushes.

**The rows.** `MemRow` is the memory block's row: the word's two limbs `m`, first, as the
committed columns are, so that the prover data Clean derives from the block is the image, the
address `idx` (the index column of §6.5, which the verifier computes: a fixed column), and the
finalize count `cntFin`; `BytecodeRow` is the bytecode block's: the counter `idx`, the finalize
count, and the entry as the opcode and the twelve operand slots, in the order of `BytecodeMsg`.

**The blocks as components.** Both blocks are preallocated (`memComponent κ`, `bytecodeComponent
prog`): one row per word of a memory of `2^κ` words and one per slot of the program, in order. Their
index columns are fixed to `g^i`, and the bytecode block's entry columns to the program's
(`fixedColumn`), which is what the verifier computes itself (§6.5; §8.6 Bus 4, `Coord::Public`);
`memMode_fixedAt` and `bytecodeMode_fixedAt` read the fixed cells of a row. `PublicIO` is what the verifier reads off the public data:
the four lanes of the public input (§2, §8.2), and `PublicIO.ofInput input` is the public input
of a run, which `SatisfiedBy` requires of the witness. The verifier is a `Verifier.Program` of the
public program, `leanIsaVerifier prog`, and pulls `Expression.const prog.pcFinal`: leanVM's
`layout(prog, …)` derives the counter from the program and writes it into the block as a
constant, so here it is a constant of the verifier, never a column and never a public
coordinate, and the statement's ensemble is `leanIsaEnsemble prog κ`.

**The specifications.** A block's `Spec` is what its pull guarantees (`Channels`): `MemSpec r
data` says the row is bound to the image the data names, `MemBindings (imageOf data).2 r`, the
cell at `idx` holding the row's word `E.ofLimbs m[0] m[1]`; `BytecodeDecodes r` says the
row's entry decodes to an instruction (`decode`), the program-free guarantee of the bytecode
pull, which reads no data. The program is not the circuit's to name: the block's rows are the
public program's entries because its fixed columns are (§8.6, Bus 4; `Coord::Public`), which the
statement reads as `BytecodeRowsAreTheProgram prog`, a theorem, that the block's rows are
`bytecodeRowOf prog i cntFin` for every slot `i` with some finalize count.
`BytecodeBindings prog r` is its per-row reading, the program fetching at `idx` an instruction the
row's entry decodes to: proved of every `bytecodeRowOf` row (`bytecodeRowOf_bindings`), derived
for every seed row by `Soundness`, and never the circuit's `Spec`, since the program is public and
never prover data. The verifier's
`Spec` is `True`: the state pull carries no guarantee, since a pulled state need not be
reachable (a closed walk balances), and what the state boundary yields, a run from `(1, 1)` to
`(g^(N_prog - 1), 1)` inside a balanced bus, is `exists_run_of_balanced`, stated once, from
balance, never per component. Access counts are outside every specification: nothing checks a
finalize count (§6.2, "Nothing checks the finalize counts"), and a wrong one can only unbalance
the bus.

**Soundness and completeness.** Soundness assumes the guarantee of the block's pull and
concludes `Spec`, which is that guarantee; the requirement of its push is vacuous. The
honest-prover premise is `Spec` itself, and nothing above this file assumes it: `memRowOf mem i
cntFin` is the seed row of word `i` of an image and `bytecodeRowOf prog i cntFin` the seed row
of slot `i` of a program, `memRowOf_bindings` proves the word's row bound and
`bytecodeRowOf_decodes` the slot's row decodable, with any finalize count, and
`mem_word_complete` and `bytecode_entry_complete` push them through `completeness` over the
prover data: every word of the image and every slot of the program has a satisfying row, in
the row environment `rowEnv data`. Both builders are computable, since they read the image and
the program as functions, never through `MemoryImage.read`. The verifier is complete for every
program and public input, and `verifier_push_eval` and `verifier_pull_eval` read its two
states as `Registers.initial` and `Registers.final prog`.

## Wrong readings excluded

* The seed count is the literal `1 = g^0` and the finalize count a column: a block whose seed
  carried the finalize count, or whose finalize pulled `1`, would let a read go unbalanced;
  `main` transcribes `Const(one)` on the push and `Col(MFCNT)`/`Col(BFCNT)` on the pull.
* The verifier pulls `fp = 1` as a literal (§6.1, the final frame pointer is `g^0`), never a
  public coordinate: a run ending with `fp ≠ 1` cannot balance the state pair.
* The counter it pulls is the program's constant, never a public coordinate or a column: the
  Rust derives `final_pc` and neither reads nor checks one. A verifier reading the counter off
  the public input accepts a witness whose sentinel is not the program's unless a further
  conjunct ties the two, and says nothing per component; `verifier_pull_eval` says the pulled
  state is `Registers.final prog` in every environment.
* Nothing in `main` ties row `i` to `g^i` or a slot to the program: the components' fixed columns
  do (`memComponent`, `bytecodeComponent`), and the statement reads them as theorems
  (`IndexColumnsAreRowIndices`, `SeedRowsAreTheImage`, `BytecodeRowsAreTheProgram`).
* The bytecode circuit's `Spec` names no program: one read off the prover data is the prover's.
  The component carries the program in its fixed columns, and a row whose entry is not the
  program's at its counter breaks `Table.fixed_rows_match`, never the circuit (the tests reject it
  through `BytecodeBindings`).
* The bytecode entry carries all twelve operand slots, spare slots as literal zeros, so that the
  seed of a slot and a table's read of it are the same tuple; `decode` rejects a nonzero spare
  slot, and so do `BytecodeDecodes` and `BytecodeBindings` (tests).
* The public words are not on the bus: §8.2 checks them against the committed memory by an
  evaluation claim, which the statement makes a conjunct of `SatisfiedBy` over `imageOf w.data`,
  and the verifier reads `lanes` for nothing.
-/

namespace LeanVM.Arithmetization

open LeanVM.Parameters LeanVM.Semantics

/-! ## The public input of the constraint system -/

/-- What the verifier circuit reads off the public data: the four lanes of the public input
(specification §2, §8.2). The sentinel counter is not here: it is a constant of the public
program (`leanIsaVerifier`). -/
structure PublicIO (F : Type) where
  /-- `input₀, …, input₃`. -/
  lanes : Vector F 4
  deriving ProvableStruct

/-- The public input of a run on `input`: its four lanes. -/
def PublicIO.ofInput (input : PublicInput) : PublicIO K :=
  ⟨#v[input.lanes 0, input.lanes 1, input.lanes 2, input.lanes 3]⟩

/-! ## The memory block -/

/-- A row of the memory block: the word's two limbs (`MEM_LO, MEM_HI`;
`layout.rs`), the address `g^i` (the index column of §6.5, a fixed column), and the finalize
count `g^(A[i])` (`MFCNT`). The limbs come first, as the committed columns do, so that the prover
data Clean derives from the block, its rows cut at two cells (`memRows`), is the image. -/
structure MemRow (F : Type) where
  /-- The word at the address, as limbs. -/
  m : Vector F 2
  /-- The address, `g^i` for row `i`. -/
  idx : F
  /-- The finalize count, `g^(A[i])` for an address read `A[i]` times. -/
  cntFin : F
  deriving ProvableStruct

/-- The row's binding to an image: the cell at its address holds its word. -/
structure MemBindings {κ : ℕ} (mem : MemoryImage κ) (r : MemRow K) : Prop where
  /-- The cell `idx` holds the row's word `m`. -/
  word_eq : mem.read r.idx = some (E.ofLimbs r.m[0] r.m[1])

/-- The memory block's `Spec`: the row is bound to the image the prover data names
(`imageOf`). -/
def MemSpec (r : MemRow K) (data : ProverData K) : Prop :=
  MemBindings (imageOf data).2 r

/-- The memory block (specification §6.2, seed and finalize; `layout.rs`): push
`(idx, 1, m)`, pull `(idx, cntFin, m)`. -/
def memTable : GeneralFormalCircuit K MemRow unit where
  -- Clean keys the prover data by component name: the block's rows are the `"mem"` table.
  name := memDataName
  main r := do
    MemPush.push ⟨r.idx, 1, r.m⟩
    MemPull.pull ⟨r.idx, r.cntFin, r.m⟩
  -- The push channel: its requirement is vacuous, the obligation is `Spec`.
  channelsWithRequirements := [MemPush.toRaw]
  requirementsChannelsLawful input offset := by
    -- Without core's `BitVec.reduceNeg` simproc, which misreads `-1 : K`.
    simp only [circuit_norm, -BitVec.reduceNeg]
    tauto
  Spec r _ data := MemSpec r data
  -- The honest prover's row: a word of the image. Proved of the row of every word by
  -- `memRowOf_bindings`; see `mem_word_complete`.
  ProverAssumptions r data _ := MemSpec r data
  soundness := by
    circuit_proof_start [MemPull, MemPush]
    obtain ⟨hm, _, _⟩ := h_input
    subst hm
    exact ⟨by simpa only [Vector.getElem_map] using h_holds⟩
  completeness := by
    circuit_proof_start [MemPull, MemPush]
    obtain ⟨hm, _, _⟩ := h_input
    subst hm
    simpa only [Vector.getElem_map] using h_assumptions.word_eq

/-- The seed row of word `i` of the image `mem`, with finalize count `cntFin`: the address `g^i`
and the word's limbs. -/
def memRowOf {κ : ℕ} (mem : MemoryImage κ) (i : Fin (2 ^ κ)) (cntFin : K) : MemRow K :=
  ⟨#v[(mem i).limb 0, (mem i).limb 1], addressOfIndex i, cntFin⟩

/-- On an image within the address space `gLog?_spec` covers, `memRowOf` is bound, with any
finalize count. -/
theorem memRowOf_bindings {κ : ℕ} (hκ : κ < 64) (mem : MemoryImage κ) (i : Fin (2 ^ κ))
    (cntFin : K) : MemBindings mem (memRowOf mem i cntFin) :=
  ⟨by
    show mem.read (addressOfIndex i) = some (E.ofLimbs ((mem i).limb 0) ((mem i).limb 1))
    rw [MemoryImage.read_gpow hκ, ofLimbs_limb]⟩

/-- Every word of the image named by the data has a satisfying seed row, from the image alone:
the constraints of `main` hold of `memRowOf` in the row environment over the data. -/
theorem mem_word_complete {data : ProverData K} (i : Fin (2 ^ (imageOf data).1)) (cntFin : K) :
    ConstraintsHold.Completeness (rowEnv data)
      ((memTable.main (const (memRowOf (imageOf data).2 i cntFin))).operations 0) :=
  (memTable.completeness 0 (rowEnv data) (const _)
    -- No witness slot: the row environment uses the local witnesses vacuously.
    (by simp only [circuit_norm, memTable, -BitVec.reduceNeg]) _
    ProvableType.eval_const_prover
    (memRowOf_bindings (lt_of_le_of_lt (Nat.min_le_right _ _) (by decide)) _ _ _)).1

/-! ## The bytecode block -/

/-- A row of the bytecode block: the counter `g^i` (the index column), the finalize count
`g^(A[i])` (`BFCNT`), and the `entry` at that slot, the opcode and the twelve operand slots (the
thirteen public columns of `bytecode_columns`, `cpu/layout.rs` at leanVM main
`40f877dc`). -/
structure BytecodeRow (F : Type) where
  /-- The counter, `g^i` for row `i`. -/
  idx : F
  /-- The finalize count, `g^(A[i])` for a slot executed `A[i]` times. -/
  cntFin : F
  /-- The opcode, coordinate 3 of the tuple. -/
  opcode : F
  /-- The twelve operand slots. -/
  op : Vector F 12
  deriving ProvableStruct

/-- The row's entry decodes to an instruction (`decode_eq_some_iff` reads it as the entry):
the bytecode pull's guarantee, and the block's `Spec`. -/
structure BytecodeDecodes (r : BytecodeRow K) : Prop where
  /-- The row's entry is an instruction's. -/
  entry_eq : ∃ ins, decode (#v[r.opcode] ++ r.op) = some ins

/-- The row's binding to a program: the program fetches an instruction at the row's counter,
and the row's entry decodes to it. The per-row reading of `BytecodeRowsAreTheProgram prog`,
the statement's conjunct that the block's rows are the program's, and never the block's `Spec`
(the module docstring): `Soundness` derives it for every seed row from the conjunct, and
`bytecodeRowOf_bindings` proves it of every row the builder writes. -/
structure BytecodeBindings (prog : LeanIsaProgram) (r : BytecodeRow K) : Prop where
  /-- The program fetches at `idx` the instruction the row's entry decodes to. -/
  entry_eq : ∃ ins, prog.fetch r.idx = some ins ∧ decode (#v[r.opcode] ++ r.op) = some ins

/-- The bytecode block (specification §6.2 and §6.4, seed and finalize; `layout.rs`):
push `(idx, 1, opcode, op)`, pull `(idx, cntFin, opcode, op)`. Program-free: the entry columns
are the program's by the statement's conjunct, not by anything here. -/
def bytecodeTable : GeneralFormalCircuit K BytecodeRow unit where
  name := "bytecode"
  main r := do
    BytecodePush.push ⟨r.idx, 1, r.opcode, r.op⟩
    BytecodePull.pull ⟨r.idx, r.cntFin, r.opcode, r.op⟩
  -- The push channel: its requirement is vacuous, the obligation is `Spec`.
  channelsWithRequirements := [BytecodePush.toRaw]
  requirementsChannelsLawful input offset := by
    simp only [circuit_norm, -BitVec.reduceNeg]
    tauto
  Spec r _ _ := BytecodeDecodes r
  -- The honest prover's row: a slot of the program, whose entry decodes. Proved of the row of
  -- every slot by `bytecodeRowOf_decodes`; see `bytecode_entry_complete`.
  ProverAssumptions r _ _ := BytecodeDecodes r
  soundness := by
    circuit_proof_start [BytecodePull, BytecodePush]
    obtain ⟨_, _, _, hop⟩ := h_input
    subst hop
    exact ⟨h_holds⟩
  completeness := by
    circuit_proof_start [BytecodePull, BytecodePush]
    obtain ⟨_, _, _, hop⟩ := h_input
    subst hop
    exact h_assumptions.entry_eq

/-! ## Proof helpers -/

/-- A thirteen-coordinate entry is its opcode followed by its twelve operand slots. -/
private theorem cons_append_ops (e : Vector K 13) :
    #v[e[0]] ++ #v[e[1], e[2], e[3], e[4], e[5], e[6], e[7], e[8], e[9], e[10], e[11], e[12]] =
      e := by
  obtain ⟨⟨l⟩, hl⟩ := e
  match l, hl with
  | [_, _, _, _, _, _, _, _, _, _, _, _, _], _ => rfl

/-- The seed row of slot `i` of the program `prog`, with finalize count `cntFin`: the counter
`g^i` and the slot's `entry` as the opcode and the twelve operand slots. -/
def bytecodeRowOf (prog : LeanIsaProgram) (i : Fin (2 ^ prog.logSize)) (cntFin : K) :
    BytecodeRow K :=
  let e := busEntry (prog.instructions i)
  ⟨addressOfIndex i, cntFin, e[0],
    #v[e[1], e[2], e[3], e[4], e[5], e[6], e[7], e[8], e[9], e[10], e[11], e[12]]⟩

/-- `bytecodeRowOf` is bound to its program, with any finalize count. -/
theorem bytecodeRowOf_bindings (prog : LeanIsaProgram) (i : Fin (2 ^ prog.logSize)) (cntFin : K) :
    BytecodeBindings prog (bytecodeRowOf prog i cntFin) :=
  ⟨_, prog.fetch_gpow i, by
    show decode (#v[(busEntry (prog.instructions i))[0]] ++ #v[(busEntry (prog.instructions i))[1],
      (busEntry (prog.instructions i))[2], (busEntry (prog.instructions i))[3], (busEntry
          (prog.instructions i))[4],
      (busEntry (prog.instructions i))[5], (busEntry (prog.instructions i))[6], (busEntry
          (prog.instructions i))[7],
      (busEntry (prog.instructions i))[8], (busEntry (prog.instructions i))[9], (busEntry
          (prog.instructions i))[10], (busEntry (prog.instructions i))[11],
      (busEntry (prog.instructions i))[12]]) = some _
    rw [cons_append_ops]
    exact decode_entry _⟩

/-- `bytecodeRowOf` decodes, with any finalize count: the block's `Spec` of every row the
builder writes. -/
theorem bytecodeRowOf_decodes (prog : LeanIsaProgram) (i : Fin (2 ^ prog.logSize)) (cntFin : K) :
    BytecodeDecodes (bytecodeRowOf prog i cntFin) :=
  ⟨(bytecodeRowOf_bindings prog i cntFin).entry_eq.imp fun _ h ↦ h.2⟩

/-- Every slot of a program has a satisfying seed row, from the program alone and over any
data: the constraints of `main` hold of `bytecodeRowOf` in the row environment. -/
theorem bytecode_entry_complete {data : ProverData K} (prog : LeanIsaProgram)
    (i : Fin (2 ^ prog.logSize)) (cntFin : K) :
    ConstraintsHold.Completeness (rowEnv data)
      ((bytecodeTable.main (const (bytecodeRowOf prog i cntFin))).operations 0) :=
  (bytecodeTable.completeness 0 (rowEnv data) (const _)
    (by simp only [circuit_norm, bytecodeTable, -BitVec.reduceNeg]) _
    ProvableType.eval_const_prover (bytecodeRowOf_decodes _ _ _)).1

/-! ## The fixed columns

The two blocks are preallocated: one row per word of the image and one per slot of the program,
in order, so their index columns, and the bytecode block's entry columns, are *fixed columns*,
which the verifier computes and the prover does not choose (Clean's `PreallocatedMode`; leanVM's
index column of §6.5 and its `Coord::Public` entry columns). A fixed cell is a witness-IR
expression of the row index; `fixedColumn n f` is `f j` at row `j < n`. Clean's witness generator
is not run on this ensemble (the prover is leanVM's, and in Lean `Arithmetization.Completeness`):
the committed cells' expressions are placeholders (`committedCell`), and no demand is routed to a
block (`rowOf` is past the height), so only the fixed cells carry meaning, through
`Component.FixedRowsMatch`. -/

/-- The fixed column with `f j` at row `j < n`, `0` past them. -/
def fixedColumn (n : ℕ) (f : Fin n → K) : Witgen.FExpr K :=
  .listGet (List.ofFn fun j ↦ .const (f j)) .idx

/-- A committed cell of a preallocated row: a value the prover chooses. -/
def committedCell : Air.Flat.WitnessGeneration.Cell K := .witness (.const 0)

theorem evalList_eq (ctx : Witgen.Ctx K) (xs : List (Witgen.FExpr K)) (k : ℕ) :
    Witgen.FExpr.evalList ctx k xs = ((xs[k]?).map (Witgen.FExpr.eval ctx)).getD 0 := by
  induction xs generalizing k with
  | nil => cases k <;> rfl
  | cons x xs ih =>
    cases k with
    | zero => rfl
    | succ k => exact ih k

/-- A fixed column at a row within it is the column's entry there. -/
theorem fixedColumn_eval {n : ℕ} (f : Fin n → K) (env : ProverEnvironment K)
    (locals : Array (K ⊕ UInt64)) {k : ℕ} (h64 : k < 2 ^ 64) (hn : k < n) :
    (fixedColumn n f).eval ⟨env, locals, k⟩ = f ⟨k, hn⟩ := by
  simp only [fixedColumn, Witgen.FExpr.eval, Witgen.U64Expr.eval, evalList_eq,
    UInt64.toNat_ofNat_of_lt' h64, List.length_ofFn, Option.map_some, Option.getD_some, hn,
    List.getElem?_eq_getElem, List.getElem_ofFn]

/-! ## The blocks as components -/

/-- The memory block's generation: `2^κ` rows, the index column `g^i` fixed, the word and its
finalize count committed. -/
def memMode (κ : ℕ) : Air.Flat.WitnessGeneration.PreallocatedMode K MemRow where
  channel := MemPull
  trigger := .pull
  height := UInt64.ofNat (2 ^ κ)
  input _ := pure ⟨#v[committedCell, committedCell],
    .fixed (fixedColumn (2 ^ κ) fun j ↦ addressOfIndex j), committedCell⟩
  rowOf _ := .const (UInt64.ofNat (2 ^ κ))

/-- The memory block of a memory of `2^κ` words (`κ` the announced `log_mem`): `memTable`, its
index column fixed. -/
def memComponent (κ : ℕ) : Air.Flat.Component K where
  circuit := memTable
  generation := .preallocated (memMode κ)

/-- The bytecode block's generation: `2^N` rows for a program of `2^N` slots, the counter `g^i`
and the entry of slot `i` fixed, the finalize count committed. -/
def bytecodeMode (prog : LeanIsaProgram) : Air.Flat.WitnessGeneration.PreallocatedMode K BytecodeRow where
  channel := BytecodePull
  trigger := .pull
  height := UInt64.ofNat (2 ^ prog.logSize)
  input _ := pure ⟨.fixed (fixedColumn (2 ^ prog.logSize) fun j ↦ addressOfIndex j), committedCell,
    .fixed (fixedColumn (2 ^ prog.logSize) fun j ↦ (busEntry (prog.instructions j))[0]),
    Vector.ofFn fun k : Fin 12 ↦
      .fixed (fixedColumn (2 ^ prog.logSize) fun j ↦ (busEntry (prog.instructions j))[k.val + 1])⟩
  rowOf _ := .const (UInt64.ofNat (2 ^ prog.logSize))

/-- The bytecode block of the public program `prog`: `bytecodeTable`, its counter and entry
columns fixed to the program's. -/
def bytecodeComponent (prog : LeanIsaProgram) : Air.Flat.Component K where
  circuit := bytecodeTable
  generation := .preallocated (bytecodeMode prog)

/-- A row of the memory block agrees with the fixed cells of row `i` exactly when its address is
`g^i`: the index column, which the verifier computes (§6.5). -/
theorem memMode_fixedAt {κ : ℕ} {i : UInt64} (hi : i.toNat < 2 ^ κ) (r : MemRow K) :
    (memMode κ).FixedAt i r ↔ r.idx = addressOfIndex i.toNat := by
  obtain ⟨⟨⟨l⟩, hl⟩, idx, c⟩ := r
  match l, hl with
  | [a, b], _ =>
  simp only [Air.Flat.WitnessGeneration.PreallocatedMode.FixedAt, memMode, Witgen.M.pure_def]
  simp [circuit_norm, explicit_provable_type, ProvableStruct.toComponents, committedCell,
    Air.Flat.WitnessGeneration.Cell.FixedMatches]
  rw [fixedColumn_eval _ _ _ (show i.toNat < 2 ^ 64 from i.toNat_lt) hi]

/-- A row of the bytecode block agrees with the fixed cells of row `i` exactly when it is the
program's row of slot `i` (`bytecodeRowOf`), with its own finalize count: the counter and the entry
are the verifier's (§8.6, Bus 4; `Coord::Public`). -/
theorem bytecodeMode_fixedAt (prog : LeanIsaProgram) {i : UInt64} (hi : i.toNat < 2 ^ prog.logSize)
    (r : BytecodeRow K) :
    (bytecodeMode prog).FixedAt i r ↔ r = bytecodeRowOf prog ⟨i.toNat, hi⟩ r.cntFin := by
  obtain ⟨idx, c, opc, ⟨⟨l⟩, hl⟩⟩ := r
  match l, hl with
  | [o1, o2, o3, o4, o5, o6, o7, o8, o9, o10, o11, o12], _ =>
  simp only [Air.Flat.WitnessGeneration.PreallocatedMode.FixedAt, bytecodeMode, Witgen.M.pure_def]
  simp [circuit_norm, explicit_provable_type, ProvableStruct.toComponents, committedCell,
    Air.Flat.WitnessGeneration.Cell.FixedMatches, Vector.ofFn, List.ofFn_succ,
    fixedColumn_eval _ _ _ (show i.toNat < 2 ^ 64 from i.toNat_lt) hi, bytecodeRowOf]

/-! ## The verifier -/

/-- The verifier's state boundary for the public program `prog` (specification §6.1;
`layout.rs`): push the initial state `(1, 1)`, pull the final state
`(g^(N_prog - 1), 1)`, the counter a constant of the program as `Const(g_pow(final_pc))` is
(`layout.rs`). `Spec` is `True`: the state pull carries no guarantee, and the
run the boundary closes is `exists_run_of_balanced`. -/
def leanIsaVerifier (prog : LeanIsaProgram) : Verifier.Program K PublicIO where
  main _ := do
    Verifier.push StatePush ⟨1, 1⟩
    Verifier.pull StatePull ⟨Expression.const prog.pcFinal, 1⟩
  Spec _ _ := True
  soundness _ _ := trivial

/-! ## Load-bearing lemmas -/

/-- The state the verifier pushes is `Registers.initial`, in every environment. -/
theorem verifier_push_eval (env : Environment K) :
    eval env (⟨1, 1⟩ : Registers (Expression K)) = Registers.initial := by
  simp only [circuit_norm]; rfl

/-- The state the verifier pulls is `Registers.final prog`, in every environment: the
counter is a constant of the component, not a column or a public coordinate. -/
theorem verifier_pull_eval (prog : LeanIsaProgram) (env : Environment K) :
    eval env (⟨Expression.const prog.pcFinal, 1⟩ : Registers (Expression K)) = Registers.final prog := by
  simp only [circuit_norm]; rfl

end LeanVM.Arithmetization
