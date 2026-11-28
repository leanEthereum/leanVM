/-
  LeanVM.Protocol.Relation.Link.Rel

  The link's part of the relation on a committed stack: what `verify_link` checks of the tables'
  rows, stated on the stack's columns.
-/

module

public import LeanVM.Protocol.Relation.Stack
public import LeanVM.Protocol.Hotwire.StateLink
public import LeanVM.Protocol.Hotwire.Lookup
public import LeanVM.Protocol.Link.Skeleton

/-!
# The link's relation

`verify_link` (`Statement/Verifier/Link.lean`, `crates/verifier/src/link.rs`) checks, at the
chunks `Chunks.new` gives the pointer width (`linkChunks`), what each instruction table's rows say
through their `Links` (`Statement/Verifier/Layout.lean`). Here it is stated on a stack's columns
(`columnValue`, `Stack.lean`; table `t`'s local column `c` is the global column
`GLOBAL_COLUMN_BASES[t] + c`), row by row, for the rows a table executes, `u < table_rows[t]`
(`omega_at`'s and `less_than`'s `n`):

* **one-hot pointers** (`PointersOneHot`): every pointer column's word (`Links.pointers`) holds, in
  each chunk's block of `2^{w_i}` bits from bit `word_shifts[i]`, exactly one set bit; it decodes to
  the index `ptrIndex` (chunk `i`'s position at bit `index_shifts[i]`), the mirror test's notion
  (`Hotwire/Mirror.lean`, `Window.lean`'s `OneHot` over the bits in `E`);
* **the state link** (`StateHolds`): `Hotwire/StateLink.lean`'s identity (I) over the executed rows,
  each at its decoded cycle pointer, its state `(pc, fp)` and successor `next`, from `(1, 1)` to
  `(g^(2^log_bytecode − 1), 1)` after the cycle count `T = Σ table_rows`;
* **the memory lookup** (`MemoryHolds`): each access of an executed row whose gate is nonzero names,
  through its pointer and shift inside the pointer's window (`windowHit`), a cell below
  `2^log_memory` whose address `g^j` is the access's address and whose word is the access's word,
  its reads at their values (`readValue`: a word where a pointer points, a slot of the row's
  instruction, times `fp` or `pc`);
* **the program lookup** (`ProgramHolds`): each executed row's program pointer names an instruction
  below `2^log_bytecode` at the row's `pc`, of the table's opcode, whose operand slots meet the
  row's operand equations;
* **the constraints** (`ConstraintsHold`): every row of a table with constraints (`JUMP`'s
  fourteen-column identities, `jumpConstraints`) on its `2^h` rows, as the row side weighs them by
  `eq(τ, ·)` over the whole table.

`LinkRel` is their conjunction at the link's chunks. It is what `verify_link` enforces, with the
Keccak lanes' meaning (`KeccakRel`) and the public input (`PubRel`) beside it, and what the
execution's validity needs (`Link/Valid.lean`). The program's slots are read here unmasked, as the
instruction's words (`bcWord`); the link's program side masks them by the opcode, which the program
lookup fixes.
-/

namespace LeanVM.Protocol.Relation

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol.Verifier LeanVM.Protocol.Link

@[expose] public section

/-! ## The tables' rows -/

/-- Table `t` of the layout. -/
def tableAt (layout : Layout) (t : ℕ) : Table := layout.tables.getD t default

/-- Table `t`'s local column `c` at row `u`, in `E` (`columnValue`: a `KECCAK` output lane is the
permutation's output). -/
def tableValue (layout : Layout) {μ : ℕ} (q : Column μ) (t c u : ℕ) : E :=
  columnValue layout q (globalColumnBases.getD t 0 + c) u

/-- Table `t`'s local column `c` at row `u`, the committed word. -/
def tableWord (layout : Layout) {μ : ℕ} (q : Column μ) (t c u : ℕ) : K :=
  columnRow layout q (globalColumnBases.getD t 0 + c) u

/-- Row `u` of table `t`: its columns' values, in order (the verifier's `values`). -/
def rowValues (layout : Layout) {μ : ℕ} (q : Column μ) (t u : ℕ) : List E :=
  (List.range (tableAt layout t).width).map fun c ↦ tableValue layout q t c u

/-- The rows table `t` executes, `table_rows[t]`. -/
def tableRowCount (layout : Layout) (t : ℕ) : ℕ := layout.tableRows.getD t 0

/-- The chunks `verify_link` reads the pointers at, if the width is one it accepts. -/
def linkChunks (layout : Layout) : Option Chunks := Chunks.new (linkWidth layout)

/-! ## Pointers -/

/-- Chunk `i`'s table of a pointer word: its bit `word_shifts[i] + v`, in `E`. -/
def chunkTable (chunks : Chunks) (w : K) (i : ℕ) : ℕ → E :=
  fun v ↦ bitOf w (chunks.wordShifts.getD i 0 + v)

/-- Chunk `i` of the word `w` is one-hot over its `2^{w_i}` values. -/
def ChunkOneHot (chunks : Chunks) (w : K) (i : ℕ) : Prop :=
  ∃ σ < 2 ^ chunks.widths.getD i 0, Hotwire.OneHot (chunks.widths.getD i 0) (chunkTable chunks w i) σ

/-- The position of chunk `i`'s first set bit (`0` for none). -/
def chunkPos (chunks : Chunks) (w : K) (i : ℕ) : ℕ :=
  ((List.range (2 ^ chunks.widths.getD i 0)).find? fun v ↦
    w.toBitVec.getLsbD (chunks.wordShifts.getD i 0 + v)).getD 0

/-- The index a pointer word decodes to: chunk `i`'s position at bit `index_shifts[i]`. -/
def ptrIndex (chunks : Chunks) (w : K) : ℕ :=
  ((List.range chunks.d).map fun i ↦ chunkPos chunks w i * 2 ^ chunks.indexShifts.getD i 0).sum

/-- The decoded index of table `t`'s pointer column `p` at row `u`. -/
def rowPtr (layout : Layout) {μ : ℕ} (q : Column μ) (chunks : Chunks) (t p u : ℕ) : ℕ :=
  ptrIndex chunks (tableWord layout q t p u)

/-- **Every executed row's pointers are one-hot** in every chunk. -/
def PointersOneHot (layout : Layout) {μ : ℕ} (q : Column μ) (chunks : Chunks) : Prop :=
  ∀ t < nTables, ∀ u < tableRowCount layout t, ∀ p ∈ (tableAt layout t).links.pointers,
    ∀ i < chunks.d, ChunkOneHot chunks (tableWord layout q t p u) i

/-! ## The state link -/

/-- The executed rows of all tables. -/
abbrev LinkRow (layout : Layout) : Type := Σ t : Fin nTables, Fin (tableRowCount layout t)

/-- A row's cycle pointer, decoded, in `Fin (2^W)`. -/
def rowCycle (layout : Layout) {μ : ℕ} (q : Column μ) (chunks : Chunks) (x : LinkRow layout) :
    Fin (2 ^ chunks.width) :=
  ⟨rowPtr layout q chunks x.1 (tableAt layout x.1).links.stateLink.cycle x.2 % 2 ^ chunks.width,
    Nat.mod_lt _ (Nat.two_pow_pos _)⟩

/-- A row's state `(pc, fp)`. -/
def rowState (layout : Layout) {μ : ℕ} (q : Column μ) (x : LinkRow layout) : Fin 2 → E :=
  let state := (tableAt layout x.1).links.stateLink
  ![tableValue layout q x.1 state.pc x.2, tableValue layout q x.1 state.fp x.2]

/-- A row's successor state, its `next` forms on its values. -/
def rowNext (layout : Layout) {μ : ℕ} (q : Column μ) (x : LinkRow layout) : Fin 2 → E :=
  let state := (tableAt layout x.1).links.stateLink
  let col := fun c ↦ tableValue layout q x.1 c x.2
  ![state.next.1.evaluate col, state.next.2.evaluate col]

/-- The initial state `(1, 1)`. -/
def linkInit : Fin 2 → E := ![1, 1]

/-- The final state `(g^(2^log_bytecode − 1), 1)`. -/
def linkFinal (layout : Layout) : Fin 2 → E := ![gpow (2 ^ layout.logBytecode - 1), 1]

/-- **The state link**: identity (I) of `StateLink.lean` over the executed rows. -/
def StateHolds (layout : Layout) {μ : ℕ} (q : Column μ) (chunks : Chunks) : Prop :=
  Hotwire.LinkHolds (linkCycles layout) (rowCycle layout q chunks) (rowState layout q)
    (rowNext layout q) linkInit (linkFinal layout)

/-! ## The memory and the program -/

/-- Slot `s` of instruction `k` of the stacked program: word `s·2^log_bytecode + k`. -/
def bcWord (layout : Layout) (s k : ℕ) : E :=
  ofK (layout.bytecode.getD (s * 2 ^ layout.logBytecode + k) 0)

/-- The memory word at `j`: its two limbs (`memoryImage`). -/
def memWord (layout : Layout) {μ : ℕ} (q : Column μ) (j : ℕ) : E :=
  E.ofLimbs (columnRow layout q memory0 j) (columnRow layout q memory1 j)

/-- A read's value in row `u` of table `t`, whose program pointer names `k`: a word where a pointer
points, or a slot of the instruction, times `fp` or `pc = g^k`. -/
def readValue (layout : Layout) {μ : ℕ} (q : Column μ) (chunks : Chunks) (t u k : ℕ) :
    Read → E
  | .word p scale => scale.evaluate (fun c ↦ tableValue layout q t c u) *
      memWord layout q (rowPtr layout q chunks t p u)
  | .slot s scale => scale * bcWord layout s k
  | .frame s scale =>
      scale * tableValue layout q t (tableAt layout t).links.stateLink.fp u * bcWord layout s k
  | .pc s scale => scale * gpow k * bcWord layout s k

/-- An access's address in row `u` of table `t`: its committed part, and `g^e·fp·BC_slot` for a
framed access. -/
def accessAddress (layout : Layout) {μ : ℕ} (q : Column μ) (t u k : ℕ) (a : Access) : E :=
  a.address.evaluate (fun c ↦ tableValue layout q t c u) +
    match a.frame with
    | some (s, e) => gpow e * tableValue layout q t (tableAt layout t).links.stateLink.fp u *
        bcWord layout s k
    | none => 0

/-- An access's word in row `u` of table `t`: its committed part plus its reads. -/
def accessWord (layout : Layout) {μ : ℕ} (q : Column μ) (chunks : Chunks) (t u k : ℕ)
    (a : Access) : E :=
  a.value.evaluate (fun c ↦ tableValue layout q t c u) +
    (a.reads.map (readValue layout q chunks t u k)).sum

/-- An access's gate in row `u` of table `t`: its gating column, `1` for none. -/
def accessGate (layout : Layout) {μ : ℕ} (q : Column μ) (t u : ℕ) (a : Access) : E :=
  (a.gate.map fun c ↦ tableValue layout q t c u).getD 1

/-- Row `u` of table `t`'s program pointer, decoded. -/
def rowBc (layout : Layout) {μ : ℕ} (q : Column μ) (chunks : Chunks) (t u : ℕ) : ℕ :=
  rowPtr layout q chunks t (tableAt layout t).links.bytecodeLink.pointer u

/-- **The memory lookup**: every access of an executed row whose gate is nonzero names, inside its
pointer's window, a cell below `2^log_memory` at its address holding its word. -/
def MemoryHolds (layout : Layout) {μ : ℕ} (q : Column μ) (chunks : Chunks) : Prop :=
  ∀ t < nTables, ∀ u < tableRowCount layout t, ∀ a ∈ (tableAt layout t).links.memory,
    accessGate layout q t u a ≠ 0 →
      ∃ j, Hotwire.windowHit (chunks.widths.getD 0 0) (rowPtr layout q chunks t a.pointer u)
          a.shift = some j ∧ j < 2 ^ layout.logMemory ∧
        gpow j = accessAddress layout q t u (rowBc layout q chunks t u) a ∧
        memWord layout q j = accessWord layout q chunks t u (rowBc layout q chunks t u) a

/-- **The program lookup**: every executed row's program pointer names an instruction below
`2^log_bytecode`, at the row's `pc`, whose opcode (`opcodeOf` of slot `3`) is the table's, and whose
operand slots sum to the row's operand forms. -/
def ProgramHolds (layout : Layout) {μ : ℕ} (q : Column μ) (chunks : Chunks) : Prop :=
  ∀ t < nTables, ∀ u < tableRowCount layout t,
    let link := (tableAt layout t).links.bytecodeLink
    let k := rowBc layout q chunks t u
    k < 2 ^ layout.logBytecode ∧ tableValue layout q t link.pc u = gpow k ∧
      opcodeOf (layout.bytecode.getD (3 * 2 ^ layout.logBytecode + k) 0) = t ∧ link.opcode = t ∧
      ∀ op ∈ link.operands, (op.1.map fun s ↦ bcWord layout s k).sum =
        op.2.evaluate fun c ↦ tableValue layout q t c u

/-- **The constraints** of every table that has them (`JUMP`'s), on all its `2^h` rows. -/
def ConstraintsHold (layout : Layout) {μ : ℕ} (q : Column μ) : Prop :=
  ∀ t < nTables, ∀ u < 2 ^ layout.tableLogHeights.getD t 0,
    ∀ c ∈ (tableAt layout t).constraints (rowValues layout q t u), c = 0

/-! ## The relation -/

/-- **The link's part of the relation**, at the link's chunks. -/
def LinkRel (layout : Layout) {μ : ℕ} (q : Column μ) : Prop :=
  ∃ chunks, linkChunks layout = some chunks ∧ PointersOneHot layout q chunks ∧
    StateHolds layout q chunks ∧ MemoryHolds layout q chunks ∧ ProgramHolds layout q chunks ∧
    ConstraintsHold layout q

/-! ## The extracted execution -/

/-- The cycles of the executed rows in the final state `(g^(2^log_bytecode − 1), 1)`, decoded as
`rowCycle` decodes them. -/
def finalCycles (layout : Layout) {μ : ℕ} (q : Column μ) (chunks : Chunks) : List ℕ :=
  (List.range nTables).flatMap fun t ↦ (List.range (tableRowCount layout t)).filterMap fun u ↦
    let state := (tableAt layout t).links.stateLink
    if tableWord layout q t state.pc u = g ^ (2 ^ layout.logBytecode - 1) ∧
        tableWord layout q t state.fp u = 1 then
      some (rowPtr layout q chunks t state.cycle u % 2 ^ chunks.width)
    else none

/-- **The cycle the run halts at**: the least cycle of an executed row in the final state, the
cycle count `T` if none is. The state link lets a run pass through the final state and come back
to it at `T` (a last instruction that jumps to itself, say), where leanISA's `run` halts at the
first visit. -/
def firstFinal (layout : Layout) {μ : ℕ} (q : Column μ) : ℕ :=
  match linkChunks layout with
  | some chunks => (finalCycles layout q chunks).foldl min (linkCycles layout)
  | none => linkCycles layout

/-- **The execution a stack gives**: the memory read off it, run until the first cycle in the
final state (`firstFinal`). -/
def candidate (program : LeanIsaProgram) (layout : Layout) {μ : ℕ} (q : Column μ) :
    Execution program :=
  ⟨layout.logMemory, memoryImage layout q, firstFinal layout q⟩

end

end LeanVM.Protocol.Relation
