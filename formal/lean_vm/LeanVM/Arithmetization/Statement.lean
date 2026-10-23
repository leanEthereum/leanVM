/-
  LeanVM.Arithmetization.Statement

  The constraint statement of leanISA: the ensemble of the six opcode tables, the two seed
  blocks and the verifier; bus balance as a multiset equality; the checks the verifier makes
  on the announced instance; the three hypotheses Clean cannot yet express; the relation
  `SatisfiedBy` that `constraintSoundness` and `constraintCompleteness` connect to
  `ValidExecution`; and what it means for a
  witness to represent a trace.
-/

module

public import LeanVM.Arithmetization.Boundary
public import LeanVM.Arithmetization.Tables.Xor
public import LeanVM.Arithmetization.Tables.MulNative
public import LeanVM.Arithmetization.Tables.SetConstant
public import LeanVM.Arithmetization.Tables.Deref
public import LeanVM.Arithmetization.Tables.Jump
public import LeanVM.Arithmetization.Tables.Blake2s
public import Clean.Air.FlatEnsemble

@[expose] public section

/-!
# The constraint statement

At leanVM pin `127510d14c98ade4e8a97646c44fa7f1ff5e752d` and Clean pin `42fe4b26`. The
statement itself is written from the specification, as what the M3 model means by an
accepted instance (specification §5, `doc/leanvm/body/05-arithmetization.tex:4`: "an instance
is accepted exactly when every table's constraints hold and the bus balances", the balance
being the multiset equality of `:14`), and what the verifier checks of an announced instance
is transcribed: the caps (`crates/verifier/src/lib.rs:208-222` and
`crates/verifier/src/layout.rs:381-395`, the
announcement checks of `walk` and `build_layout`, which replace `read_public` of `a386121f`;
§6.2 "Instance caps", `06-bus-interactions.tex:80`), the nonzero count product (§6.2 "The count
product", `:78`; `cpu/layout.rs:73`, the count channel of the six tables' read-count columns,
`:396-412`), the public words against the committed memory (§8.2,
`08-end-to-end-protocol.tex:27-37`), the public parts of the bus the verifier forms itself, the
index column and the program's share of the bytecode blocks (§8.5, `:74`; §6.5,
`06-bus-interactions.tex:98`), and the BLAKE2s validity Flock proves (§8.5 "BLAKE2s validity";
`crates/verifier/src/lib.rs:266-289`). This file is the accept relation of the M3 constraint
system and its ensemble, a statement with no soundness or completeness theorem: it is what
`constraintSoundness` and `constraintCompleteness` are about.

**The ensemble.** `leanIsaEnsemble prog` is Clean's `Ensemble`: the six opcode tables and the two
seed blocks of `Boundary` as its components, program-free as leanVM's AIRs are, the six
channels of `Channels`, and the verifier `leanIsaVerifier prog`, the one program-bearing
component, as leanVM's `layout(prog, log_mem, taus, pi)` is a function of the program through
its state boundary alone. A witness `w : EnsembleWitness (leanIsaEnsemble prog)`
is Clean's: one `Air.Flat.Table` of raw rows per component, the prover data, and the public
input, with the constraints `w.Constraints` ("every component's constraints hold on every
row") Clean's own, consumed unchanged.

**Reading a witness.** Tables are read by position in the ensemble's `tables` (`tableAt`),
and channels by name (`messagesOn`, `rowMessagesOn`): Clean's `RawChannel` carries
propositions and has no decidable equality, and the six channels are told apart by name as
`channelDir` and `channelSep` already read them. A raw row is read as its typed row
exactly as the component's constraints read it (`memRowAt`, `blake2sRowAt`: Clean's
`Component.rowInput`, the first `size Row` cells of the row, a missing cell `0`).

**Balance.** `BalancedPair w pull push` says the messages pushed on `push` and the messages
pulled on `pull` form the same multiset (§5.1 "Balance", `05-arithmetization.tex:14`): a
`List.Perm`, counted in `ℕ`. It is never Clean's `BalancedInteractions`, a sum in the field:
`ringChar K = 2` lets that sum accept at most one interaction, and a message pushed twice and
never pulled has field-sum balance `2 = 0`.
Every interaction of the ensemble has multiplicity `1`, so the multiset of messages
is the multiset of interactions. The direction of an interaction is the channel it is on: the
three pairs `(StatePull, StatePush)`, `(MemPull, MemPush)`, `(BytecodePull, BytecodePush)`.

**The verifier's checks.** `CountsNonzero w` is the nonzero count product: every read pull of
the six tables carries a nonzero count, message index `1` (bus coordinate 2) of a memory or
bytecode tuple (§6.2 "The count product"; `layout.rs:73` and `:396-412`, the count channel
stacks the read-count columns of the six tables and nothing else, so the finalize counts of
the two blocks are outside it, as §6.2 "Nothing checks the finalize counts" says). `Caps w` is
the M3 part of the announcement checks (`read_public` at `a386121f`; at the pin, `walk` and
`build_layout`, `verifier/src/lib.rs:208-222` and `verifier/src/layout.rs:381-395`, behind the
wrapper `crates/leanvm_core/src/cpu/mod.rs:685-698`), which make eight checks: (1) the
announced sizes have zero upper limbs (`verifier/src/lib.rs:210-213`, the transcript format)
and (2) the two public words have a zero third limb (`cpu/mod.rs:688-690`), both by type here
(`PublicInput.word0`, `word1`); (3) the bytecode length is a power of two at most `2^32`
(`cpu/mod.rs:688`, `verifier/src/layout.rs:386` and `:393`), `Program`'s by type
(`Program.logSize_le`); (4) the memory log-size is within `[MIN_LOG_MEM, MAX_LOG_MEM] = [16, 32]`
(`verifier/src/layout.rs:388`); (5) every table has at most `2^MAX_LOG_ROWS` rows
(`verifier/src/layout.rs:417` at leanVM `3a37fb6e1c7423e36b67d1cac4eda70c3ad4dd45`; the prover
announces each table's row count, the rows past it in the table's height being padding rows,
which the bus never sees, so the witness's tables are the executed rows only); (6) there is no
`BLAKE2S` floor since that commit; (7) the WHIR rate (`verifier/src/lib.rs:217`) and (8) the
stacked size `mu ∈ [MIN_MU, MAX_MU]` (`verifier/src/lib.rs:219-222`) are parameters of the
commitment, left to the protocol layer, which reads them off the same announcement. `Caps`
transcribes (4) and (5) and adds `WellShapedData w.data`, a representation hypothesis
rather than a check: the shape the announced `log_mem` already implies for an honest prover,
so that `imageOf` drops no row of the prover data. These caps are what keeps the
total read count below `2^64 - 1`, the bound the bus argument of `Soundness` needs (Lemma 6.3).

**The three hypotheses Clean cannot yet express** (removed by Clean PR #446, indexed fixed
columns and proof-committed `ProverData`):
`IndexColumnsAreRowIndices w`, the `idx` column of row `i` of the memory block is `g^i` (§6.5,
the index column the verifier computes; `layout.rs:364` and `:375`, `Index`; the bytecode
block's index column needs no conjunct, since `bytecodeRowOf prog i` writes it);
`SeedRowsAreTheImage w`,
the memory block's rows are the words of the image the prover data names, in order, the index
and finalize columns free (§6.2 "Seed" and "Finalize"; `layout.rs:358-381`, `MEM_LO, MEM_HI,
MEM_TOP` and `MFCNT`); and `BytecodeRowsAreTheProgram prog w`, the bytecode block's rows are
`bytecodeRowOf prog i cntFin` for every slot `i` with some finalize-count column `cntFin`
(§8.5 Bus 4: the verifier forms "the program's whole share of the two bytecode blocks" itself;
`layout.rs:287-289` and `:382-394`, `Coord::Public` and `BFCNT`). Each is faithful: the index
column is verifier-computed, the memory columns are the committed image, the program is
public. Their per-row readings are `memRowOf_bindings` and `BytecodeBindings prog`.

**The BLAKE2s validity.** `Blake2sRowsValid w`, every row of the `BLAKE2S` table satisfies
`Blake2sRelation` (the table's `Assumptions` field), is the one conjunct the verifier
enforces outside the bus: the table has no constraint on its eighteen limbs, and the compression is
proved by Flock on the region the limb columns are routed to (§8.5 "BLAKE2s validity", Opening step
4; `crates/verifier/src/lib.rs:266-289`). Clean's `EnsembleWitness.Constraints` does not include a
table's `Assumptions`, and its `AssumptionsConsistency` sources them from the public input alone, so
the fact is a conjunct of the statement, and `assumptions_of_blake2sRowsValid` turns it into the
`w.Assumptions` that Clean's `TableSoundness` takes. The conjunct stays: the proof system's adaptor
discharges it from the Flock region, whose R1CS forces every block's limbs to compress
(`blake2sRowsValid_witnessOf`).

**The statement.** `SatisfiedBy prog input w` is the relation the proof system proves and
extracts (issue #13), a structure with named fields so that the soundness and completeness
proofs project the conjunct they consume by name. Its `constraints` field is Clean's; only
the `JUMP` table emits an assertion (`tables.rs:729-736`; the other seven components and the
verifier have none), so the field reduces to the `JUMP` residuals on every `JUMP` row.
The `public_input_eq` field is read by no component: the lanes bind the run through
`word0_eq` and `word1_eq`, the two public words at `g^0` and `g^1` of the image the data
names (§8.2, the evaluation claim against the committed memory; spelled as
`HasPublicBoundary` spells it, through `MemImage.read`).

**The trace.** `AssignmentRepresents w t` says what a witness of `SatisfiedBy` is a witness
of: the image the data names is the trace's (`κ_eq`, `image_eq`; `assignmentRepresents_image`
reads the two as one equality of dependent pairs), and each consecutive pair `(r_k, r_{k+1})`
of the trace's register sequence `r_0, …, r_steps` (`Trace.regs`) occurs as the
state pull and the state push of some row of some table (`RowSteps`). Occurrence, not an
injection of steps into rows: a witness with one traversal of a loop represents a trace with
two, and the image determines the run. The remaining rows are the closed walks of §8.3, about
which nothing is claimed. `constraintSoundness` yields a trace the witness
represents, and `constraintCompleteness` a witness representing the trace.

## Bus soundness

The bus-soundness statements, recorded at the end of this file as their original interface,
are proved in `LeanVM.Arithmetization.Soundness` (`mem_channel_sound`,
`bytecode_channel_sound`, `no_row_at_sentinel`, `exists_run_of_balanced`).

## Wrong readings excluded

* Balance is a permutation, not a field sum: `BalancedPair` is `List.Perm`;
  Clean's `Ensemble.Statement` is not consumed.
* A channel is identified by its name, never by the sign of a multiplicity:
  `messagesOn` filters by `RawChannel.name`, and a push on the pull channel of a pair
  would count as a pull (`memRead` and `bytecodeRead` never do that).
* The count product covers the six tables' read counts and nothing else: `CountsNonzero`
  quantifies over `w.tables.take 6`, and a finalize count of `0` is rejected by balance alone
  (§6.2).
* The compression is not a constraint of the table and not a bus fact: `Blake2sRowsValid` is
  a conjunct of its own, discharged by Flock, never by `w.Constraints` (which the `BLAKE2S`
  table satisfies on every row) and never by balance (which binds the limbs to the cells, not
  the cells to the compression).
* The ensemble is a function of the program through the verifier alone; the program is in no
  table of the prover data, and `BytecodeRowsAreTheProgram prog` is the conjunct that pins the
  bytecode block's public columns to it.
* The public words are not on the bus (§8.2): `word0_eq` and `word1_eq` read the image the
  data names, as `HasPublicBoundary` reads the trace's.
* The state pull carries no guarantee: `AssignmentRepresents` claims the
  run's steps are rows, and nothing about the rows that are not.
-/

namespace LeanVM.Arithmetization

open LeanVM.Parameters LeanVM.Semantics
open Air.Flat (Ensemble EnsembleWitness Component)

/-! ## The ensemble -/

/-- The leanISA ensemble of the public program `prog`: the six opcode tables, the memory and
bytecode blocks, the six channels, and the verifier `leanIsaVerifier prog`, its one
program-bearing component (`layout.rs:351-394`). -/
def leanIsaEnsemble (prog : Program) : Ensemble K PublicIO where
  tables := [⟨xorTable⟩, ⟨mulTable⟩, ⟨setTable⟩, ⟨derefTable⟩, ⟨jumpTable⟩, ⟨blake2sTable⟩,
    ⟨memTable⟩, ⟨bytecodeTable⟩]
  channels := [StatePull.toRaw, StatePush.toRaw, MemPull.toRaw, MemPush.toRaw,
    BytecodePull.toRaw, BytecodePush.toRaw]
  verifier := leanIsaVerifier prog
  -- The verifier has no local witness.
  verifier_length_zero _ := by simp only [circuit_norm, leanIsaVerifier]

/-! ## Reading a witness -/

variable {prog : Program}

/-- The witness's table of component `j`, in the order of the ensemble's `tables`: `XOR`,
`MUL_NATIVE`, `SET_CONSTANT`, `DEREF`, `JUMP`, `BLAKE2S`, then the memory block and the
bytecode block. -/
def tableAt (w : EnsembleWitness (leanIsaEnsemble prog)) (j : Fin 8) : Air.Flat.Table K :=
  w.tables[(j : ℕ)]'(by rw [← w.same_length]; exact j.isLt)

/-- The rows of the `BLAKE2S` table. -/
abbrev blake2sRows (w : EnsembleWitness (leanIsaEnsemble prog)) : List (Array K) :=
  (tableAt w 5).table

/-- The rows of the memory block. -/
abbrev memBlockRows (w : EnsembleWitness (leanIsaEnsemble prog)) : List (Array K) :=
  (tableAt w 6).table

/-- The rows of the bytecode block. -/
abbrev bytecodeBlockRows (w : EnsembleWitness (leanIsaEnsemble prog)) : List (Array K) :=
  (tableAt w 7).table

/-- The messages the witness sends on the channel `c`, in table and row order: every
interaction on the channel of that name. -/
def messagesOn (w : EnsembleWitness (leanIsaEnsemble prog)) (c : RawChannel K) :
    List (Array K) :=
  (w.interactions.filter (·.channel.name = c.name)).map (·.msg)

/-- The messages one row of a table sends on the channel `c`. -/
def rowMessagesOn (t : Air.Flat.Table K) (row : Array K) (c : RawChannel K) : List (Array K) :=
  ((t.component.operations.interactionValues (t.environment row)).filter
    (·.channel.name = c.name)).map (·.msg)

/-- A raw row of the memory block, read as its typed row: the first `size MemRow` cells, a
missing cell `0`, as the block's constraints read it (Clean's `Component.rowInput`). -/
def memRowAt (w : EnsembleWitness (leanIsaEnsemble prog)) (row : Array K) : MemRow K :=
  valueFromOffset MemRow 0 (Environment.fromArray row w.data)

/-- A raw row of the `BLAKE2S` table, read as its typed row, likewise. -/
def blake2sRowAt (w : EnsembleWitness (leanIsaEnsemble prog)) (row : Array K) : Blake2sRow K :=
  valueFromOffset Blake2sRow 0 (Environment.fromArray row w.data)

/-! ## Balance -/

/-- Pushed and pulled messages of a channel pair form the same multiset (specification §5.1):
a permutation of message lists, counted in `ℕ`, never a field sum. -/
def BalancedPair (w : EnsembleWitness (leanIsaEnsemble prog)) (pull push : RawChannel K) :
    Prop :=
  (messagesOn w push).Perm (messagesOn w pull)

/-! ## The verifier's checks -/

/-- Every read pull of the six tables carries a nonzero count, message index `1` (bus
coordinate 2) of the memory and bytecode tuples: the nonzero count product (§6.2 "The count
product"; `layout.rs:73`, `:396-412`). The finalize counts of the two blocks are outside it
(§6.2). Both tuples have at least two coordinates (`MemMsg`, `BytecodeMsg`), so the
bound is never the reason the conjunct holds. -/
def CountsNonzero (w : EnsembleWitness (leanIsaEnsemble prog)) : Prop :=
  ∀ t ∈ w.tables.take 6, ∀ i ∈ t.interactions,
    (i.channel.name = MemPull.name ∨ i.channel.name = BytecodePull.name) →
      ∀ h : 1 < i.msg.size, i.msg[1] ≠ 0

/-- The M3 checks of the announced instance, two of the verifier's announcement checks
(`crates/verifier/src/layout.rs:414-418`; §6.2 "Instance caps"): the memory log-size window and
the row cap. The bytecode length and the public words' third limbs are
checked by type (`Program`, `PublicInput`); the WHIR rate and the stacked size are the protocol
layer's (see the module docstring). -/
structure Caps (w : EnsembleWitness (leanIsaEnsemble prog)) : Prop where
  /-- `MIN_LOG_MEM ≤ log_mem` (`:388`). -/
  minLogMem_le : minLogMem ≤ (imageOf w.data).1
  /-- `log_mem ≤ MAX_LOG_MEM` (`:388`). -/
  le_maxLogMem : (imageOf w.data).1 ≤ maxLogMem
  /-- Every table has at most `2^MAX_LOG_ROWS` rows (`rows <= 2**32`, `verifier.py:884`; the
  rows are the executed ones, announced as counts). The verifier's own table has one row and is
  not among `w.tables`. -/
  heights : ∀ t ∈ w.tables, t.table.length ≤ 2 ^ maxLogRows
  /-- Not a verifier check: the data's `"mem"` table has exactly the `2^κ` rows of its image
  (`imageOf`), the shape the announced `log_mem` implies for an honest prover. -/
  well_shaped : WellShapedData w.data

/-! ## The hypotheses Clean cannot yet express -/

/-- The `idx` column of row `i` of the memory block is `g^i`: the index column the verifier
computes (§6.5; `layout.rs:364`, `:375`). The bytecode block needs no such conjunct: its
index column is written by `bytecodeRowOf prog i` inside `BytecodeRowsAreTheProgram`, while
`SeedRowsAreTheImage` leaves the memory block's free, since the Rust computes the two from
different sources (the row index here, the program there). Removed by Clean PR #446. -/
def IndexColumnsAreRowIndices (w : EnsembleWitness (leanIsaEnsemble prog)) : Prop :=
  ∀ i (hi : i < (memBlockRows w).length), (memRowAt w (memBlockRows w)[i]).idx = gpow i

/-- The memory block's rows are the words of the image the prover data names, in order, for
some index column `idx` and finalize-count column `cntFin`: the committed columns `MEM_LO,
MEM_HI, MEM_TOP` are the image (§6.2 "Seed" and "Finalize"; `layout.rs:358-381`). Removed by
Clean PR #446. -/
def SeedRowsAreTheImage (w : EnsembleWitness (leanIsaEnsemble prog)) : Prop :=
  ∃ idx cntFin : Fin (2 ^ (imageOf w.data).1) → K,
    memBlockRows w = List.ofFn fun i ↦
      (toElements (⟨idx i, cntFin i, #v[((imageOf w.data).2 i).limb 0,
        ((imageOf w.data).2 i).limb 1, ((imageOf w.data).2 i).limb 2]⟩ : MemRow K)).toArray

/-- The bytecode block's rows are the program's: for some finalize-count column `cntFin`, the
block's raw rows are `bytecodeRowOf prog i (cntFin i)` for `i < 2 ^ prog.logSize`, in order.
The verifier forms the block's entry columns from the program itself (§8.5, Bus 4;
`Coord::Public`), the prover commits only `cntFin`; Clean PR #446's fixed columns are this
conjunct as a primitive. Its per-row reading is `BytecodeBindings prog`. -/
def BytecodeRowsAreTheProgram (prog : Program) (w : EnsembleWitness (leanIsaEnsemble prog)) :
    Prop :=
  ∃ cntFin : Fin (2 ^ prog.logSize) → K,
    bytecodeBlockRows w = List.ofFn fun i ↦ (toElements (bytecodeRowOf prog i (cntFin i))).toArray

/-! ## The BLAKE2s validity -/

/-- Every row of the `BLAKE2S` table satisfies the compression relation on its eighteen limbs
(`Blake2sRelation`, the table's `Assumptions`): what Flock proves of the region the limb columns
are routed to (§8.5 "BLAKE2s validity"; `crates/verifier/src/lib.rs:266-289`). The one conjunct
enforced outside the bus; the proof system discharges it from the Flock region. -/
def Blake2sRowsValid (w : EnsembleWitness (leanIsaEnsemble prog)) : Prop :=
  ∀ row ∈ blake2sRows w, Blake2sRelation (blake2sRowAt w row)

/-! ## The statement -/

/-- The witness `w` satisfies the constraint system of `prog` on `input`: the relation the
proof system proves and extracts (issue #13). `constraints` is Clean's; the three balances are
`BalancedPair`; `counts_nonzero` and `caps` are the verifier's checks; the three named
hypotheses are the facts Clean cannot yet express; `blake2s_valid` is Flock's; the two words
are §8.2's evaluation claim against the committed memory. -/
structure SatisfiedBy (prog : Program) (input : PublicInput)
    (w : EnsembleWitness (leanIsaEnsemble prog)) : Prop where
  /-- The public input is the run's: the four lanes (`PublicIO`). No component reads them; the
  run is bound to them by `word0_eq` and `word1_eq`. -/
  public_input_eq : w.publicInput = PublicIO.ofInput input
  /-- Every component's constraints hold on every row (Clean): the `JUMP` residuals, the
  other components having none. -/
  constraints : w.Constraints
  /-- The state pair balances (§6.1). -/
  state_balanced : BalancedPair w StatePull.toRaw StatePush.toRaw
  /-- The memory pair balances (§6.3). -/
  mem_balanced : BalancedPair w MemPull.toRaw MemPush.toRaw
  /-- The bytecode pair balances (§6.4). -/
  bytecode_balanced : BalancedPair w BytecodePull.toRaw BytecodePush.toRaw
  /-- Every read count is nonzero (§6.2). -/
  counts_nonzero : CountsNonzero w
  /-- The announced sizes are within the caps (§6.2). -/
  caps : Caps w
  /-- The memory block's index column is the row index (§6.5). -/
  index_columns : IndexColumnsAreRowIndices w
  /-- The memory block's rows are the image (§6.2). -/
  seed_rows : SeedRowsAreTheImage w
  /-- The bytecode block's rows are the program's (§8.5). -/
  bytecode_rows : BytecodeRowsAreTheProgram prog w
  /-- Every `BLAKE2S` row compresses (§8.5). -/
  blake2s_valid : Blake2sRowsValid w
  /-- The first word of the image is `input₀ + input₁·y` (§8.2). -/
  word0_eq : (imageOf w.data).2.read (gpow 0) = some input.word0
  /-- The second word of the image is `input₂ + input₃·y` (§8.2). -/
  word1_eq : (imageOf w.data).2.read (gpow 1) = some input.word1

/-! ## The trace a witness represents -/

/-- Some row of some table steps from `r` to `r'`: its one state pull is `r` and its one state
push is `r'` (§6.1). -/
def RowSteps (w : EnsembleWitness (leanIsaEnsemble prog)) (r r' : Regs K) : Prop :=
  ∃ t ∈ w.tables, ∃ row ∈ t.table,
    rowMessagesOn t row StatePull.toRaw = [#[r.pc, r.fp]] ∧
      rowMessagesOn t row StatePush.toRaw = [#[r'.pc, r'.fp]]

/-- The witness `w` represents the trace `t`: the image the data names is the trace's, and
each consecutive pair of the trace's register sequence `r_0, …, r_steps`
(`Trace.regs`) occurs as the state pull and push of some row (occurrence, not an injection of
steps into rows). The remaining rows are the closed walks of §8.3. -/
structure AssignmentRepresents (w : EnsembleWitness (leanIsaEnsemble prog)) (t : Trace prog) :
    Prop where
  /-- The memory log-size is the trace's. -/
  κ_eq : (imageOf w.data).1 = t.κ
  /-- Every word of the image is the trace's. -/
  image_eq : ∀ i (hi : i < 2 ^ t.κ), (imageOf w.data).2 ⟨i, κ_eq ▸ hi⟩ = t.image ⟨i, hi⟩
  /-- Each step of the register sequence occurs as some row's state pull and push. -/
  regs_embed : ∀ k (hk : k + 1 < t.regs.length), RowSteps w t.regs[k] t.regs[k + 1]

/-! ## Load-bearing lemmas -/

/-- A raw row written from a typed row reads back as it: reading at offset `0` inverts
`toElements`, for any row type and any data. -/
theorem rowAt_toElements {Row : TypeMap} [ProvableType Row] (data : ProverData K) (r : Row K) :
    valueFromOffset Row 0 (Environment.fromArray (toElements r).toArray data) = r := by
  unfold valueFromOffset
  convert ProvableType.fromElements_toElements r
  refine Vector.ext fun i hi ↦ ?_
  rw [Vector.getElem_mapRange]
  show ((toElements r).toArray[0 + i]?).getD 0 = _
  rw [Nat.zero_add, Array.getElem?_eq_getElem (by simpa using hi), Option.getD_some,
    Vector.getElem_toArray]

/-- `memRowAt` inverts `toElements`. -/
theorem memRowAt_toElements (w : EnsembleWitness (leanIsaEnsemble prog)) (r : MemRow K) :
    memRowAt w (toElements r).toArray = r :=
  rowAt_toElements w.data r

/-- `blake2sRowAt` inverts `toElements`. -/
theorem blake2sRowAt_toElements (w : EnsembleWitness (leanIsaEnsemble prog))
    (r : Blake2sRow K) : blake2sRowAt w (toElements r).toArray = r :=
  rowAt_toElements w.data r

/-- A table of the witness is `tableAt w j` for some `j`. -/
theorem mem_tables_iff {w : EnsembleWitness (leanIsaEnsemble prog)} {t : Air.Flat.Table K} :
    t ∈ w.tables ↔ ∃ j : Fin 8, tableAt w j = t := by
  rw [List.mem_iff_getElem]
  constructor
  · rintro ⟨i, hi, rfl⟩
    exact ⟨⟨i, by rwa [← w.same_length] at hi⟩, rfl⟩
  · rintro ⟨j, rfl⟩
    exact ⟨j, _, rfl⟩

/-- The component of `tableAt w j` is the ensemble's `j`-th. -/
theorem tableAt_component (w : EnsembleWitness (leanIsaEnsemble prog)) (j : Fin 8) :
    (tableAt w j).component = (leanIsaEnsemble prog).tables[(j : ℕ)] :=
  (w.same_circuits j j.isLt).symm

/-- The BLAKE2s validity is the whole of Clean's `w.Assumptions`: the `BLAKE2S` table's
`Assumptions` is `Blake2sRelation` and every other component's is `True`. This is the form
Clean's `TableSoundness` takes in `constraintSoundness`. -/
theorem assumptions_of_blake2sRowsValid {w : EnsembleWitness (leanIsaEnsemble prog)}
    (h : Blake2sRowsValid w) : w.Assumptions := by
  intro t ht
  simp only [EnsembleWitness.allTables, List.mem_cons] at ht
  rcases ht with rfl | ht
  · exact fun _ _ ↦ trivial
  · have hd : t.data = w.data := w.same_data t ht
    obtain ⟨j, rfl⟩ := mem_tables_iff.mp ht
    intro row hrow
    rw [tableAt_component, Air.Flat.Table.environment, hd]
    fin_cases j
    · exact trivial
    · exact trivial
    · exact trivial
    · exact trivial
    · exact trivial
    · exact h row hrow
    · exact trivial
    · exact trivial

/-- The image a representing witness names is the trace's, as one equality of dependent
pairs. -/
theorem assignmentRepresents_image {w : EnsembleWitness (leanIsaEnsemble prog)} {t : Trace prog}
    (h : AssignmentRepresents w t) : imageOf w.data = ⟨t.κ, t.image⟩ := by
  obtain ⟨κ, image, steps⟩ := t
  obtain ⟨hκ, himage, -⟩ := h
  revert hκ himage
  generalize imageOf w.data = s
  obtain ⟨κ', image'⟩ := s
  intro hκ himage
  dsimp only at hκ
  subst hκ
  congr 1
  funext ⟨i, hi⟩
  exact himage i hi

/-! ## Bus soundness, the interface

The four bus-soundness statements, as first specified; they are proved in
`LeanVM.Arithmetization.Soundness` (`Soundness/MemChannel.lean`, `BytecodeChannel.lean`,
`StateWalk.lean`), with `SentinelSafe` as the program condition. Channels are identified by name
and a pulled message is read as its typed form, as the module does (`messagesOn`, `memRowAt`):

```lean
/-- Specification Lemma 6.3, Thm. 6.4, Cor. 6.5: with nonzero counts and fewer than `2^64 - 1`
reads, balance of the memory pair makes every pulled memory tuple a correct read. -/
theorem mem_channel_sound (h : SatisfiedBy prog input w) :
    ∀ i ∈ w.interactions, i.channel.name = MemPull.name →
      ∀ m : MemMsg K, i.msg = (toElements m).toArray → MemPull.Guarantees m w.data

/-- The same for the bytecode pair, in the strong form: every pulled entry is the public
program's at the pulled counter (from `BytecodeRowsAreTheProgram prog`), which implies the
pull's guarantee, that it decodes, and is what `constraintSoundness` joins to `execute` by
`execute_of_step`. -/
theorem bytecode_channel_sound (h : SatisfiedBy prog input w) :
    ∀ i ∈ w.interactions, i.channel.name = BytecodePull.name →
      ∀ m : BytecodeMsg K, i.msg = (toElements m).toArray →
        ∃ k : Fin (2 ^ prog.logSize), m.pc = gpow k ∧ #v[m.opcode] ++ m.op = entry (prog.code k)

/-- No row sits at the sentinel counter: its bytecode entry is not a `JUMP`, so the row would
push `(g^N_prog, fp)`, a counter no bytecode read can balance. -/
theorem no_row_at_sentinel (hsafe : SentinelSafe prog) (h : SatisfiedBy prog input w) :
    ∀ i ∈ w.interactions, i.channel.name = StatePull.name →
      ∀ pc fp : K, i.msg = #[pc, fp] → pc ≠ prog.finalPc

/-- Specification Prop. 6.1: a balanced state channel over rows that are steps contains a run
from `(1, 1)` to `(g^(N_prog - 1), 1)`; the remaining rows are closed walks. -/
theorem exists_run_of_balanced (hsafe : SentinelSafe prog) (h : SatisfiedBy prog input w) :
    ∃ n, run prog (imageOf w.data).2 n Regs.initial = some (Regs.final prog)
```

The read bound `mem_channel_sound` needs is derived from `Caps` (`≤ 10 · 6 · 2^32`), never
assumed; `SentinelSafe prog` is the one hypothesis on the program, and only soundness takes it.
-/

end LeanVM.Arithmetization
