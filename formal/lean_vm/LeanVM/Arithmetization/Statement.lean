/-
  LeanVM.Arithmetization.Statement

  The constraint statement of leanISA: the ensemble of the six opcode tables, the two seed
  blocks and the verifier; bus balance as a multiset equality; the checks the verifier makes
  on the announced instance; what the fixed columns and the derived prover data give; the relation
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
public import LeanVM.Arithmetization.Tables.Keccak
public import Clean.Air.FlatEnsemble

@[expose] public section

/-!
# The constraint statement

At leanVM pin `4af2cdddd7cd41b9df2cc7e123e314a91b0b4462` and Clean pin `b41c196b`. The
statement itself is written from the specification, as what the M3 model means by an
accepted instance (specification §5, `doc/leanvm/body/05-arithmetization.tex:4`: "an instance
is accepted exactly when every table's constraints hold and the bus balances", the balance
being the multiset equality of `:14`), and what the verifier checks of an announced instance
is transcribed: the caps (`crates/verifier/src/lib.rs:227-245` and
`crates/verifier/src/layout.rs:478-489`, the
announcement checks of `walk` and `build_layout`, which replace `read_public` of `a386121f`;
§6.2 "Instance caps", `06-bus-interactions.tex:80`), the nonzero count product (§6.2 "The count
product", `:78`; `cpu/layout.rs:136`, the count channel of the six tables' read-count columns,
`:396-412`), the public words against the committed memory (§8.2,
`08-end-to-end-protocol.tex:27-37`), the public parts of the bus the verifier forms itself, the
index column and the program's share of the bytecode blocks (§8.6, `:105`; §6.5,
`06-bus-interactions.tex:98`), and the `KECCAK` validity the Keccak reduction proves
(`walk` step 6, `verifier/src/lib.rs:283-300` at `40f877dc`). This file is the accept relation of
the M3 constraint system and its ensemble, a statement with no soundness or completeness theorem:
it is what `constraintSoundness` and `constraintCompleteness` are about.

**The ensemble.** `leanIsaEnsemble prog κ` is Clean's `Ensemble`: the six opcode tables
(`opcodeComponent`, rows by demand) and the two seed blocks of `Boundary` as its components, each
named as leanVM names it (Clean keys the prover data by name), the six channels of `Channels`, and
the verifier `leanIsaVerifier prog`, a `Verifier.Program`. The two blocks are preallocated
(`memComponent κ`, `bytecodeComponent prog`): `2^κ` rows for the announced `log_mem = κ` and
`2^N` for the program, their index columns `g^i` and the bytecode block's entry columns *fixed*,
which the verifier computes (leanVM's index column and `Coord::Public` columns). So the instance
is a function of the program and of `log_mem`, as leanVM's `layout(prog, log_mem, taus, pi)` is:
of the program through the sentinel the verifier pulls and the bytecode block's fixed columns, of
`log_mem` through the memory block's height; the opcode tables are program-free, as leanVM's AIRs
are. A witness `w : EnsembleWitness (leanIsaEnsemble prog κ)` is Clean's: one `Air.Flat.Table`
of raw rows per component, each preallocated table's rows agreeing with its fixed cells, and the
public input; its prover data `w.data` is not chosen but derived, the tables' input rows under
their names (`deriveProverData`). The constraints `w.Constraints` ("every component's constraints
hold on every row") are Clean's own, consumed unchanged.

**Reading a witness.** Tables are read by position in the ensemble's `tables` (`tableAt`),
and channels by name (`messagesOn`, `rowMessagesOn`): Clean's `RawChannel` carries
propositions and has no decidable equality, and the six channels are told apart by name as
`channelDir` and `channelSep` already read them. A raw row is read as its typed row
exactly as the component's constraints read it (`memRowAt`, `keccakRowAt`: Clean's
`Component.rowInput`, the first `size Row` cells of the row, a missing cell `0`).

**Balance.** `BalancedPair w pull push` says the messages pushed on `push` and the messages
pulled on `pull` form the same multiset (§5.1 "Balance", `05-arithmetization.tex:14`): a
`List.Perm`, counted in `ℕ`. It is never a field sum, Clean's LogUp `Balance`:
`ringChar K = 2`, so a message pushed twice and never pulled has field-sum balance `2 = 0`.
Balance counts every interaction once, whatever its multiplicity, as the M3 bus flushes it and
as the Rust verifier does: every interaction has multiplicity `1` but the pull of a `KECCAK`
gated output cell (`memReadIf`), of multiplicity `flag`, which is flushed at every flag; at flag
`0` its push is its own tuple, the pair cancels, and `Soundness.MemChannel` drops it before the
lookup argument. The direction of an interaction is the channel it is on: the
three pairs `(StatePull, StatePush)`, `(MemPull, MemPush)`, `(BytecodePull, BytecodePush)`; the
direction Clean now tags every interaction with agrees (a `*.pull` channel carries pulls only).

**The verifier's checks.** `CountsNonzero w` is the nonzero count product: every read pull of
the six tables carries a nonzero count, message index `1` (bus coordinate 2) of a memory or
bytecode tuple (§6.2 "The count product"; `layout.rs:136` and `:463-479`, the count channel
stacks the read-count columns of the six tables and nothing else, so the finalize counts of
the two blocks are outside it, as §6.2 "Nothing checks the finalize counts" says). `Caps w` is
the M3 part of the announcement checks (`read_public` at `a386121f`; at `leanvm-rev`, `walk` and
`build_layout`, `verifier/src/lib.rs:243-261` and `verifier/src/layout.rs:483-494`, behind the
wrapper `crates/leanvm_core/src/cpu/mod.rs:627-639`), which make eight checks: (1) the
announced sizes have zero upper limbs (`verifier/src/lib.rs:248-252`, the transcript format) and
(2) the two public words are two-limb words (`cpu/mod.rs:627`, `[F128; 2]`), both by type here
(`PublicInput.word0`, `word1`); (3) the bytecode length is a power of two at most `2^32`
(`cpu/mod.rs:629`, `verifier/src/layout.rs:488` and `:492`), `Program`'s by type
(`LeanIsaProgram.logSize_le`); (4) the memory log-size is within
`[MIN_LOG_MEM, MAX_LOG_MEM] = [16, 32]` (`verifier/src/layout.rs:490`); (5) every table has at most
`2^MAX_LOG_ROWS` rows (`verifier/src/layout.rs:491`; the prover announces each table's row count, the rows
past it in the table's height being padding rows, which the bus never sees, so the witness's tables
are the executed rows only); (6) the `KECCAK` table's height floor (`TABLE_LOG_FLOORS`) is the
protocol layer's, its padding rows being outside the bus; (7) the WHIR rate
(`verifier/src/lib.rs:256`) and (8) the stacked size `mu ∈ [MIN_MU, MAX_MU]`
(`verifier/src/lib.rs:258-261`) are parameters of the commitment, left to the protocol layer, which
reads them off the same announcement. `Caps` transcribes (4), on the announced `κ`, and (5). That
the prover data is well shaped (`WellShapedData`, so that `imageOf` drops no row) is no longer a
hypothesis: the data is the memory block's `2^κ` rows (`Caps.well_shaped`). These caps are what
keeps the total read count below `2^64 - 1`, the bound the bus argument of `Soundness` needs
(Lemma 6.3).

**The fixed columns and the derived data** (Clean PR #446, which the statement anticipated; until
it, three hypotheses of `SatisfiedBy`). The memory block's index column is fixed to `g^i`, so
`IndexColumnsAreRowIndices w` is a theorem (§6.5, the index column the verifier computes;
`layout.rs:431` and `:442`, `Index`). The prover data is derived from the rows, and the memory
block, named `"mem"`, holds the limbs in its first two cells, so the image the data names *is* the
block (`memRows_data`) and `SeedRowsAreTheImage w` is a theorem (§6.2 "Seed" and "Finalize";
`cpu/layout.rs:431-440` at `leanvm-rev`, `MEM_LO, MEM_HI` and `MFCNT`, the index and finalize
columns free).
The bytecode block's counter and entry columns are fixed to the program's, so
`BytecodeRowsAreTheProgram prog w` is a theorem (§8.6 Bus 4: the verifier forms "the program's
whole share of the two bytecode blocks" itself; `layout.rs:354-356` and `:449-461`,
`Coord::Public` and `BFCNT`). The three keep their names as projections of `SatisfiedBy`
(`SatisfiedBy.index_columns`, `seed_rows`, `bytecode_rows`); their per-row readings are
`memRowOf_bindings` and `BytecodeBindings prog`.

**The `KECCAK` validity.** `KeccakRowsValid w`, every row of the `KECCAK` table satisfies
`KeccakRelation` (the component's `Assumptions`: its output lanes are Keccak-f[1600] of its input
lanes), is the one conjunct the verifier enforces outside the bus: the table has no constraint on
its lanes, and the permutation is proved by the Keccak reduction on the input lanes committed in
`q_keccak` and the output lanes the table's claims hand it (`lib.rs:283-300` at `40f877dc`).
Clean's `EnsembleWitness.Constraints` does not include a component's `Assumptions`, and its
`AssumptionsConsistency` sources them from the public input alone, so the fact is a conjunct of the
statement, and `assumptions_of_keccakRowsValid` turns it into the `w.Assumptions` that Clean's
`Table.weakSoundness` takes. The conjunct stays: the proof system's adaptor discharges it from the Keccak
region.

**The statement.** `SatisfiedBy prog input w` is the relation the proof system proves and
extracts (issue #13), a structure with named fields so that the soundness and completeness
proofs project the conjunct they consume by name. Its `constraints` field is Clean's; only
the `JUMP` table emits an assertion (`tables.rs:762-769`; the other seven components and the
verifier have none), so the field reduces to the `JUMP` residuals on every `JUMP` row.
The `public_input_eq` field is read by no component: the lanes bind the run through
`word0_eq` and `word1_eq`, the two public words at `g^0` and `g^1` of the image the data
names (§8.2, the evaluation claim against the committed memory; spelled as
`HoldsPublicInput` spells it, through `MemoryImage.read`).

**The trace.** `AssignmentRepresents w t` says what a witness of `SatisfiedBy` is a witness
of: the image the data names is the trace's (`κ_eq`, `image_eq`; `assignmentRepresents_image`
reads the two as one equality of dependent pairs), and each consecutive pair `(r_k, r_{k+1})`
of the trace's register sequence `r_0, …, r_steps` (`Execution.regs`) occurs as the
state pull and the state push of some row of some table (`RowSteps`). Occurrence, not an
injection of steps into rows: a witness with one traversal of a loop represents a trace with
two, and the image determines the run. The remaining rows are the closed walks of §8.3, about
which nothing is claimed. `constraintSoundness` yields a trace the witness
represents, and `constraintCompleteness` a witness representing the trace.

## Bus soundness

The bus-soundness statements, recorded at the end of this file as their original interface,
are proved in `LeanVM.Arithmetization.Soundness` (`mem_channel_sound`,
`bytecode_channel_sound`, `exists_run_of_balanced`).

## Wrong readings excluded

* Balance is a permutation, not a field sum: `BalancedPair` is `List.Perm`;
  Clean's `Ensemble.Statement` is not consumed.
* A channel is identified by its name, never by the sign of a multiplicity:
  `messagesOn` filters by `RawChannel.name`, and a push on the pull channel of a pair
  would count as a pull (`memRead` and `bytecodeRead` never do that).
* The count product covers the six tables' read counts and nothing else: `CountsNonzero`
  quantifies over `w.tables.take 6`, and a finalize count of `0` is rejected by balance alone
  (§6.2).
* The permutation is not a constraint of the table and not a bus fact: `KeccakRowsValid` is
  a conjunct of its own, discharged by the Keccak reduction, never by `w.Constraints` (which the
  `KECCAK` table satisfies on every row) and never by balance (which binds the lanes to the cells,
  not the output to the input).
* The program is in no committed column: it enters the ensemble through the verifier's sentinel
  and the bytecode block's fixed columns, which pin the block's public columns to it
  (`BytecodeRowsAreTheProgram prog`, a theorem). `log_mem` enters through the memory block's
  height; the prover data is derived, never chosen.
* The public words are not on the bus (§8.2): `word0_eq` and `word1_eq` read the image the
  data names, as `HoldsPublicInput` reads the trace's.
* The state pull carries no guarantee: `AssignmentRepresents` claims the
  run's steps are rows, and nothing about the rows that are not.
-/

namespace LeanVM.Arithmetization

open LeanVM.Parameters LeanVM.Semantics
open Air.Flat (Ensemble EnsembleWitness Component)

/-! ## The components -/

/-- An opcode table as a component: its rows are made by demand, one per step of the run, so it
has no fixed cell, and its assumptions are its circuit's, the ensemble's to provide: `True` but for
`KECCAK`, whose `KeccakRelation` the statement provides (`KeccakRowsValid`). Clean's witness
generator is not run on this ensemble (the rows are the Rust prover's, and in Lean
`Completeness`'s): the demand mode answers no message (its guard is false) and its input is a
placeholder, never read by soundness, which reads only fixed cells. -/
def opcodeComponent {Row : TypeMap} [ProvableType Row] (c : GeneralFormalCircuit K Row Registers) :
    Component K where
  circuit := c
  generation := .demand
    { channel := StatePush
      trigger := .push
      guard := fun _ ↦ .false
      input := fun _ ↦ pure (fromElements (Vector.replicate _ committedCell)) }
  Assumptions := c.Assumptions
  circuit_assumptions_of_assumptions _ _ _ _ _ h := h

/-! ## The ensemble -/

/-- The leanISA ensemble of the public program `prog` with a memory of `2^κ` words (`κ` the
announced `log_mem`): the six opcode tables, the memory and bytecode blocks, preallocated with
their index and entry columns fixed, the six channels, and the verifier `leanIsaVerifier prog`
(`layout.rs:418-461`). The instance is a function of the program and `log_mem`, as leanVM's
`layout(prog, log_mem, …)` is. -/
def leanIsaEnsemble (prog : LeanIsaProgram) (κ : ℕ) : Ensemble K PublicIO where
  tables := [opcodeComponent xorTable, opcodeComponent mulTable, opcodeComponent setTable,
    opcodeComponent derefTable, opcodeComponent jumpTable, opcodeComponent keccakTable,
    memComponent κ, bytecodeComponent prog]
  unique_names := by
    show ["XOR", "MUL", "SET", "DEREF", "JUMP", "KECCAK", "mem", "bytecode"].Nodup
    decide
  channels := [StatePull.toRaw, StatePush.toRaw, MemPull.toRaw, MemPush.toRaw,
    BytecodePull.toRaw, BytecodePush.toRaw]
  unique_channel_names := by
    show ["st.pull", "st.push", "mem.pull", "mem.push", "bc.pull", "bc.push"].Nodup
    decide
  verifier := leanIsaVerifier prog
  -- Each component's channels, its pulls (with guarantees) then its pushes (with requirements),
  -- as Clean's elaboration lists them.
  tables_channels := by
    simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · show [StatePull.toRaw, BytecodePull.toRaw] ++ List.replicate 3 MemPull.toRaw ++
        [StatePush.toRaw, MemPush.toRaw, BytecodePush.toRaw] ⊆ _
      simp [List.subset_def]
    · show [StatePull.toRaw, BytecodePull.toRaw] ++ List.replicate 3 MemPull.toRaw ++
        [StatePush.toRaw, MemPush.toRaw, BytecodePush.toRaw] ⊆ _
      simp [List.subset_def]
    · show [StatePull.toRaw, BytecodePull.toRaw] ++ List.replicate 1 MemPull.toRaw ++
        [StatePush.toRaw, MemPush.toRaw, BytecodePush.toRaw] ⊆ _
      simp [List.subset_def]
    · show [StatePull.toRaw, BytecodePull.toRaw] ++ List.replicate 3 MemPull.toRaw ++
        [StatePush.toRaw, MemPush.toRaw, BytecodePush.toRaw] ⊆ _
      simp [List.subset_def]
    · show [StatePull.toRaw, BytecodePull.toRaw] ++ List.replicate 3 MemPull.toRaw ++
        [StatePush.toRaw, MemPush.toRaw, BytecodePush.toRaw] ⊆ _
      simp [List.subset_def]
    · show [StatePull.toRaw, BytecodePull.toRaw] ++ List.replicate 26 MemPull.toRaw ++
        [StatePush.toRaw, MemPush.toRaw, BytecodePush.toRaw, MemPull.toRaw] ⊆ _
      simp [List.subset_def]
    · show [MemPull.toRaw] ++ [MemPush.toRaw] ⊆ _
      simp [List.subset_def]
    · show [BytecodePull.toRaw] ++ [BytecodePush.toRaw] ⊆ _
      simp [List.subset_def]
  verifier_channels := by simp [circuit_norm, leanIsaVerifier]

/-! ## Reading a witness -/

variable {prog : LeanIsaProgram} {κ : ℕ}

/-- The witness's table of component `j`, in the order of the ensemble's `tables`: `XOR`,
`MUL_NATIVE`, `SET_CONSTANT`, `DEREF`, `JUMP`, `KECCAK`, then the memory block and the
bytecode block. -/
def tableAt (w : EnsembleWitness (leanIsaEnsemble prog κ)) (j : Fin 8) : Air.Flat.Table K :=
  w.tables[(j : ℕ)]'(by rw [← w.same_length]; exact j.isLt)

/-- The rows of the `KECCAK` table. -/
abbrev keccakRows (w : EnsembleWitness (leanIsaEnsemble prog κ)) : List (Array K) :=
  (tableAt w 5).table

/-- The rows of the memory block. -/
abbrev memBlockRows (w : EnsembleWitness (leanIsaEnsemble prog κ)) : List (Array K) :=
  (tableAt w 6).table

/-- The rows of the bytecode block. -/
abbrev bytecodeBlockRows (w : EnsembleWitness (leanIsaEnsemble prog κ)) : List (Array K) :=
  (tableAt w 7).table

/-- The messages the witness sends on the channel `c`, in table and row order: every
interaction on the channel of that name. -/
def messagesOn (w : EnsembleWitness (leanIsaEnsemble prog κ)) (c : RawChannel K) :
    List (Array K) :=
  (w.interactions.filter (·.channel.name = c.name)).map (·.msg)

/-- The messages one row of a table sends on the channel `c`. -/
def rowMessagesOn (t : Air.Flat.Table K) (row : Array K) (c : RawChannel K) : List (Array K) :=
  ((t.component.operations.interactionValues (t.environment row)).filter
    (·.channel.name = c.name)).map (·.msg)

/-- A raw row of the memory block, read as its typed row: the first `size MemRow` cells, a
missing cell `0`, as the block's constraints read it (Clean's `Component.rowInput`). -/
def memRowAt (w : EnsembleWitness (leanIsaEnsemble prog κ)) (row : Array K) : MemRow K :=
  valueFromOffset MemRow 0 (Environment.fromArray row w.data)

/-- A raw row of the `KECCAK` table, read as its typed row, likewise. -/
def keccakRowAt (w : EnsembleWitness (leanIsaEnsemble prog κ)) (row : Array K) : KeccakRow K :=
  valueFromOffset KeccakRow 0 (Environment.fromArray row w.data)

/-! ## Balance -/

/-- Pushed and pulled messages of a channel pair form the same multiset (specification §5.1):
a permutation of message lists, counted in `ℕ`, never a field sum. -/
def BalancedPair (w : EnsembleWitness (leanIsaEnsemble prog κ)) (pull push : RawChannel K) :
    Prop :=
  (messagesOn w push).Perm (messagesOn w pull)

/-! ## The verifier's checks -/

/-- Every read pull of the six tables carries a nonzero count, message index `1` (bus
coordinate 2) of the memory and bytecode tuples: the nonzero count product (§6.2 "The count
product"; `layout.rs:136`, `:463-479`). The finalize counts of the two blocks are outside it
(§6.2). Both tuples have at least two coordinates (`MemMsg`, `BytecodeMsg`), so the
bound is never the reason the conjunct holds. -/
def CountsNonzero (w : EnsembleWitness (leanIsaEnsemble prog κ)) : Prop :=
  ∀ t ∈ w.tables.take 6, ∀ i ∈ t.interactions,
    (i.channel.name = MemPull.name ∨ i.channel.name = BytecodePull.name) →
      ∀ h : 1 < i.msg.size, i.msg[1] ≠ 0

/-- The M3 checks of the announced instance, two of the verifier's announcement checks
(`crates/verifier/src/layout.rs:489-494` at `leanvm-rev`; §6.2 "Instance caps"): the window of the announced memory
log-size `κ` and the row cap. The bytecode length and the public words' two limbs are checked by
type (`Program`, `PublicInput`); the WHIR rate and the stacked size are the protocol layer's (see
the module docstring). -/
structure Caps (w : EnsembleWitness (leanIsaEnsemble prog κ)) : Prop where
  /-- `MIN_LOG_MEM ≤ log_mem` (`:490`). -/
  minLogMem_le_logMem : minLogMem ≤ κ
  /-- `log_mem ≤ MAX_LOG_MEM` (`:490`). -/
  logMem_le_maxLogMem : κ ≤ maxLogMem
  /-- Every table has at most `2^MAX_LOG_ROWS` rows (`rows <= 1 << MAX_TABLE_LOG`, `layout.rs:491`
  at `leanvm-rev`; the rows are the executed ones, announced as counts). The verifier is not among
  `w.tables`. -/
  heights : ∀ t ∈ w.tables, t.table.length ≤ 2 ^ maxLogRows

/-! ## What the fixed columns and the derived data give

These three were hypotheses of the statement until Clean's fixed columns and proof-derived prover
data (Clean PR #446); they are now theorems (`SatisfiedBy.index_columns`, `SatisfiedBy.seed_rows`,
`SatisfiedBy.bytecode_rows`). -/

/-- The `idx` column of row `i` of the memory block is `g^i`: the index column the verifier
computes (§6.5; `layout.rs:431`, `:442`). -/
def IndexColumnsAreRowIndices (w : EnsembleWitness (leanIsaEnsemble prog κ)) : Prop :=
  ∀ i (hi : i < (memBlockRows w).length), (memRowAt w (memBlockRows w)[i]).idx = addressOfIndex i

/-- The memory block's rows are the words of the image the prover data names, in order, for
some index column `idx` and finalize-count column `cntFin`: the committed columns `MEM_LO,
MEM_HI` are the image (§6.2 "Seed" and "Finalize"; `cpu/layout.rs:431-440` at `leanvm-rev`). -/
def SeedRowsAreTheImage (w : EnsembleWitness (leanIsaEnsemble prog κ)) : Prop :=
  ∃ idx cntFin : Fin (2 ^ (imageOf w.data).1) → K,
    memBlockRows w = List.ofFn fun i ↦
      (toElements (⟨#v[((imageOf w.data).2 i).limb 0, ((imageOf w.data).2 i).limb 1], idx i,
        cntFin i⟩ : MemRow K)).toArray

/-- The bytecode block's rows are the program's: for some finalize-count column `cntFin`, the
block's raw rows are `bytecodeRowOf prog i (cntFin i)` for `i < 2 ^ prog.logSize`, in order.
The verifier forms the block's entry columns from the program itself (§8.6, Bus 4;
`Coord::Public`), the prover commits only `cntFin`. Its per-row reading is
`BytecodeBindings prog`. -/
def BytecodeRowsAreTheProgram (prog : LeanIsaProgram)
    (w : EnsembleWitness (leanIsaEnsemble prog κ)) : Prop :=
  ∃ cntFin : Fin (2 ^ prog.logSize) → K,
    bytecodeBlockRows w = List.ofFn fun i ↦ (toElements (bytecodeRowOf prog i (cntFin i))).toArray

/-! ## The `KECCAK` validity -/

/-- Every row of the `KECCAK` table satisfies the permutation relation on its lanes
(`KeccakRelation`, the component's `Assumptions`): what the Keccak reduction proves
(`lib.rs:283-300` at `40f877dc`). The one conjunct enforced outside the bus; the proof system
discharges it from the Keccak region. -/
def KeccakRowsValid (w : EnsembleWitness (leanIsaEnsemble prog κ)) : Prop :=
  ∀ row ∈ keccakRows w, KeccakRelation (keccakRowAt w row)

/-! ## The statement -/

/-- The witness `w` satisfies the constraint system of `prog` on `input`, its memory announced
at `2^κ` words: the relation the proof system proves and extracts (issue #13). `constraints` is
Clean's, with the fixed columns and the derived prover data in the witness itself; the three
balances are `BalancedPair`; `counts_nonzero` and `caps` are the verifier's checks;
`keccak_valid` is the Keccak reduction's; the two words are §8.2's evaluation claim against the
committed memory. -/
structure SatisfiedBy (prog : LeanIsaProgram) (input : PublicInput)
    (w : EnsembleWitness (leanIsaEnsemble prog κ)) : Prop where
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
  /-- Every `KECCAK` row permutes. -/
  keccak_valid : KeccakRowsValid w
  /-- The first word of the image is `input₀ + input₁·y` (§8.2). -/
  word0_eq : (imageOf w.data).2.read (addressOfIndex 0) = some input.word0
  /-- The second word of the image is `input₂ + input₃·y` (§8.2). -/
  word1_eq : (imageOf w.data).2.read (addressOfIndex 1) = some input.word1

/-! ## The trace a witness represents -/

/-- Some row of some table steps from `r` to `r'`: its one state pull is `r` and its one state
push is `r'` (§6.1). -/
def RowSteps (w : EnsembleWitness (leanIsaEnsemble prog κ)) (r r' : Registers K) : Prop :=
  ∃ t ∈ w.tables, ∃ row ∈ t.table,
    rowMessagesOn t row StatePull.toRaw = [#[r.pc, r.fp]] ∧
      rowMessagesOn t row StatePush.toRaw = [#[r'.pc, r'.fp]]

/-- The witness `w` represents the trace `t`: the image the data names is the trace's, and
each consecutive pair of the trace's register sequence `r_0, …, r_steps`
(`Execution.regs`) occurs as the state pull and push of some row (occurrence, not an injection of
steps into rows). The remaining rows are the closed walks of §8.3. -/
structure AssignmentRepresents (w : EnsembleWitness (leanIsaEnsemble prog κ))
    (t : Execution prog) : Prop where
  /-- The memory log-size is the trace's. -/
  κ_eq : (imageOf w.data).1 = t.logMemorySize
  /-- Every word of the image is the trace's. -/
  image_eq : ∀ i (hi : i < 2 ^ t.logMemorySize), (imageOf w.data).2 ⟨i, κ_eq ▸ hi⟩ = t.memory ⟨i, hi⟩
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
theorem memRowAt_toElements (w : EnsembleWitness (leanIsaEnsemble prog κ)) (r : MemRow K) :
    memRowAt w (toElements r).toArray = r :=
  rowAt_toElements w.data r

/-- `keccakRowAt` inverts `toElements`. -/
theorem keccakRowAt_toElements (w : EnsembleWitness (leanIsaEnsemble prog κ))
    (r : KeccakRow K) : keccakRowAt w (toElements r).toArray = r :=
  rowAt_toElements w.data r

/-- A table of the witness is `tableAt w j` for some `j`. -/
theorem mem_tables_iff {w : EnsembleWitness (leanIsaEnsemble prog κ)} {t : Air.Flat.Table K} :
    t ∈ w.tables ↔ ∃ j : Fin 8, tableAt w j = t := by
  rw [List.mem_iff_getElem]
  constructor
  · rintro ⟨i, hi, rfl⟩
    exact ⟨⟨i, by rwa [← w.same_length] at hi⟩, rfl⟩
  · rintro ⟨j, rfl⟩
    exact ⟨j, _, rfl⟩

/-- The component of `tableAt w j` is the ensemble's `j`-th. -/
theorem tableAt_component (w : EnsembleWitness (leanIsaEnsemble prog κ)) (j : Fin 8) :
    (tableAt w j).component = (leanIsaEnsemble prog κ).tables[(j : ℕ)] :=
  (w.same_circuits j j.isLt).symm

/-- The `KECCAK` validity is the whole of Clean's `w.Assumptions`: the `KECCAK` component's
`Assumptions` is `KeccakRelation` and every other component's is `True`. This is the form
Clean's `Table.weakSoundness` takes in `constraintSoundness`. -/
theorem assumptions_of_keccakRowsValid {w : EnsembleWitness (leanIsaEnsemble prog κ)}
    (h : KeccakRowsValid w) : w.Assumptions := by
  intro t ht
  have hd : t.data = w.data := w.same_data t ht
  obtain ⟨j, rfl⟩ := mem_tables_iff.mp ht
  intro row hrow
  simp only [Component.RowAssumptions, Air.Flat.Table.environment]
  rw [tableAt_component]
  fin_cases j
  · exact trivial
  · exact trivial
  · exact trivial
  · exact trivial
  · exact trivial
  · rw [hd]; exact h row hrow
  · exact trivial
  · exact trivial

/-- The image a representing witness names is the trace's, as one equality of dependent
pairs. -/
theorem assignmentRepresents_image {w : EnsembleWitness (leanIsaEnsemble prog κ)}
    {t : Execution prog} (h : AssignmentRepresents w t) :
    imageOf w.data = ⟨t.logMemorySize, t.memory⟩ := by
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

/-! ## What the fixed columns and the derived data give

Clean derives the prover data from the witness's rows (`deriveProverData`, keyed by component
name), and checks every preallocated row against its fixed cells (`Table.fixed_rows_match`). So the
memory block is the image (`memRows_data`), its index column is the row index, and the bytecode
block is the program: the three facts that were hypotheses of the statement until Clean's fixed
columns, now theorems of every witness (`SatisfiedBy.index_columns`, `SatisfiedBy.seed_rows`,
`SatisfiedBy.bytecode_rows`), and the data is well shaped (`Caps.well_shaped`). -/

/-- The memory block's rows have four cells: its input, no local witness. -/
theorem memComponent_width : (memComponent κ).width = 4 := rfl
/-- The bytecode block's rows have fifteen cells. -/
theorem bytecodeComponent_width : (bytecodeComponent prog).width = 15 := rfl

/-- The witness's tables carry the ensemble's names, which are distinct. -/
theorem names_nodup (w : EnsembleWitness (leanIsaEnsemble prog κ)) :
    (w.tables.map fun t ↦ t.component.circuit.name).Nodup := by
  have h := (leanIsaEnsemble prog κ).unique_names
  rw [← w.tables_map_component, List.map_map] at h
  exact h

theorem tableAt_mem (w : EnsembleWitness (leanIsaEnsemble prog κ)) (j : Fin 8) :
    tableAt w j ∈ w.tables := List.getElem_mem _

/-- **The image is the memory block.** The prover data's `"mem"` table, which `imageOf` reads, is
Clean's derivation from the witness: the memory block's rows cut at two cells, its limbs. -/
theorem memRows_data (w : EnsembleWitness (leanIsaEnsemble prog κ)) :
    memRows w.data = ((memBlockRows w).map (Air.Flat.rowPrefix 2)).toArray := by
  have h := Air.Flat.deriveProverData_eq_of_mem w.tables (names_nodup w) (tableAt_mem w 6) 2
  rw [tableAt_component] at h
  exact h

/-- The memory block's rows are its `2^κ` preallocated rows, each agreeing with the fixed cells of
its index. -/
theorem memBlock_fixed (w : EnsembleWitness (leanIsaEnsemble prog κ)) :
    (memBlockRows w).length = (UInt64.ofNat (2 ^ κ)).toNat ∧
      ∀ i (hi : i < (memBlockRows w).length), (memMode κ).FixedAt (UInt64.ofNat i)
        (fromElements (Air.Flat.rowPrefix (size MemRow) (memBlockRows w)[i])) := by
  have h := (tableAt w 6).fixed_rows_match
  rw [tableAt_component] at h
  exact h

/-- The bytecode block's rows are its `2^N` preallocated rows, each agreeing with the fixed cells of
its index. -/
theorem bytecodeBlock_fixed (w : EnsembleWitness (leanIsaEnsemble prog κ)) :
    (bytecodeBlockRows w).length = (UInt64.ofNat (2 ^ prog.logSize)).toNat ∧
      ∀ i (hi : i < (bytecodeBlockRows w).length), (bytecodeMode prog).FixedAt (UInt64.ofNat i)
        (fromElements (Air.Flat.rowPrefix (size BytecodeRow) (bytecodeBlockRows w)[i])) := by
  have h := (tableAt w 7).fixed_rows_match
  rw [tableAt_component] at h
  exact h

theorem rowPrefix_toArray {n : ℕ} {row : Array K} (h : row.size = n) :
    (Air.Flat.rowPrefix n row).toArray = row := by
  subst h
  apply Array.ext
  · simp [Air.Flat.rowPrefix]
  · intro i h1 h2
    simp [Air.Flat.rowPrefix]

/-- A row as wide as its type is its typed reading, written back. -/
theorem toElements_rowPrefix {Row : TypeMap} [ProvableType Row] {row : Array K}
    (h : row.size = size Row) :
    (toElements (fromElements (Air.Flat.rowPrefix (size Row) row) : Row K)).toArray = row := by
  rw [ProvableType.toElements_fromElements, rowPrefix_toArray h]

theorem memRowAt_eq (w : EnsembleWitness (leanIsaEnsemble prog κ)) (row : Array K) :
    memRowAt w row = fromElements (Air.Flat.rowPrefix (size MemRow) row) :=
  Air.Flat.valueFromOffset_fromArray row w.data

theorem memBlockRows_length (w : EnsembleWitness (leanIsaEnsemble prog κ)) (hκ : κ < 64) :
    (memBlockRows w).length = 2 ^ κ := by
  rw [(memBlock_fixed w).1, UInt64.toNat_ofNat_of_lt' (Nat.pow_lt_pow_right (by norm_num) hκ)]

/-- The image the data names has the announced size. -/
theorem imageOf_fst (w : EnsembleWitness (leanIsaEnsemble prog κ)) (hκ : κ ≤ maxLogMem) :
    (imageOf w.data).1 = κ := by
  show min (Nat.log 2 (memRows w.data).size) maxLogMem = κ
  rw [memRows_data, List.size_toArray, List.length_map,
    memBlockRows_length w (lt_of_le_of_lt hκ (by decide)), Nat.log_pow (by norm_num),
    Nat.min_eq_left hκ]

/-- The derived data is well shaped: the `"mem"` table has the `2^κ` rows of the image. -/
theorem wellShaped (w : EnsembleWitness (leanIsaEnsemble prog κ)) (hκ : κ ≤ maxLogMem) :
    WellShapedData w.data :=
  (wellShapedData_iff _).mpr ⟨κ, hκ, by
    rw [memRows_data, List.size_toArray, List.length_map,
      memBlockRows_length w (lt_of_le_of_lt hκ (by decide))]⟩

/-- The memory block's index column is the row index: a fixed column. -/
theorem indexColumnsAreRowIndices (w : EnsembleWitness (leanIsaEnsemble prog κ)) (hκ : κ < 64) :
    IndexColumnsAreRowIndices w := by
  intro i hi
  have hlen := memBlockRows_length w hκ
  have h64 : i < 2 ^ 64 := lt_of_lt_of_le (hlen ▸ hi) (Nat.pow_le_pow_right (by norm_num) hκ.le)
  have hlt : (UInt64.ofNat i).toNat < 2 ^ κ := by
    rw [UInt64.toNat_ofNat_of_lt' h64]; exact hlen ▸ hi
  have hfix := (memMode_fixedAt hlt _).mp ((memBlock_fixed w).2 i hi)
  rw [memRowAt_eq, hfix, UInt64.toNat_ofNat_of_lt' h64]

theorem bytecodeBlockRows_length (w : EnsembleWitness (leanIsaEnsemble prog κ)) :
    (bytecodeBlockRows w).length = 2 ^ prog.logSize := by
  rw [(bytecodeBlock_fixed w).1, UInt64.toNat_ofNat_of_lt'
    (Nat.pow_lt_pow_right (a := 2) (by norm_num)
      (lt_of_le_of_lt prog.logSize_le (show maxLogBytecode < 64 by decide)))]

/-- The bytecode block's rows are the program's: its counter and entry columns are fixed. -/
theorem bytecodeRowsAreTheProgram (w : EnsembleWitness (leanIsaEnsemble prog κ)) :
    BytecodeRowsAreTheProgram prog w := by
  have hlen := bytecodeBlockRows_length w
  have h64 : 2 ^ prog.logSize ≤ 2 ^ 64 :=
    Nat.pow_le_pow_right (by norm_num) (le_trans prog.logSize_le (by decide))
  refine ⟨fun i ↦ (fromElements (Air.Flat.rowPrefix (size BytecodeRow)
      ((bytecodeBlockRows w)[(i : ℕ)]'(by rw [hlen]; exact i.isLt))) : BytecodeRow K).cntFin,
    List.ext_getElem (by rw [List.length_ofFn]; exact hlen) fun k hk hk' ↦ ?_⟩
  have hk2 : k < 2 ^ prog.logSize := hlen ▸ hk
  have hnat : (UInt64.ofNat k).toNat = k := UInt64.toNat_ofNat_of_lt' (lt_of_lt_of_le hk2 h64)
  have hfix := (bytecodeMode_fixedAt prog (i := UInt64.ofNat k) (by rw [hnat]; exact hk2) _).mp
    ((bytecodeBlock_fixed w).2 k hk)
  have hw : (bytecodeBlockRows w)[k].size = size BytecodeRow := by
    rw [(tableAt w 7).uniform_width _ (List.getElem_mem hk), tableAt_component]; rfl
  rw [List.getElem_ofFn]
  conv_lhs => rw [← toElements_rowPrefix hw, hfix]
  congr 3
  exact Fin.ext hnat

theorem memRowAt_m (w : EnsembleWitness (leanIsaEnsemble prog κ)) (row : Array K) :
    (memRowAt w row).m = Air.Flat.rowPrefix 2 row := by
  rw [memRowAt_eq]
  ext j hj
  interval_cases j <;> simp [Air.Flat.rowPrefix, explicit_provable_type, circuit_norm]

/-- The memory block's rows are the image the data names: the image is derived from them. -/
theorem seedRowsAreTheImage (w : EnsembleWitness (leanIsaEnsemble prog κ)) (hκ : κ ≤ maxLogMem) :
    SeedRowsAreTheImage w := by
  have hfst := imageOf_fst w hκ
  have hlen := memBlockRows_length w (lt_of_le_of_lt hκ (by decide))
  have hws := wellShaped w hκ
  have hlt : ∀ i : Fin (2 ^ (imageOf w.data).1), (i : ℕ) < (memBlockRows w).length := fun i ↦ by
    rw [hlen]; exact lt_of_lt_of_eq i.isLt (congrArg (2 ^ ·) hfst)
  refine ⟨fun i ↦ (memRowAt w ((memBlockRows w)[(i : ℕ)]'(hlt i))).idx,
    fun i ↦ (memRowAt w ((memBlockRows w)[(i : ℕ)]'(hlt i))).cntFin,
    List.ext_getElem (by rw [List.length_ofFn, hlen, hfst]) fun k hk hk' ↦ ?_⟩
  have hw : (memBlockRows w)[k].size = size MemRow := by
    rw [(tableAt w 6).uniform_width _ (List.getElem_mem hk), tableAt_component]; rfl
  rw [List.getElem_ofFn]
  conv_lhs => rw [← toElements_rowPrefix hw, ← memRowAt_eq w]
  have himg := imageOf_apply hws ⟨k, by simpa using hk'⟩
    (v := Air.Flat.rowPrefix 2 (memBlockRows w)[k]) (by simp [memRows_data])
  rw [himg]
  have hm := memRowAt_m w (memBlockRows w)[k]
  simp only []
  generalize memRowAt w (memBlockRows w)[k] = r at hm ⊢
  obtain ⟨m, idx, c⟩ := r
  subst hm
  rfl
namespace Caps

variable {w : EnsembleWitness (leanIsaEnsemble prog κ)}

/-- Under the caps, the image the data names has the announced size. -/
theorem imageOf_fst_eq (h : Caps w) : (imageOf w.data).1 = κ :=
  imageOf_fst w h.logMem_le_maxLogMem

/-- `MIN_LOG_MEM ≤ log_mem`, on the image. -/
theorem minLogMem_le (h : Caps w) : minLogMem ≤ (imageOf w.data).1 :=
  h.imageOf_fst_eq.symm ▸ h.minLogMem_le_logMem

/-- `log_mem ≤ MAX_LOG_MEM`, on the image. -/
theorem le_maxLogMem (h : Caps w) : (imageOf w.data).1 ≤ maxLogMem :=
  h.imageOf_fst_eq.symm ▸ h.logMem_le_maxLogMem

/-- Under the caps, the derived data is well shaped. -/
theorem well_shaped (h : Caps w) : WellShapedData w.data :=
  wellShaped w h.logMem_le_maxLogMem

end Caps

namespace SatisfiedBy

variable {input : PublicInput} {w : EnsembleWitness (leanIsaEnsemble prog κ)}

/-- The memory block's index column is the row index (§6.5). -/
theorem index_columns (h : SatisfiedBy prog input w) : IndexColumnsAreRowIndices w :=
  indexColumnsAreRowIndices w (lt_of_le_of_lt h.caps.logMem_le_maxLogMem (by decide))

/-- The memory block's rows are the image (§6.2). -/
theorem seed_rows (h : SatisfiedBy prog input w) : SeedRowsAreTheImage w :=
  seedRowsAreTheImage w h.caps.logMem_le_maxLogMem

/-- The bytecode block's rows are the program's (§8.6). -/
theorem bytecode_rows (_ : SatisfiedBy prog input w) : BytecodeRowsAreTheProgram prog w :=
  bytecodeRowsAreTheProgram w

end SatisfiedBy

/-! ## Bus soundness, the interface

The three bus-soundness statements, as first specified; they are proved in
`LeanVM.Arithmetization.Soundness` (`Soundness/MemChannel.lean`, `BytecodeChannel.lean`,
`StateWalk.lean`), with no condition on the program. Channels are identified by name
and a pulled message is read as its typed form, as the module does (`messagesOn`, `memRowAt`):

```lean
/-- Specification Lemma 6.3, Thm. 6.4, Cor. 6.5: with nonzero counts and fewer than `2^64 - 1`
reads, balance of the memory pair makes every memory pull of multiplicity `1` (every pull but a
`KECCAK` gated output cell at flag `0`, which cancels) a correct read. -/
theorem mem_channel_sound (h : SatisfiedBy prog input w) :
    ∀ i ∈ w.interactions, i.channel.name = MemPull.name → i.mult = 1 →
      ∀ m : MemMsg K, i.msg = (toElements m).toArray → MemPull.Guarantees m w.data

/-- The same for the bytecode pair, in the strong form: every pulled entry is the public
program's at the pulled counter (from `SatisfiedBy.bytecode_rows`), which implies the
pull's guarantee, that it decodes, and is what `constraintSoundness` joins to `execute` by
`execute_of_step`. -/
theorem bytecode_channel_sound (h : SatisfiedBy prog input w) :
    ∀ i ∈ w.interactions, i.channel.name = BytecodePull.name →
      ∀ m : BytecodeMsg K, i.msg = (toElements m).toArray →
        ∃ k : Fin (2 ^ prog.logSize), m.pc = gpow k ∧ #v[m.opcode] ++ m.op = entry (prog.code k)

/-- Specification Prop. 6.1: a balanced state channel over rows that are steps contains a run
from `(1, 1)` to `(g^(N_prog - 1), 1)`, cut at its first visit of the final state; the remaining
rows are closed walks. -/
theorem exists_run_of_balanced (h : SatisfiedBy prog input w) :
    ∃ n, run prog (imageOf w.data).2 n Regs.initial = some (Regs.final prog)
```

The read bound `mem_channel_sound` needs is derived from `Caps` (`≤ 27 · 6 · 2^32`), never
assumed; there is no hypothesis on the program.
-/

end LeanVM.Arithmetization
