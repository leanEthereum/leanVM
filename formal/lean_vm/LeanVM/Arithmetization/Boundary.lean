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
public import Clean.Utils.Tactics.CircuitProofStart

@[expose] public section

/-!
# The boundary blocks

At leanVM pin `127510d14c98ade4e8a97646c44fa7f1ff5e752d` and Clean pin `42fe4b26`. The three
blocks are `crates/leanvm_core/src/cpu/layout.rs:351-394` (the "shared blocks" of `layout`),
matching specification §6.1 (`doc/leanvm/body/06-bus-interactions.tex:8`, the state boundary),
§6.2 "Flush rules" (`:44-46`, seed and finalize), §6.4 (the bytecode array), §6.5 (`:98`, the
index column), and §8.5 (`08-end-to-end-protocol.tex:74`: "three blocks per side belong to no
table"). The committed
columns are `MEM_LO, MEM_HI, MEM_TOP, MFCNT` and `BFCNT` (`layout.rs:13-17`); the bytecode entry
rides eight *public* columns (`bytecode_columns`, `layout.rs:228-289`, `Bytecode`'s `entry`); the
sentinel counter `g^(N_prog - 1)` is derived from the public program's length and written into the
state block as a constant (`layout.rs:334`, `final_pc`; `:356`, `Const(g_pow(final_pc))`).

**The three blocks.** Every row of an opcode table pulls its state and pushes its successor,
and reads its cells and its instruction through the counted lookup of §6.2. What closes the
three channel pairs are the boundary blocks: the *memory block* pushes each word of the image
once, as `(g^i, 1, mem[i])`, and pulls it back with its final count, `(g^i, g^(A[i]), mem[i])`;
the *bytecode block* does the same for each slot of the public program; the *verifier* pushes
the initial state `(1, 1)` and pulls the final state `(g^(N_prog - 1), 1)`. None has a
constraint: each is its two flushes.

**The rows.** `MemRow` is the memory block's row: the address `idx` (the index column of §6.5,
which the verifier computes and which is a column here until Clean PR #446), the finalize count
`cntFin`, and the word's three limbs `m`; `BytecodeRow` is the bytecode block's: the counter
`idx`, the finalize count, and the entry as the opcode and the seven operand slots, in the
order of `BytecodeMsg`. `PublicIO` is what the verifier reads off the public data:
the four lanes of the public input (§2, §8.2), and `PublicIO.ofInput input` is the public input
of a run, which `SatisfiedBy` requires of the witness. The verifier is a function of the public
program, `leanIsaVerifier prog`, and pulls `Expression.const prog.finalPc`: leanVM's
`layout(prog, …)` derives the counter from the program and writes it into the block as a
constant, so here it is a constant of the component, never a column and never a public
coordinate, and the statement's ensemble is `leanIsaEnsemble prog`.

**The specifications.** A block's `Spec` is what its pull guarantees (`Channels`): `MemSpec r
data` says the row is bound to the image the data names, `MemBindings (imageOf data).2 r`, the
cell at `idx` holding the row's word `E.ofLimbs m[0] m[1] m[2]`; `BytecodeDecodes r` says the
row's entry decodes to an instruction (`decode`), the program-free guarantee of the bytecode
pull, which reads no data. The program is not the block's to name: its rows are the public
program's entries because the verifier forms them from the program (§8.5, Bus 4;
`Coord::Public`), which the statement gives as the conjunct `BytecodeRowsAreTheProgram prog` of
`SatisfiedBy prog`, that the block's rows are `bytecodeRowOf prog i cntFin` for every slot `i`
with some finalize count. `BytecodeBindings prog r` is that conjunct's per-row reading, the
program fetching at `idx` an instruction the row's entry decodes to: proved of every
`bytecodeRowOf` row (`bytecodeRowOf_bindings`), derived for every seed row by `Soundness`, and
never the block's `Spec`, since the program is public and never prover data. The verifier's
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
the program as functions, never through `MemImage.read`. The verifier is complete for every
program and public input, and `verifier_push_eval` and `verifier_pull_eval` read its two
states as `Regs.initial` and `Regs.final prog`.

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
  state is `Regs.final prog` in every environment.
* `idx` is a column of the row here, not the verifier's index column: nothing in `main` ties
  row `i` to `g^i`. That is the statement's `IndexColumnsAreRowIndices`, and the two seed tables
  being the image and the program are its `SeedRowsAreTheImage` and `BytecodeRowsAreTheProgram`,
  all three removed by Clean PR #446.
* The bytecode block's `Spec` names no program: one read off the prover data is the prover's,
  and a parameter would be Clean PR #446's fixed columns done by hand on a component that has
  no constraint to hold them. The statement carries the program (`BytecodeRowsAreTheProgram`),
  and a row whose entry is not the program's at its counter is rejected there, never here (the
  tests reject it through `BytecodeBindings`).
* The bytecode entry carries all seven operand slots, spare slots as literal zeros, so that the
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

/-- A row of the memory block: the address `g^i` (the index column of §6.5), the finalize count
`g^(A[i])` (`MFCNT`), and the word's three limbs (`MEM_LO, MEM_HI, MEM_TOP`; `layout.rs:13-16`). -/
structure MemRow (F : Type) where
  /-- The address, `g^i` for row `i`. -/
  idx : F
  /-- The finalize count, `g^(A[i])` for an address read `A[i]` times. -/
  cntFin : F
  /-- The word at the address, as limbs. -/
  m : Vector F 3
  deriving ProvableStruct

/-- The row's binding to an image: the cell at its address holds its word. -/
structure MemBindings {κ : ℕ} (mem : MemImage κ) (r : MemRow K) : Prop where
  /-- The cell `idx` holds the row's word `m`. -/
  word_eq : mem.read r.idx = some (E.ofLimbs r.m[0] r.m[1] r.m[2])

/-- The memory block's `Spec`: the row is bound to the image the prover data names
(`imageOf`). -/
def MemSpec (r : MemRow K) (data : ProverData K) : Prop :=
  MemBindings (imageOf data).2 r

/-- The memory block (specification §6.2, seed and finalize; `layout.rs:358-381`): push
`(idx, 1, m)`, pull `(idx, cntFin, m)`. -/
def memTable : GeneralFormalCircuit K MemRow unit where
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
    obtain ⟨_, _, hm⟩ := h_input
    subst hm
    exact ⟨by simpa only [Vector.getElem_map] using h_holds⟩
  completeness := by
    circuit_proof_start [MemPull, MemPush]
    obtain ⟨_, _, hm⟩ := h_input
    subst hm
    simpa only [Vector.getElem_map] using h_assumptions.word_eq

/-- The seed row of word `i` of the image `mem`, with finalize count `cntFin`: the address `g^i`
and the word's limbs. -/
def memRowOf {κ : ℕ} (mem : MemImage κ) (i : Fin (2 ^ κ)) (cntFin : K) : MemRow K :=
  ⟨gpow i, cntFin, #v[(mem i).limb 0, (mem i).limb 1, (mem i).limb 2]⟩

/-- On an image within the address space `gLog?_spec` covers, `memRowOf` is bound, with any
finalize count. -/
theorem memRowOf_bindings {κ : ℕ} (hκ : κ < 64) (mem : MemImage κ) (i : Fin (2 ^ κ))
    (cntFin : K) : MemBindings mem (memRowOf mem i cntFin) :=
  ⟨by
    show mem.read (gpow i) = some (E.ofLimbs ((mem i).limb 0) ((mem i).limb 1) ((mem i).limb 2))
    rw [MemImage.read_gpow hκ, ofLimbs_limb]⟩

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
`g^(A[i])` (`BFCNT`, `layout.rs:17`), and the `entry` at that slot, the opcode and the
seven operand slots (the eight public columns of `bytecode_columns`, `layout.rs:228-289`). -/
structure BytecodeRow (F : Type) where
  /-- The counter, `g^i` for row `i`. -/
  idx : F
  /-- The finalize count, `g^(A[i])` for a slot executed `A[i]` times. -/
  cntFin : F
  /-- The opcode, coordinate 3 of the tuple. -/
  opcode : F
  /-- The seven operand slots. -/
  op : Vector F 7
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
structure BytecodeBindings (prog : Program) (r : BytecodeRow K) : Prop where
  /-- The program fetches at `idx` the instruction the row's entry decodes to. -/
  entry_eq : ∃ ins, prog.fetch r.idx = some ins ∧ decode (#v[r.opcode] ++ r.op) = some ins

/-- The bytecode block (specification §6.2 and §6.4, seed and finalize; `layout.rs:382-394`):
push `(idx, 1, opcode, op)`, pull `(idx, cntFin, opcode, op)`. Program-free: the entry columns
are the program's by the statement's conjunct, not by anything here. -/
def bytecodeTable : GeneralFormalCircuit K BytecodeRow unit where
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

/-- An eight-coordinate entry is its opcode followed by its seven operand slots. -/
private theorem cons_append_ops (e : Vector K 8) :
    #v[e[0]] ++ #v[e[1], e[2], e[3], e[4], e[5], e[6], e[7]] = e := by
  ext j hj
  interval_cases j <;> rfl

/-- The seed row of slot `i` of the program `prog`, with finalize count `cntFin`: the counter
`g^i` and the slot's `entry` as the opcode and the seven operand slots. -/
def bytecodeRowOf (prog : Program) (i : Fin (2 ^ prog.logSize)) (cntFin : K) : BytecodeRow K :=
  let e := entry (prog.code i)
  ⟨gpow i, cntFin, e[0], #v[e[1], e[2], e[3], e[4], e[5], e[6], e[7]]⟩

/-- `bytecodeRowOf` is bound to its program, with any finalize count. -/
theorem bytecodeRowOf_bindings (prog : Program) (i : Fin (2 ^ prog.logSize)) (cntFin : K) :
    BytecodeBindings prog (bytecodeRowOf prog i cntFin) :=
  ⟨_, prog.fetch_gpow i, by
    show decode (#v[(entry (prog.code i))[0]] ++ #v[(entry (prog.code i))[1],
      (entry (prog.code i))[2], (entry (prog.code i))[3], (entry (prog.code i))[4],
      (entry (prog.code i))[5], (entry (prog.code i))[6], (entry (prog.code i))[7]]) = some _
    rw [cons_append_ops]
    exact decode_entry _⟩

/-- `bytecodeRowOf` decodes, with any finalize count: the block's `Spec` of every row the
builder writes. -/
theorem bytecodeRowOf_decodes (prog : Program) (i : Fin (2 ^ prog.logSize)) (cntFin : K) :
    BytecodeDecodes (bytecodeRowOf prog i cntFin) :=
  ⟨(bytecodeRowOf_bindings prog i cntFin).entry_eq.imp fun _ h ↦ h.2⟩

/-- Every slot of a program has a satisfying seed row, from the program alone and over any
data: the constraints of `main` hold of `bytecodeRowOf` in the row environment. -/
theorem bytecode_entry_complete {data : ProverData K} (prog : Program)
    (i : Fin (2 ^ prog.logSize)) (cntFin : K) :
    ConstraintsHold.Completeness (rowEnv data)
      ((bytecodeTable.main (const (bytecodeRowOf prog i cntFin))).operations 0) :=
  (bytecodeTable.completeness 0 (rowEnv data) (const _)
    (by simp only [circuit_norm, bytecodeTable, -BitVec.reduceNeg]) _
    ProvableType.eval_const_prover (bytecodeRowOf_decodes _ _ _)).1

/-! ## The verifier -/

/-- The verifier's state boundary for the public program `prog` (specification §6.1;
`layout.rs:351-357`): push the initial state `(1, 1)`, pull the final state
`(g^(N_prog - 1), 1)`, the counter a constant of the program as `Const(g_pow(final_pc))` is
(`layout.rs:334`, `:356`). `Spec` is `True`: the state pull carries no guarantee, and the
run the boundary closes is `exists_run_of_balanced`. -/
def leanIsaVerifier (prog : Program) : GeneralFormalCircuit K PublicIO unit where
  main _ := do
    StatePush.push ⟨1, 1⟩
    StatePull.pull ⟨Expression.const prog.finalPc, 1⟩
  -- The push channel: its requirement is vacuous.
  channelsWithRequirements := [StatePush.toRaw]
  requirementsChannelsLawful input offset := by
    simp only [circuit_norm, -BitVec.reduceNeg]
    tauto
  Spec _ _ _ := True
  -- No constraint, no guarantee, no requirement: both statements are closed by their openers.
  soundness := by
    circuit_proof_start [StatePull, StatePush]
  completeness := by
    circuit_proof_start [StatePull, StatePush]

/-! ## Load-bearing lemmas -/

/-- The state the verifier pushes is `Regs.initial`, in every environment. -/
theorem verifier_push_eval (env : Environment K) :
    eval env (⟨1, 1⟩ : Regs (Expression K)) = Regs.initial := by
  simp only [circuit_norm]; rfl

/-- The state the verifier pulls is `Regs.final prog`, in every environment: the
counter is a constant of the component, not a column or a public coordinate. -/
theorem verifier_pull_eval (prog : Program) (env : Environment K) :
    eval env (⟨Expression.const prog.finalPc, 1⟩ : Regs (Expression K)) = Regs.final prog := by
  simp only [circuit_norm]; rfl

end LeanVM.Arithmetization
