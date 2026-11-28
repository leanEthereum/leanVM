module

public import Statement.Verifier.Whir
public import Statement.Verifier.Keccak
public import Statement.Verifier.RingSwitch
public import Statement.Verifier.Link

/-!
# The leanVM verifier (`lib.rs`; `layout.rs`; `transcript.rs`)

`leanVmVerifierProgram bytecode publicInput` is `verify_execution` in the verifier language, one
`VerifierProgram` function per numbered step of the Rust's `walk` (the steps of `verifyExecution`).
The program returns `true` where the Rust returns `Ok`; `Transcript::finish`, the check that the
proof is consumed, is `runProof`'s.

**The seed.** The sponge starts at Keccak-f of `IV ‖ public_input ‖ 0^17`, `IV` the Keccak-256 hash
of `TAG ‖ bytecode`, the tag `"leanvm-v1"` naming the proof system's version and the bytecode as its
little-endian words. The seed's input has the capacity lanes zero, Keccak-256's initial state, and
nothing separates its domain from a Keccak-256 block: in the random-permutation model the
transcript's duplex calls and Keccak-256's sponge calls query the one permutation from states of the
same kind. This is harmless for the end statements, which are proved for exactly this experiment.
-/

@[expose] public section

namespace LeanVM.Protocol.Verifier

open LeanVM.Parameters
open LeanVM.Semantics
open LeanVM.Protocol.Compile
open LeanVM.Protocol.KeccakHash

/-- Step 1, the announced sizes, read and checked, and the layout they give (`walk`, `lib.rs`): the
layout and the WHIR rate exponent. -/
def readAnnouncedSizes (bytecode : List K) : VerifierProgram (Layout × ℕ) := do
  let announced ← VerifierProgram.readScalars (2 + nTables)
  VerifierProgram.require (announced.all fun value ↦ value.limb 1 = 0)
  let logMemory := kToNat ((announced.headD 0).limb 0)
  let tableRows := ((announced.drop 1).take nTables).map fun value ↦ kToNat (value.limb 0)
  let logInverseRate := kToNat ((announced.getLastD 0).limb 0)
  VerifierProgram.require (1 ≤ logInverseRate ∧ logInverseRate ≤ 4)
  let layout ← liftOption (buildLayout bytecode logMemory tableRows)
  VerifierProgram.require (Whir.minLogStack ≤ layout.stackLog ∧ layout.stackLog ≤ Whir.maxLogStack)
  return (layout, logInverseRate)

/-- `verify_stacked_opening(transcript, root, stack_log, log_inv_rate, claims, batching)`
(`lib.rs`): at most `maxStackedClaims` claims (`StackedClaims`), batched with the powers of the
ring switch's batching challenge into one WHIR opening of the stack, commitment `0`: the powers
weigh the values into the target and the weights into the basis WHIR evaluates at its terminal
point. -/
def verifyStackedOpening (stackLog logInvRate : ℕ) (claims : List StackClaim) (batching : E) :
    VerifierProgram Unit := do
  VerifierProgram.require (claims.length ≤ maxStackedClaims)
  let scales := powers batching claims.length
  verifyWhir stackLog logInvRate (dot scales (claims.map (·.2)))
    fun point ↦ dot scales (claims.map fun c ↦ c.1 point)

/-- `ColumnClaim::on_stack(layout)` (`lib.rs`): the claim's weight on the stack, `eq` of the
column's stack point, and its value; `none` for a column nothing commits, whose claim never reaches
the stack. -/
def ColumnClaim.onStack (c : ColumnClaim) (layout : Layout) : Option StackClaim :=
  (layout.placements.getD c.column none).map fun placement ↦
    let point := placement.stackPoint c.point layout.stackLog
    (fun x ↦ eqEval point x, c.value)

/-- Step 3's column claims (`walk`, `lib.rs`): each table's non-pointer columns at its row point,
on the global columns from the table's base (`GLOBAL_COLUMN_BASES`: the global columns, then each
table's columns in opcode order). -/
def linkColumnClaims (link : LinkEnd) : List ColumnClaim :=
  (globalColumnBases.zip link.columns).flatMap fun (base, point, values) ↦
    values.map fun (column, value) ↦ ⟨base + column, point, value⟩

/-- Step 4, binding the public input (`walk`, `lib.rs`): a challenge, with no grind (a line has
error `1/|E|`), and claims on the two memory columns at `(challenge, 0, …, 0)` over the memory's
variables, each limb's claim the line through that limb of the public input's two halves,
evaluated at the challenge by the verifier itself. The prover sends nothing. -/
def bindPublicInput (layout : Layout) (publicInput : Digest) :
    VerifierProgram (List ColumnClaim) := do
  let publicChallenge ← VerifierProgram.sampleChallenge
  let halves := digestHalves publicInput
  let memory ← liftOption (layout.placements.getD memory0 none)
  let publicPoint := publicChallenge :: List.replicate (memory.variableCount - 1) 0
  let publicLimbs := ([0, 1] : List (Fin 2)).map fun limb ↦
    multilinearEval [ofK (halves.1.limb limb), ofK (halves.2.limb limb)] [publicChallenge]
  return List.zipWith (fun column value ↦ ⟨column, publicPoint, value⟩) [memory0, memory1]
    publicLimbs

/-- Step 5, `KECCAK`'s validity (`walk`, `lib.rs`): the `KECCAK` table's row point from the link,
and its output lanes' values there (local columns `KECCAK_OUT ..< KECCAK_OUT + STATE_LANES`, never
pointers, so the link sent each) are the Keccak reduction's claim on the permutation's output. The
reduction's claim on `q_keccak`'s committed outputs, and the point and slices it leaves for ring
switching. -/
def keccakValidity (layout : Layout) (link : LinkEnd) :
    VerifierProgram (List ColumnClaim × List E × List E) := do
  let (point, values) := link.columns.getD opKeccak ([], [])
  let lanes ← liftOption ((List.range keccakStateLanes).mapM fun lane ↦
    (values.find? fun value ↦ value.1 = keccakOut + lane).map (·.2))
  verifyKeccak (layout.tableLogHeights.getD opKeccak 0) point lanes

/-- Step 6's first ring claim (`walk`, `lib.rs`): the Keccak reduction's input slices on
`q_keccak`, one piece, the whole column at the reduction's point. -/
def keccakRingClaim (qkeccakPlacement : Placement) (point slices : List E) : RingClaim :=
  ⟨[⟨some qkeccakPlacement, point, 1⟩], slices⟩

/-- Step 6's memory term (`walk`, `lib.rs`): the link's claim on the memory at its low point `r`,
`Σ_limb scale_limb · memory_limb(r)`, as the weight `Σ scale · eq(stack point, ·)` and the value. -/
def memoryTermClaim (layout : Layout) (link : LinkEnd) : VerifierProgram StackClaim := do
  let memory0Placement ← liftOption (layout.placements.getD memory0 none)
  let memory1Placement ← liftOption (layout.placements.getD memory1 none)
  let memoryPoints := [(memory0Placement.stackPoint link.memoryPoint layout.stackLog,
      link.memoryScales.1),
    (memory1Placement.stackPoint link.memoryPoint layout.stackLog, link.memoryScales.2)]
  return (fun x ↦ sumE (memoryPoints.map fun (point, scale) ↦ scale * eqEval point x),
    link.memoryValue)

/-- `verify_execution(bytecode, public_input, proof)` without its `finish` (`walk`, `lib.rs`), the
program's split at the link's point given by `bytecodeSplit` (`verifyLink`). The stacked opening's claims: the merged ring claim (the Keccak reduction's input
slices, then the link's pointer slices) at `λ^0`, then the memory term, the column claims (the
link's, the public input's, the Keccak reduction's on `q_keccak`) with a placement, and the
out-of-domain sample. -/
def verifyExecution (bytecodeSplit : List K → List E → List (ℕ × ℕ) → VerifierProgram Split)
    (bytecode : List K) (publicInput : Digest) : VerifierProgram Unit := do
  -- 1] memory log-size, table row counts, and the WHIR rate
  let (layout, logInverseRate) ← readAnnouncedSizes bytecode
  -- 2] the stack's commitment, and its out-of-domain sample
  commitStack layout.stackLog logInverseRate
  let ood ← readOod layout.stackLog
  -- 3] the links: two chained sum-checks, over the index, then the rows and the pointer columns
  let link ← verifyLink bytecodeSplit layout
  let claims := linkColumnClaims link
  -- 4] binding the public input
  let publicClaims ← bindPublicInput layout publicInput
  let claims := claims ++ publicClaims
  -- 5] KECCAK validity, by GKR over the rounds, on the link's KECCAK columns
  let (outputs, keccakPoint, keccakSlices) ← keccakValidity layout link
  let claims := claims ++ outputs
  -- 6] ring switching: the Keccak reduction's input slices, then the pointer columns' slices
  let qkeccakPlacement ← liftOption (layout.placements.getD qkeccak none)
  let (ring, batching) ←
    ringSwitch [keccakRingClaim qkeccakPlacement keccakPoint keccakSlices, link.ring]
  let memoryTerm ← memoryTermClaim layout link
  -- 7] one opening of the stack for every claim with a placement
  verifyStackedOpening layout.stackLog logInverseRate
    (ring :: memoryTerm :: claims.filterMap (·.onStack layout) ++ [ood]) batching

/-! ### The program's split -/

/-- The deployed verifier computes the program's split at the point (`Bytecode::split`,
`bytecode.rs`, at the `(opcode, slot)` pairs read times `pc`, `pc_slots`, `link.rs`): it rejects a
point of `64` coordinates or more, or not one per instruction bit (`MultilinearSize`). -/
def computedSplit (bytecode : List K) (point : List E) (pc : List (ℕ × ℕ)) :
    VerifierProgram Split := do
  VerifierProgram.require (point.length < 64 ∧ bytecode.length >>> bytecodeSlotBits = 2 ^ point.length)
  return splitAt bytecode point pc

/-- A claim on the program split by opcode, for a verifier that does not evaluate it: a point and
a value (`DeferredBytecodeClaim`, `crates/aggregation/src/deferred.rs`). When it holds is
`LeanVmGuestBatching.lean`'s (`BytecodeClaim.Holds`, on `split_table`). -/
structure BytecodeClaim where
  /-- The point: the instructions' coordinates, then the split columns'. -/
  bytecodePoint : List E
  /-- The value claimed there. -/
  bytecodeValue : E

/-- The claim a child's verification raises (`FreshClaim`, `crates/aggregation/src/deferred.rs`):
the split columns' values at its link point's instruction coordinates. -/
structure FreshClaim where
  /-- `point`: the link point's instruction coordinates. -/
  point : List E
  /-- `values`: the split columns' values there. -/
  values : List E
  deriving Inhabited

/-- A column of the split program over the instructions `k` (`Column`,
`crates/aggregation/src/split.rs`): `[op_k = op]` (`count`), `[op_k = op]·BC_slot(k)` (`slot`), or
`[op_k = op]·g^k·BC_slot(k)` (`pc`). -/
inductive SplitColumn where
  /-- `Column::Count`. -/
  | count (op : ℕ)
  /-- `Column::Slot`. -/
  | slot (op slot : ℕ)
  /-- `Column::Pc`. -/
  | pc (op slot : ℕ)
  deriving DecidableEq, Inhabited

/-- The split program's columns, in `split_terms`' order (`split.rs`): each opcode's count, then,
table by table, the columns its links name, first seen first: its program link's operand slots,
then per access its frame slot and its reads (a word read names none). -/
def splitColumns (tables : List Table) : List SplitColumn :=
  let note := fun (columns : List SplitColumn) (c : SplitColumn) ↦
    if c ∈ columns then columns else columns ++ [c]
  tables.zipIdx.foldl (fun columns (table, t) ↦
    let links := table.links
    let columns := links.bytecodeLink.operands.foldl
      (fun columns (slots, _) ↦ slots.foldl (fun columns s ↦ note columns (.slot t s)) columns)
      columns
    links.memory.foldl (fun columns access ↦
      let columns := match access.frame with
        | some (s, _) => note columns (.slot t s)
        | none => columns
      access.reads.foldl (fun columns read ↦
        match read with
        | .word _ _ => columns
        | .slot slot _ => note columns (.slot t slot)
        | .frame slot _ => note columns (.slot t slot)
        | .pc slot _ => note columns (.pc t slot)) columns) columns)
    ((List.range tables.length).map .count)

/-- The `Split` whose split columns take `values` (`split_values`, `split.rs`, inverted), every
entry no column names zero: what the program side of the link reads of a child's fresh claim, as
the guest weighs the hinted columns (`verify_sub`'s `split_values`, `guests/lean_ethereum.py`). -/
def Split.ofColumns (tables : List Table) (values : List E) : Split :=
  let columns := splitColumns tables
  let valueOf := fun (c : SplitColumn) ↦ ((columns.idxOf? c).bind (values[·]?)).getD 0
  { count := (List.range nTables).map fun op ↦ valueOf (.count op)
    slots := (List.range nTables).map fun op ↦ (List.range (2 ^ bytecodeSlotBits)).map fun s ↦
      valueOf (.slot op s)
    pc := (List.range nTables).map fun op ↦ (List.range (2 ^ bytecodeSlotBits)).map fun s ↦
      valueOf (.pc op s) }

/-- The deferring verifier's split (`verify_sub`, `guests/lean_ethereum.py`; `FreshClaim`,
`crates/aggregation/src/deferred.rs`): the program side reads the child's fresh claim, one value
per split column, and the link's point over the instructions, `r[..log_bytecode]`, must be the
claim's point, which the child exports. The split columns are `split_terms`' over `tables()`, as
`split_values` takes them; neither the bytecode nor the pairs read times `pc` are read (the
columns name exactly those pairs, `pcSlots tables`). -/
def freshSplit (fresh : FreshClaim) (_bytecode : List K) (point : List E) (_pc : List (ℕ × ℕ)) :
    VerifierProgram Split := do
  VerifierProgram.require (point = fresh.point ∧ fresh.values.length = (splitColumns tables).length)
  return Split.ofColumns tables fresh.values

/-! ### The programs -/

/-- **The leanVM verifier program**: `verify_execution` in the verifier language, accepting
where the Rust returns `Ok`. -/
def leanVmVerifierProgram (bytecode : List K) (publicInput : Digest) : VerifierProgram Bool := do
  verifyExecution computedSplit bytecode publicInput
  return true

/-- The verifier program with the program's split held to a child's fresh claim, as an aggregate
runs it on a child's proof (`verify_sub`, `guests/lean_ethereum.py`). -/
def deferringVerifierProgram (fresh : FreshClaim) (bytecode : List K) (publicInput : Digest) :
    VerifierProgram Bool := do
  verifyExecution (freshSplit fresh) bytecode publicInput
  return true

/-! ### The seed and the compiled verifier -/

/-- `TAG`, the proof system's version (`layout.rs`), as
bytes. -/
def versionTag : Bytes := "leanvm-v1".toUTF8.toList

section Hash

variable {m : Type → Type} [Monad m] (π : KeccakState → m KeccakState)

/-- The IV over the permutation `π`: Keccak-256 over `π` of the tag, then the bytecode as its
little-endian words (`Bytecode::new`, `bytecode.rs`). -/
def fiatShamirIvWith (bytecode : List K) : m Digest :=
  keccak256With π (versionTag ++ bytecode.flatMap K.toBytes)

/-- The sponge's initial state over the permutation `π`: `π` of the IV's and the public input's
words, the other lanes zero (`Sponge::new`, `transcript.rs`). -/
def spongeSeedWith (bytecode : List K) (publicInput : Digest) : m KeccakState := do
  let fiatShamirIv ← fiatShamirIvWith π bytecode
  π (seedInput fiatShamirIv publicInput)

/-- The compiled verifier over the permutation `π`: the program run on the proof from the seed. -/
def verifyWith (bytecode : List K) (publicInput : Digest) (proof : Proof) : m Bool := do
  let seed ← spongeSeedWith π bytecode publicInput
  runProof π (leanVmVerifierProgram bytecode publicInput) seed proof

/-- **The deferring verifier** over the permutation `π`, as an aggregate runs it on a child's proof
(`verify_sub`): the IV is given rather than hashed from the bytecode, and the program's split at the
link's point is held to the child's fresh claim `fresh` instead of computed (`freshSplit`). -/
def verifyDeferredWith (bytecode : List K) (iv publicInput : Digest) (fresh : FreshClaim)
    (proof : Proof) : m Bool := do
  let seed ← π (seedInput iv publicInput)
  runProof π (deferringVerifierProgram fresh bytecode publicInput) seed proof

end Hash

/-- The deployed IV, over Keccak-f[1600]. -/
def fiatShamirIv (bytecode : List K) : Digest :=
  Id.run (fiatShamirIvWith (m := Id) keccakF1600 bytecode)

/-- The deployed deferring verifier, over Keccak-f[1600]. -/
def verifyDeferred (bytecode : List K) (iv publicInput : Digest) (fresh : FreshClaim)
    (proof : Proof) : Bool :=
  Id.run (verifyDeferredWith (m := Id) keccakF1600 bytecode iv publicInput fresh proof)

end LeanVM.Protocol.Verifier

/-! ## The sizes a proof announces

The verifier's first step reads the announced sizes and nothing else (`readAnnouncedSizes`): its
reads only absorb, so no hash or permutation is consulted for a value, and running it with every
permutation answered by `default` gives the layout the proof announces. The extractor's budget
(`Statement/CostMachine.lean`) grows with the stack size it announces. -/

namespace LeanVM.Protocol.Compile

open LeanVM.Parameters

/-- A run with every permutation answered by `default`, for the steps that only read scalars: what
they read does not depend on the sponge. -/
def runPure {α : Type} (program : VerifierProgram α) (s : VerifierProgramState) : Option
    (α × VerifierProgramState) :=
  Id.run (run (m := Id) (fun _ ↦ default) program s)

end LeanVM.Protocol.Compile

namespace LeanVM.Protocol.Verifier

open LeanVM.Parameters LeanVM.Protocol.Compile

/-- The announced layout and rate exponent of a stream, read by the program's own
`readAnnouncedSizes` (reads only absorb: no hash or permutation is consulted for a value). -/
def announcedLayoutAndRate (bytecode : List K) (stream : List E) : Option (Layout × ℕ) :=
  (runPure (readAnnouncedSizes bytecode) ⟨⟨default, [], none⟩, stream, [], []⟩).map (·.1)

end LeanVM.Protocol.Verifier

end
