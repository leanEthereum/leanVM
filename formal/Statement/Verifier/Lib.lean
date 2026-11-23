module

public import Statement.Verifier.Bus
public import Statement.Verifier.Whir
public import Statement.Verifier.Keccak
public import Statement.Verifier.RingSwitch

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
open LeanVM.Semantics LeanVM.Protocol.KeccakHash

/-- The announced sizes, read and checked, and the layout they give
(`lib.rs`): the layout and the WHIR rate exponent. -/
def readAnnouncedSizes (bytecode : List K) : VerifierProgram (Layout × ℕ) := do
  let announced ← VerifierProgram.readScalars (2 + tables.length)
  VerifierProgram.require (announced.all fun value ↦ value.limb 1 = 0)
  let logMemory := kToNat ((announced.headD 0).limb 0)
  let tableRows := ((announced.drop 1).take tables.length).map fun value ↦ kToNat (value.limb 0)
  let logInverseRate := kToNat ((announced.getLastD 0).limb 0)
  VerifierProgram.require (1 ≤ logInverseRate ∧ logInverseRate ≤ 4)
  let layout ← liftOption (buildLayout bytecode logMemory tableRows)
  VerifierProgram.require (Whir.minLogStack ≤ layout.stackLog ∧ layout.stackLog ≤ Whir.maxLogStack)
  return (layout, logInverseRate)

/-- Step 4, the table sumcheck at the bus point (`lib.rs`): a grind for the batch's degree
in `xi`, its `n_constraints + N_TREES` powers less one, then `xi`; each table's point and
evaluations. -/
def tablePhase (layout : Layout) (bus : BusResult) : VerifierProgram (List (List E × List E)) := do
  let nConstraints := (tables.map Table.nConstraints).sum
  let nPowers := nConstraints + nTrees
  VerifierProgram.grindProofOfWork (grindingBits (nPowers - 1))
  let xi ← VerifierProgram.sampleChallenge
  let xiPowers := powers xi nPowers
  let constraintPowers := xiPowers.take nConstraints
  let formPowers := xiPowers.drop nConstraints
  let target := dot formPowers bus.totals
  tableSumcheck layout.tableLogHeights bus.forms constraintPowers formPowers bus.point target

/-- The tables' column claims (`lib.rs`): each table's evaluations at its point,
on the table's global columns. -/
def tableColumnClaims (evaluations : List (List E × List E)) : List ColumnClaim :=
  (globalColumnBases.zip evaluations).flatMap fun (base, point, values) ↦
    values.zipIdx.map fun (value, column) ↦ ⟨base + column, point, value⟩

/-- Step 5, binding the public input (`lib.rs`): a challenge, with no grind (a line has
error `1/|E|`), and claims on the two memory columns at `(challenge, 0, …, 0)`, each limb's claim
the line through that limb of the public input's two halves, evaluated at the challenge by the
verifier itself. The prover sends nothing. -/
def publicInputPhase (layout : Layout) (publicInput : Digest) : VerifierProgram
    (List ColumnClaim) := do
  let publicChallenge ← VerifierProgram.sampleChallenge
  let halves := digestHalves publicInput
  let publicLimbs := ([0, 1] : List (Fin 2)).map fun limb ↦
    multilinearEval [ofK (halves.1.limb limb), ofK (halves.2.limb limb)] [publicChallenge]
  let publicPoint := publicChallenge ::
    List.replicate ((layout.placement memory0).variableCount - 1) 0
  return List.zipWith (fun column value ↦ ⟨column, publicPoint, value⟩)
    [memory0, memory1] publicLimbs

/-- Step 6, `KECCAK`'s validity (`lib.rs`): the `KECCAK` table's point and its
output lanes' evaluations, `values[KECCAK_OUT..KECCAK_OUT + STATE_LANES]`, are the Keccak
reduction's claim on the permutation's output. The reduction's column claims, and the point and
slices of `q_keccak` it leaves for ring switching. -/
def keccakPhase (layout : Layout) (evaluations : List (List E × List E)) : VerifierProgram
    (List ColumnClaim × List E × List E) :=
  let (point, values) := evaluations.getD opKeccak ([], [])
  verifyKeccak (layout.tableLogHeights.getD opKeccak 0) point
    ((List.range 25).map fun lane ↦ values.getD (keccakOut + lane) 0)

/-- Step 7's ring-switching claim on the stack: supported on `q_keccak`'s region, its weight
carries the placement's selector (`lib.rs`). -/
def ringSwitchClaim (layout : Layout) (target : E) (weight : List E → E) : StackClaim :=
  let qkeccakPlacement := layout.placement qkeccak
  (fun x ↦ qkeccakPlacement.eqAbove x * weight (x.take qkeccakPlacement.variableCount), target)

/-- `verify_execution(bytecode, public_input, proof)` without its `finish` (`walk`,
`lib.rs`), the fixed polynomial's claimed value checked by `bytecodeValue`. The stacked
opening's claims are the ring-switched one, every column claim with a placement, then the stack
commitment's out-of-domain claim. -/
def verifyExecution (bytecodeValue : List K → List E → E → VerifierProgram Unit)
    (bytecode : List K) (publicInput : Digest) : VerifierProgram Unit := do
  -- 1] memory log-size, table row counts, and the WHIR rate
  let (layout, logInverseRate) ← readAnnouncedSizes bytecode
  -- 2] the stack's commitment, and its out-of-domain sample
  commitStack layout.stackLog logInverseRate
  let ood ← readOod layout.stackLog
  -- 3] the bus
  let bus ← verifyBusBalance bytecodeValue layout
  -- 4] the table sumcheck, and the tables' column claims
  let evaluations ← tablePhase layout bus
  let claims := bus.claims ++ tableColumnClaims evaluations
  -- 5] the public input
  let publicClaims ← publicInputPhase layout publicInput
  let claims := claims ++ publicClaims
  -- 6] KECCAK validity, by GKR over the rounds
  let (outputs, keccakPoint, keccakSlices) ← keccakPhase layout evaluations
  let claims := claims ++ outputs
  -- 7] ring switching, then one opening of the stack for every claim with a placement
  let (ringTarget, ringWeight) ← ringSwitch keccakPoint keccakSlices
  verifyStackedOpening layout.stackLog logInverseRate
    (ringSwitchClaim layout ringTarget ringWeight :: claims.filterMap (·.onStack layout) ++ [ood])

/-! ### The fixed polynomial's value -/

/-- The deployed verifier evaluates the fixed polynomial at the point and checks the claimed value
(`BytecodeValue`, `bus.rs`; `Bytecode::evaluate`, `crates/verifier/src/bytecode.rs`,
the same value by a sparse sum). -/
def computedBytecodeValue (words : List K) (point : List E) (value : E) : VerifierProgram Unit :=
  VerifierProgram.require (multilinearEval (words.map ofK) point = value)

/-- What a proof claims of the fixed polynomial, for a verifier that does not evaluate it: the
bytecode's value at its point, the walk's `bytecode_point` (`Summary`, `lib.rs`). -/
structure BytecodeClaim where
  bytecodePoint : List E
  bytecodeValue : E

/-- The claim `claim` in place of the evaluation: the point the proof's bytecode sumcheck leaves
and the value it claims there must be the claim's, so the run fails unless the proof defers exactly
`claim`. -/
def claimedBytecodeValue (claim : BytecodeClaim) (_ : List K) (point : List E) (value : E) :
    VerifierProgram Unit :=
  VerifierProgram.require (point = claim.bytecodePoint ∧ value = claim.bytecodeValue)

/-- The claim's value is the bytecode's multilinear extension at its point (the value only;
`DeferredBytecodeClaim.HoldsWithShape`, `LeanVmGuest.lean`, adds the shape and the
power-of-two length). -/
def BytecodeClaim.Holds (bytecode : List K) (claim : BytecodeClaim) : Prop :=
  multilinearEval (bytecode.map ofK) claim.bytecodePoint = claim.bytecodeValue

/-! ### The programs -/

/-- **The leanVM verifier program**: `verify_execution` in the verifier language, accepting
where the Rust returns `Ok`. -/
def leanVmVerifierProgram (bytecode : List K) (publicInput : Digest) : VerifierProgram Bool := do
  verifyExecution computedBytecodeValue bytecode publicInput
  return true

/-- The verifier program with the fixed polynomial's claimed point and value held to `claim`. -/
def deferringVerifierProgram (claim : BytecodeClaim) (bytecode : List K) (publicInput : Digest) :
    VerifierProgram Bool := do
  verifyExecution (claimedBytecodeValue claim) bytecode publicInput
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
(`verify_sub`): the IV is given rather than hashed from the bytecode, and the fixed polynomial's
point and value are held to `claim` instead of evaluated. Only the bytecode's length is read. -/
def verifyDeferredWith (bytecode : List K) (iv publicInput : Digest) (claim : BytecodeClaim)
    (proof : Proof) : m Bool := do
  let seed ← π (seedInput iv publicInput)
  runProof π (deferringVerifierProgram claim bytecode publicInput) seed proof

end Hash

/-- The deployed IV, over Keccak-f[1600]. -/
def fiatShamirIv (bytecode : List K) : Digest :=
  Id.run (fiatShamirIvWith (m := Id) keccakF1600 bytecode)

/-- The deployed deferring verifier, over Keccak-f[1600]. -/
def verifyDeferred (bytecode : List K) (iv publicInput : Digest) (claim : BytecodeClaim)
    (proof : Proof) : Bool :=
  Id.run (verifyDeferredWith (m := Id) keccakF1600 bytecode iv publicInput claim proof)

end LeanVM.Protocol.Verifier

/-! ## The sizes a proof announces

The verifier's first step reads the announced sizes and nothing else (`readAnnouncedSizes`): its
reads only absorb, so no hash or permutation is consulted for a value, and running it with every
permutation answered by `default` gives the layout the proof announces. The extractor's budget
(`Statement/LeanVmExtractor.lean`) grows with the stack size it announces. -/

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
