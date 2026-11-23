/-
  LeanVM.Protocol.Verifier.Defers

  A proof the leanVM verifier accepts is accepted by the deferring verifier, under the IV the
  verifier hashes, with exactly one claim on the bytecode, and that claim is true.
-/

module

public import LeanVM.Protocol.Verifier.DeferredShape
public import Statement.LeanVm
import LeanVM.Protocol.WithHashBridge

/-!
# The claim an accepted proof defers

The verifier reads the fixed polynomial once, at the bus's bytecode point (`verifyBusBalance`).
`verifyExecution ev` is a prefix (`prefixProg`: the sizes, the stack's root and its out-of-domain
sample, the bus up to its bytecode sumcheck), the evaluation `ev` at the point and value the prefix
returns, and a suffix (`execSplit`). So:

* an accepted run with the computed value is the run with the claim of that value at that point
  (`run_claimed_of_computed`), a claim true of the bytecode (`BytecodeClaim.Holds`);
* the claimed evaluation fails off the claim's point and value, so a run with a claim that returns
  has the prefix's point and value as its claim, whatever the claim (`claim_of_run_claimed`): a
  proof is accepted with at most one claim (`claim_unique`).

`verifyDeferredWithHash_of_verifyWithHash` puts them together at any hash and permutation function
in `Id`, `LeanVM.verifyDeferredWith_of_leanVmVerifier` states it for the statement's verifier over
any permutation function in `Id`, and `LeanVM.verifyDeferred_of_leanVmVerifier` at the deployed
Keccak-f[1600]. The converse, under a true claim, is `verify_of_verifyDeferred`.
-/

namespace LeanVM.Protocol.Verifier.Defers

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Compile
open LeanVM.Protocol.Verifier LeanVM.Protocol.KeccakHash

@[expose] public section

/-! ## The verifier, split at its evaluation -/

/-- What the prefix has read when the verifier evaluates the bytecode. -/
structure Pre where
  layout : Layout
  rate : ℕ
  ood : StackClaim
  weights : List E
  beta : E
  point : List E
  treeValues : List E
  memory : List E
  memoryFinal : E
  bytecodeFinal : E
  share : E
  bytecodePoint : List E
  value : E

/-- The verifier up to its evaluation of the bytecode: the bytecode sumcheck's point and value. -/
def prefixProg (bytecode : List K) : VerifierProgram Pre := do
  let (layout, rate) ← readAnnouncedSizes bytecode
  commitStack layout.stackLog rate
  let ood ← readOod layout.stackLog
  let pushLayout := busLayout [0, layout.logMemory, layout.logBytecode] layout.push
  VerifierProgram.require (pushLayout.depth < 64)
  VerifierProgram.grindProofOfWork (busGrindingBits pushLayout.depth)
  let weights ← VerifierProgram.sampleChallenges (2 ^ busBits)
  let beta ← VerifierProgram.sampleChallenge
  let (countRoot, point, treeValues) ← verifyGkrGrandProducts pushLayout.depth
  VerifierProgram.require (countRoot ≠ 0)
  let memory ← VerifierProgram.readScalars 2
  let memoryFinal ← VerifierProgram.readScalar
  let bytecodeFinal ← VerifierProgram.readScalar
  let (share, bytecodePoint, value) ← bytecodeShare weights (point.take layout.logBytecode)
  return ⟨layout, rate, ood, weights, beta, point, treeValues, memory, memoryFinal, bytecodeFinal,
    share, bytecodePoint, value⟩

/-- The bus's result from what the prefix read. -/
def busOf (y : Pre) : BusResult :=
  let layout := y.layout
  let frameworkLogRows := [0, layout.logMemory, layout.logBytecode]
  let pushLayout := busLayout frameworkLogRows layout.push
  let pullLayout := busLayout frameworkLogRows layout.pull
  let countLayout := busLayout [] layout.count
  let memoryLow := y.point.take layout.logMemory
  let bytecodeLow := y.point.take layout.logBytecode
  let claims : List ColumnClaim :=
    (List.zipWith (fun column value ↦ ⟨column, memoryLow, value⟩) [memory0, memory1] y.memory) ++
    [⟨memoryFinalCounters, memoryLow, y.memoryFinal⟩, ⟨bytecodeFinalCounters, bytecodeLow,
      y.bytecodeFinal⟩]
  let fp := fingerprints y.weights y.memory memoryLow bytecodeLow y.share
  let pcFinal := Verifier.gpow (2 ^ layout.logBytecode - 1)
  let forms0 : List (List Form) := tables.map fun _ ↦ [{}, {}, {}]
  let (forms1, total0) := accumulateSide forms0 0 layout.push pushLayout (fp (Verifier.gpow 0) 1 1)
    y.weights y.beta y.point (y.treeValues.getD 0 0)
  let (forms2, total1) := accumulateSide forms1 1 layout.pull pullLayout
    (fp pcFinal y.memoryFinal y.bytecodeFinal) y.weights y.beta y.point (y.treeValues.getD 1 0)
  let (forms3, total2) := accumulateSide forms2 2 layout.count countLayout [] [1] 0 y.point
    (y.treeValues.getD 2 0)
  ⟨claims, y.bytecodePoint, y.point, forms3, [total0, total1, total2]⟩

/-- The verifier after its evaluation of the bytecode. -/
def suffixProg (publicInput : Digest) (y : Pre) : VerifierProgram Unit := do
  let layout := y.layout
  let bus := busOf y
  let evaluations ← tablePhase layout bus
  let claims := bus.claims ++ tableColumnClaims evaluations
  let publicClaims ← publicInputPhase layout publicInput
  let claims := claims ++ publicClaims
  let (outputs, keccakPoint, keccakSlices) ← keccakPhase layout evaluations
  let claims := claims ++ outputs
  let (ringTarget, ringWeight) ← ringSwitch keccakPoint keccakSlices
  verifyStackedOpening layout.stackLog y.rate
    (ringSwitchClaim layout ringTarget ringWeight :: claims.filterMap (·.onStack layout) ++ [y.ood])

/-- **The verifier, split at its evaluation of the bytecode.** -/
theorem execSplit (ev : List K → List E → E → VerifierProgram Unit) (bytecode : List K)
    (publicInput : Digest) :
    verifyExecution ev bytecode publicInput = (prefixProg bytecode).bind fun y ↦
      (ev y.layout.bytecode y.bytecodePoint y.value).bind fun _ ↦ suffixProg publicInput y := by
  simp only [verifyExecution, prefixProg, VerifierProgram.bind_eq, VerifierProgram.pure_eq,
      VerifierProgram.bind_assoc, VerifierProgram.ret_bind]
  refine congrArg _ (funext fun ls ↦ ?_)
  obtain ⟨layout, rate⟩ := ls
  refine congrArg _ (funext fun _ ↦ congrArg _ (funext fun ood ↦ ?_))
  simp only [verifyBusBalance, VerifierProgram.bind_eq, VerifierProgram.pure_eq,
      VerifierProgram.bind_assoc, VerifierProgram.ret_bind]
  refine congrArg _ (funext fun _ ↦ congrArg _ (funext fun _ ↦ congrArg _ (funext fun weights ↦
    congrArg _ (funext fun beta ↦ congrArg _ (funext fun g ↦ ?_)))))
  obtain ⟨countRoot, point, treeValues⟩ := g
  refine congrArg _ (funext fun _ ↦ congrArg _ (funext fun memory ↦
    congrArg _ (funext fun mf ↦ congrArg _ (funext fun bf ↦ congrArg _ (funext fun sh ↦ ?_)))))
  obtain ⟨share, bytecodePoint, value⟩ := sh
  refine congrArg _ (funext fun _ ↦ ?_)
  rfl

/-- The prefix returns a layout of the bytecode it read. -/
theorem prefix_bytecode {bytecode : List K} {y : Pre}
    (h : VerifierProgram.Returns (prefixProg bytecode) y) : y.layout.bytecode = bytecode := by
  unfold prefixProg at h
  obtain ⟨ls, hls, h⟩ := VerifierProgram.returns_bind h
  have hb := readSizes_bytecode hls
  iterate 11 obtain ⟨_, -, h⟩ := VerifierProgram.returns_bind h
  obtain ⟨⟨_, _, _⟩, -, h⟩ := VerifierProgram.returns_bind h
  rw [VerifierProgram.returns_ret h]
  exact hb

/-! ## The claim a run evaluates -/

section Run

variable (H : Bytes → Id Digest) (F : KeccakState → Id KeccakState) (bytecode : List K)
  (publicInput : Digest)

/-- **A run with the computed value that returns is the run with a true claim**: the claim of the
value at the point the run evaluates. -/
theorem run_claimed_of_computed (k : Unit → VerifierProgram Bool) {st : VerifierProgramState}
    {r : Bool × VerifierProgramState}
    (h : Compile.runWithHash H F ((verifyExecution computedBytecodeValue bytecode
      publicInput).bind k) st = some r) :
    ∃ c : BytecodeClaim, c.Holds bytecode ∧
      Compile.runWithHash H F ((verifyExecution (claimedBytecodeValue c) bytecode
        publicInput).bind k) st = some r := by
  rw [execSplit, VerifierProgram.bind_assoc, runWithHash_bind] at h
  rcases hp : Compile.runWithHash H F (prefixProg bytecode) st with _ | ⟨y, s1⟩
  · rw [hp] at h; simp at h
  rw [hp] at h
  have hy : y.layout.bytecode = bytecode :=
    prefix_bytecode (VerifierProgram.returns_of_run H F hp)
  simp only [Option.bind_some] at h
  rw [hy] at h
  by_cases hv : multilinearEval (bytecode.map ofK) y.bytecodePoint = y.value
  · refine ⟨⟨y.bytecodePoint, y.value⟩, hv, ?_⟩
    rw [execSplit, VerifierProgram.bind_assoc, runWithHash_bind, hp]
    simp only [Option.bind_some]
    rw [← h, hy]
    simp only [claimedBytecodeValue, computedBytecodeValue, VerifierProgram.require, hv,
      and_self, ↓reduceIte]
  · exfalso
    simp only [computedBytecodeValue, VerifierProgram.require, hv, ↓reduceIte,
      VerifierProgram.bind] at h
    simp [Compile.runWithHash] at h

/-- **A run with a claim that returns has the prefix's point and value as its claim.** -/
theorem claim_of_run_claimed {c : BytecodeClaim} (k : Unit → VerifierProgram Bool)
    {st : VerifierProgramState} {r : Bool × VerifierProgramState}
    (h : Compile.runWithHash H F ((verifyExecution (claimedBytecodeValue c) bytecode
      publicInput).bind k) st = some r) :
    ∃ y s1, Compile.runWithHash H F (prefixProg bytecode) st = some (y, s1) ∧
      c = ⟨y.bytecodePoint, y.value⟩ := by
  rw [execSplit, VerifierProgram.bind_assoc, runWithHash_bind] at h
  rcases hp : Compile.runWithHash H F (prefixProg bytecode) st with _ | ⟨y, s1⟩
  · rw [hp] at h; simp at h
  rw [hp] at h
  refine ⟨y, s1, rfl, ?_⟩
  simp only [Option.bind_some] at h
  by_cases hv : y.bytecodePoint = c.bytecodePoint ∧ y.value = c.bytecodeValue
  · obtain ⟨p, v⟩ := c
    obtain ⟨rfl, rfl⟩ := hv
    rfl
  · exfalso
    simp only [claimedBytecodeValue, VerifierProgram.require, hv, ↓reduceIte,
      VerifierProgram.bind] at h
    simp [Compile.runWithHash] at h

/-- **An accepted proof with the computed value is accepted with a true claim.** -/
theorem runProof_claimed_of_computed {sd : KeccakState} {π : Proof}
    (h : Id.run (runProofWithHash H F ((verifyExecution computedBytecodeValue bytecode
        publicInput).bind fun _ ↦ VerifierProgram.ret true) sd π) = true) :
    ∃ c : BytecodeClaim, c.Holds bytecode ∧
      Id.run (runProofWithHash H F ((verifyExecution (claimedBytecodeValue c) bytecode
          publicInput).bind fun _ ↦ VerifierProgram.ret true) sd π) = true := by
  unfold runProofWithHash at h ⊢
  revert h
  match hr : Compile.runWithHash H F ((verifyExecution computedBytecodeValue bytecode
      publicInput).bind fun _ ↦ VerifierProgram.ret true)
        ⟨⟨sd, [], none⟩, π.stream, π.openings, []⟩ with
  | some (true, s) =>
    intro h
    obtain ⟨c, hc, e⟩ := run_claimed_of_computed H F bytecode publicInput _ hr
    refine ⟨c, hc, ?_⟩
    rw [e]
    exact h
  | some (false, _) => intro h; cases h
  | none => intro h; cases h

/-- **An accepted proof with a claim has the prefix's point and value as its claim.** -/
theorem claim_of_runProof_claimed {c : BytecodeClaim} {sd : KeccakState} {π : Proof}
    (h : Id.run (runProofWithHash H F ((verifyExecution (claimedBytecodeValue c) bytecode
        publicInput).bind fun _ ↦ VerifierProgram.ret true) sd π) = true) :
    ∃ y s1, Compile.runWithHash H F (prefixProg bytecode)
        ⟨⟨sd, [], none⟩, π.stream, π.openings, []⟩ = some (y, s1) ∧
      c = ⟨y.bytecodePoint, y.value⟩ := by
  unfold runProofWithHash at h
  generalize hr : Compile.runWithHash H F ((verifyExecution (claimedBytecodeValue c) bytecode
      publicInput).bind fun _ ↦ VerifierProgram.ret true)
        ⟨⟨sd, [], none⟩, π.stream, π.openings, []⟩ = o at h
  rcases o with _ | ⟨_ | _, _⟩
  · cases h
  · cases h
  · exact claim_of_run_claimed H F bytecode publicInput _ hr

end Run

end
end LeanVM.Protocol.Verifier.Defers

namespace LeanVM.Protocol.Verifier

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Compile
open LeanVM.Protocol.KeccakHash Defers

@[expose] public section

section Hash

variable (H : Bytes → Id Digest) (F : KeccakState → Id KeccakState)

/-- **The deferring verifier accepts a proof with at most one claim**, at any hash and
permutation, IV and public input. -/
theorem claim_unique {bytecode : List K} {iv publicInput : Digest} {c c' : BytecodeClaim}
    {π : Proof}
    (h : Id.run (verifyDeferredWithHash H F bytecode iv publicInput c π) = true)
    (h' : Id.run (verifyDeferredWithHash H F bytecode iv publicInput c' π) = true) : c = c' := by
  have e : ∀ c, Id.run (verifyDeferredWithHash H F bytecode iv publicInput c π) =
      Id.run (runProofWithHash H F ((verifyExecution (claimedBytecodeValue c) bytecode
        publicInput).bind fun _ ↦ VerifierProgram.ret true) (Id.run (F (seedInput iv publicInput)))
          π) := fun _ ↦ rfl
  rw [e] at h h'
  obtain ⟨y, s1, hy, rfl⟩ := claim_of_runProof_claimed H F _ _ h
  obtain ⟨y', s1', hy', rfl⟩ := claim_of_runProof_claimed H F _ _ h'
  rw [hy] at hy'
  obtain ⟨rfl, -⟩ := Prod.mk.inj (Option.some.inj hy')
  rfl

/-- **A proof the verifier accepts, the deferring verifier accepts under the verifier's IV with
exactly one claim, and that claim is true**, at any hash and permutation. -/
theorem verifyDeferredWithHash_of_verifyWithHash {bytecode : List K} {publicInput : Digest}
    {π : Proof} (h : Id.run (verifyWithHash H F bytecode publicInput π) = true) :
    ∃ c : BytecodeClaim, c.Holds bytecode ∧
      Id.run (verifyDeferredWithHash H F bytecode (Id.run (fiatShamirIvWithHash H bytecode))
        publicInput c π) = true ∧
      ∀ c', Id.run (verifyDeferredWithHash H F bytecode (Id.run (fiatShamirIvWithHash H bytecode))
        publicInput c' π) = true → c' = c := by
  have h0 : Id.run (runProofWithHash H F ((verifyExecution computedBytecodeValue bytecode
      publicInput).bind fun _ ↦ VerifierProgram.ret true)
        (Id.run (seedWithHash H F bytecode publicInput)) π) = true := h
  obtain ⟨c, hc, hacc⟩ := runProof_claimed_of_computed H F bytecode publicInput h0
  have hd : Id.run (verifyDeferredWithHash H F bytecode (Id.run (fiatShamirIvWithHash H bytecode))
      publicInput c π) = true := hacc
  exact ⟨c, hc, hd, fun c' h' ↦ claim_unique H F h' hd⟩

end Hash

end
end LeanVM.Protocol.Verifier

namespace LeanVM

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Compile
open LeanVM.Protocol.Verifier LeanVM.Protocol.KeccakHash

@[expose] public section

/-- **A proof the leanVM verifier accepts is deferred**: over any permutation function `π` in
`Id`, the deferring verifier accepts it, under the IV the verifier hashes, with exactly one claim on
the bytecode, and that claim is true. -/
theorem verifyDeferredWith_of_leanVmVerifier (π : KeccakState → Id KeccakState)
    {prog : LeanIsaProgram} {input : PublicInput} {proof : Proof}
    (h : Id.run (leanVmVerifier π prog input proof) = true) :
    ∃ c : BytecodeClaim, c.Holds (bytecodeWords prog) ∧
      Id.run (verifyDeferredWith π (bytecodeWords prog)
        (Id.run (fiatShamirIvWith π (bytecodeWords prog))) (publicInputDigest input) c proof) =
          true ∧
      ∀ c', Id.run (verifyDeferredWith π (bytecodeWords prog)
        (Id.run (fiatShamirIvWith π (bytecodeWords prog))) (publicInputDigest input) c' proof) =
          true → c' = c := by
  have h' : Id.run (verifyWithHash (keccak256With π) π (bytecodeWords prog) (publicInputDigest input)
      proof) = true := by
    rw [← verifyWith_eq_withHash]
    exact h
  simp only [verifyDeferredWith_eq_withHash]
  exact verifyDeferredWithHash_of_verifyWithHash _ _ h'

/-- **A proof the deployed leanVM verifier accepts is deferred**: the deployed deferring verifier
accepts it, under the deployed IV, with exactly one claim on the bytecode, and that claim is
true. -/
theorem verifyDeferred_of_leanVmVerifier {prog : LeanIsaProgram} {input : PublicInput}
    {proof : Proof} (h : leanVmVerifier (m := Id) keccakF1600 prog input proof = true) :
    ∃ c : BytecodeClaim, c.Holds (bytecodeWords prog) ∧
      verifyDeferred (bytecodeWords prog) (fiatShamirIv (bytecodeWords prog))
        (publicInputDigest input) c proof = true ∧
      ∀ c', verifyDeferred (bytecodeWords prog) (fiatShamirIv (bytecodeWords prog))
        (publicInputDigest input) c' proof = true → c' = c :=
  verifyDeferredWith_of_leanVmVerifier keccakF1600 h

end
end LeanVM
