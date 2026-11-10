/-
  LeanVM.Guest.Child.Fresh

  A proof the leanVM verifier accepts is accepted by the deferring verifier with a true claim on
  the bytecode, the one its run evaluates: for the deployed stacked opening and the one refusing a
  zero challenge.
-/

module

public import LeanVM.Protocol.Verifier.Claims
public import LeanVM.Guest.LimitsNZ
public import LeanVM.Protocol.Verifier.Deferred
public import LeanVM.Protocol.WithHash

/-!
# The claims of an accepted run

The verifier reads the fixed polynomial once, at the bus's bytecode point (`verifyBusBalance`).
`execWith ev opening` is `verify_execution` with the evaluation `ev` and the stacked opening
`opening` (`verifyStackedOpening`, or `Limits.verifyStackedOpeningNZ`). It is a prefix
(`prefixProg`: the sizes, the stack's root and its out-of-domain sample, the bus up to its slot
sumcheck), the evaluation at the point and of the value the prefix returns (`busPoint`), and a
suffix (`execSplit`). So an accepted run with the computed
value is the run with the claim of that value at that point (`run_claimed_of_computed`), a claim
true of the bytecode (`BytecodeClaim.Holds`).
-/

namespace LeanVM.Guest.Child

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Compile
open LeanVM.Protocol.Verifier LeanVM.Protocol.KeccakHash

@[expose] public section

/-! ## The compiled run of a sequence -/

/-- A sequence's run is the first part's, then the continuation's. -/
theorem run_bind' {α β : Type} (H : Bytes → Id Digest) (F : KeccakState → Id KeccakState) (p : VerifierProgram α)
    (f : α → VerifierProgram β) (st : VerifierProgramState) :
    Compile.runWithHash H F (p.bind f) st =
      (Compile.runWithHash H F p st).bind (fun r => Compile.runWithHash H F (f r.1) r.2) := by
  induction p generalizing st with
  | ret a => rfl
  | fail => rfl
  | read k ih =>
    simp only [VerifierProgram.bind, Compile.runWithHash]
    split
    · exact ih _ _
    · rfl
  | sample k ih => exact ih _ _
  | grind b k ih =>
    simp only [VerifierProgram.bind, Compile.runWithHash]
    split
    · simp only [bind, pure]
      split
      · exact ih _
      · rfl
    · rfl
  | commit h w k ih =>
    simp only [VerifierProgram.bind, Compile.runWithHash]
    split
    · exact ih _
    · rfl
  | query i ps k ih =>
    simp only [VerifierProgram.bind, Compile.runWithHash]
    split
    · simp only [bind]
      split
      · exact ih _ _
      · rfl
    · rfl

/-! ## The verifier, split at its evaluation -/

/-- `verify_execution` with the evaluation `ev` and the stacked opening `opening`. -/
def execWith (ev : List K → List E → E → VerifierProgram Unit)
    (opening : ℕ → ℕ → List StackClaim → VerifierProgram Unit)
    (bytecode : List K) (publicInput : Digest) : VerifierProgram Unit := do
  let (layout, logInverseRate) ← readAnnouncedSizes bytecode
  commitStack layout.stackLog logInverseRate
  let ood ← readOod layout.stackLog
  let bus ← verifyBusBalance ev layout
  let evaluations ← tablePhase layout bus
  let claims := bus.claims ++ tableColumnClaims evaluations
  let publicClaims ← publicInputPhase layout publicInput
  let claims := claims ++ publicClaims
  let (outputs, keccakPoint, keccakSlices) ← keccakPhase layout evaluations
  let claims := claims ++ outputs
  let (ringTarget, ringWeight) ← ringSwitch keccakPoint keccakSlices
  opening layout.stackLog logInverseRate
    (ringSwitchClaim layout ringTarget ringWeight :: claims.filterMap (·.onStack layout) ++ [ood])

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

/-- The verifier up to its evaluation of the bytecode: the slot sumcheck's point and value. -/
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

/-- The point at which the verifier evaluates the bytecode. -/
def busPoint (y : Pre) : List E := y.bytecodePoint

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
def suffixProg (opening : ℕ → ℕ → List StackClaim → VerifierProgram Unit) (publicInput : Digest)
    (y : Pre) : VerifierProgram Unit := do
  let layout := y.layout
  let bus := busOf y
  let evaluations ← tablePhase layout bus
  let claims := bus.claims ++ tableColumnClaims evaluations
  let publicClaims ← publicInputPhase layout publicInput
  let claims := claims ++ publicClaims
  let (outputs, keccakPoint, keccakSlices) ← keccakPhase layout evaluations
  let claims := claims ++ outputs
  let (ringTarget, ringWeight) ← ringSwitch keccakPoint keccakSlices
  opening layout.stackLog y.rate
    (ringSwitchClaim layout ringTarget ringWeight :: claims.filterMap (·.onStack layout) ++ [y.ood])

/-- **The verifier, split at its evaluation of the bytecode.** -/
theorem execSplit (ev : List K → List E → E → VerifierProgram Unit)
    (opening : ℕ → ℕ → List StackClaim → VerifierProgram Unit)
    (bytecode : List K) (publicInput : Digest) :
    execWith ev opening bytecode publicInput = (prefixProg bytecode).bind fun y ↦
      (ev y.layout.bytecode y.bytecodePoint y.value).bind fun _ ↦
        suffixProg opening publicInput y := by
  simp only [execWith, prefixProg, VerifierProgram.bind_eq, VerifierProgram.pure_eq,
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
theorem prefix_bytecode {bytecode : List K} {y : Pre} (h : VerifierProgram.Returns (prefixProg
    bytecode) y) :
    y.layout.bytecode = bytecode := by
  unfold prefixProg at h
  obtain ⟨ls, hls, h⟩ := VerifierProgram.returns_bind h
  have hb := readSizes_bytecode hls
  obtain ⟨_, -, h⟩ := VerifierProgram.returns_bind h
  obtain ⟨_, -, h⟩ := VerifierProgram.returns_bind h
  obtain ⟨_, -, h⟩ := VerifierProgram.returns_bind h
  obtain ⟨_, -, h⟩ := VerifierProgram.returns_bind h
  obtain ⟨_, -, h⟩ := VerifierProgram.returns_bind h
  obtain ⟨_, -, h⟩ := VerifierProgram.returns_bind h
  obtain ⟨_, -, h⟩ := VerifierProgram.returns_bind h
  obtain ⟨_, -, h⟩ := VerifierProgram.returns_bind h
  obtain ⟨_, -, h⟩ := VerifierProgram.returns_bind h
  obtain ⟨_, -, h⟩ := VerifierProgram.returns_bind h
  obtain ⟨_, -, h⟩ := VerifierProgram.returns_bind h
  obtain ⟨⟨_, _, _⟩, -, h⟩ := VerifierProgram.returns_bind h
  rw [VerifierProgram.returns_ret h]
  exact hb

/-! ## The deferring verifiers -/

/-- The deferring program refusing a zero challenge, as a sequence. -/
theorem deferredProgramNZ_eq (c : BytecodeClaim) (bytecode : List K) (publicInput : Digest) :
    Limits.deferredProgramNZ c bytecode publicInput =
      (execWith (claimedBytecodeValue c) Limits.verifyStackedOpeningNZ bytecode publicInput).bind
        fun _ ↦ VerifierProgram.ret true := rfl

end
end LeanVM.Guest.Child
