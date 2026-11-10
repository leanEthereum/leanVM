/-
  LeanVM.Guest.NZProgram

  The verifier refusing a zero challenge exactly where the guest divides: the fold and tail
  challenges and each WHIR level's batching challenge `λ` (G:1400, 1709, 1714), as copies of the
  verifier's programs with one `require` each. The statement refuses a zero challenge anywhere
  (`VerifierProgram.refusingZeroChallenge`, `Statement/LeanVmGuestCompleteness.lean`), which accepts
  less (`LeanVM.Guest.Child.refines_refuseZero_of_nz`); the guest's proofs work with these.
-/

module

public import LeanVM.Protocol.Verifier.WhirTarget
public import LeanVM.Protocol.Verifier.Claims
public import Statement.LeanVmGuest
public import LeanVM.Protocol.WithHash

@[expose] public section

namespace LeanVM.Guest

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Compile LeanVM.Protocol.Verifier LeanVM.Node

namespace Limits

/-- `foldRounds` refusing a zero challenge. -/
def foldRoundsNZ (grinding : ℕ) : ℕ → WhirStateT → List E → VerifierProgram (WhirStateT × List E)
  | 0, s, levelFolds => return (s, levelFolds)
  | n + 1, s, levelFolds => do
    VerifierProgram.foldProofOfWork grinding
    let challenge ← VerifierProgram.sampleChallenge
    VerifierProgram.require (challenge ≠ 0)
    let target := polyEval s.quad challenge
    let quad ← sumcheckRoundPoly 3 target none
    foldRoundsNZ grinding n { s with target, quad, folds := s.folds ++ [challenge] }
      (levelFolds ++ [challenge])

/-- `tailRounds` refusing a zero challenge. -/
def tailRoundsNZ : ℕ → E → List E → VerifierProgram (List E × E)
  | 0, target, _ => return ([], target)
  | n + 1, _, quad => do
    let challenge ← VerifierProgram.sampleChallenge
    VerifierProgram.require (challenge ≠ 0)
    let target := polyEval quad challenge
    if n = 0 then return ([challenge], target)
    else do
      let quad ← sumcheckRoundPoly 3 target none
      let (rest, target) ← tailRoundsNZ n target quad
      return (challenge :: rest, target)

/-- `whirLevels` refusing a zero fold, tail or level batching challenge. -/
def whirLevelsNZ (logN laneFolds : ℕ) (evaluateBasis : List E → E) :
    ℕ → List Whir.Level → WhirStateT → VerifierProgram Unit
  | _, [], _ => VerifierProgram.fail
  | index, level :: rest, s => do
    let (s, levelFolds) ← foldRoundsNZ level.foldGrinding level.fold s []
    let messageLog := logN - s.folds.length
    let (residual, pending) ← match rest with
      | [] => do
        let residual ← VerifierProgram.readScalars (2 ^ messageLog)
        pure (residual, ([] : List (E × List E × (List E → E))))
      | next :: _ => do
        let (height, width) := levelShape messageLog next (3 * 2 ^ next.fold)
        VerifierProgram.readCommitment height width
        let oodPoint ← VerifierProgram.sampleChallenges messageLog
        let oodValue ← VerifierProgram.readScalar
        let intro ← sumcheckRoundPoly 3 oodValue none
        pure ([], [(oodValue, intro, fun x ↦ eqEval oodPoint x)])
    VerifierProgram.grindProofOfWork Whir.queryGrindingBits
    let queries ← sampleQueries (messageLog + level.logInvRate) level.queries
    let lam ← VerifierProgram.sampleChallenge
    VerifierProgram.require (lam ≠ 0)
    let queryWeights := powers lam queries.length
    let words ← VerifierProgram.queryOpenings index queries
    let rows : List (List E) :=
      if index = 0 then words.map fun row ↦ row.reverse.map ofK else words.map extRow
    let enforced := enforcedSum rows levelFolds queryWeights
    let intro ← sumcheckRoundPoly 3 enforced none
    let pending := pending ++
      [(enforced, intro, fun x ↦ inducedWeight messageLog queries queryWeights x)]
    let s := glueT lam s pending
    match rest with
    | [] => do
      let (tailFolds, target) ← tailRoundsNZ messageLog s.target s.quad
      let point := s.folds ++ tailFolds
      let weight := s.glued.foldl
        (fun weight claim ↦
          weight + claim.scalar * claim.weightAt (s.folds.drop claim.foldStart ++ tailFolds))
        (evaluateBasis (point.drop laneFolds ++ point.take laneFolds))
      let terminal := weight * multilinearEval residual tailFolds
      VerifierProgram.require (terminal = target)
    | _ :: _ => whirLevelsNZ logN laneFolds evaluateBasis (index + 1) rest s

/-- `verifyWhir` refusing a zero fold, tail or level batching challenge. -/
def verifyWhirNZ (logN logInvRate : ℕ) (target : E) (evaluateBasis : List E → E) : VerifierProgram
    Unit := do
  let config ← liftOption (Whir.ladder logN logInvRate)
  let quad ← sumcheckRoundPoly 3 target none
  whirLevelsNZ logN ((config.head?.map (·.fold)).getD 0) evaluateBasis 0 config
    ⟨target, quad, [], []⟩

/-- `verifyStackedOpening` refusing a zero fold, tail or level batching challenge. -/
def verifyStackedOpeningNZ (stackLog logInvRate : ℕ) (claims : List StackClaim) : VerifierProgram
    Unit := do
  let scales := powers (← VerifierProgram.sampleChallenge) claims.length
  verifyWhirNZ stackLog logInvRate (dot scales (claims.map (·.2)))
    fun point ↦ dot scales (claims.map fun c ↦ c.1 point)

/-- `verifyExecution` whose stacked opening refuses a zero fold, tail or level batching
challenge. -/
def verifyExecutionNZ (ev : (List K → List E → VerifierProgram E)) (bytecode : List K) (publicInput
    : Digest) :
    VerifierProgram Unit := do
  let (layout, logInverseRate) ← readAnnouncedSizes bytecode
  commitStack layout.stackLog logInverseRate
  let bus ← verifyBusBalance ev layout
  let claims ← tablePhaseClaims layout bus
  let publicClaims ← publicInputPhase layout publicInput
  let claims := claims ++ publicClaims
  let (claims, keccakPoint, keccakSlices) ← keccakPhaseClaims layout claims
  let (ringTarget, ringWeight) ← ringSwitch keccakPoint keccakSlices
  verifyStackedOpeningNZ layout.stackLog logInverseRate
    (ringSwitchClaim layout ringTarget ringWeight :: claims.map (·.stackClaim layout))

/-- `deferringVerifierProgram` whose stacked opening refuses a zero fold, tail or level batching
challenge. -/
def deferredProgramNZ (c : BytecodeClaim) (bytecode : List K) (publicInput : Digest) :
    VerifierProgram Bool := do
  verifyExecutionNZ (claimedBytecodeValue c) bytecode publicInput
  return true

/-- **The deployed deferring verifier refusing a zero challenge where the guest program divides**:
`verifyDeferred` with `deferredProgramNZ`. -/
def verifyDeferredNZ (bytecode : List K) (iv publicInput : Digest) (c : BytecodeClaim)
    (π : Proof) : Bool :=
  Id.run (runProofWithHash (m := Id) keccak256 keccakF1600 (deferredProgramNZ c bytecode publicInput)
    (keccakF1600 (seedInput iv publicInput)) π)

end Limits

namespace Budget

/-- **The leanVM verifier refusing a zero challenge where the guest program divides**:
`verifier H F` with `Limits.verifyExecutionNZ`. -/
def verifierNZ {m : Type → Type} [Monad m] (H : Bytes → m Digest) (F : KeccakState → m KeccakState)
    (prog : LeanIsaProgram) (input : PublicInput) (proof : Proof) : m Bool := do
  let seed ← seedWithHash H F (bytecodeWords prog) (publicInputDigest input)
  runProofWithHash H F (do
    Limits.verifyExecutionNZ computedBytecodeValue (bytecodeWords prog) (publicInputDigest input)
    return true) seed proof

end Budget

end LeanVM.Guest

end
