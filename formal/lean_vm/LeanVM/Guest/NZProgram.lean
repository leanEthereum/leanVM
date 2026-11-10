/-
  LeanVM.Guest.NZProgram

  The verifier refusing what makes the guest divide by zero: a zero fold challenge `γ`, a zero
  closing-round challenge, a zero batching challenge `λ` of a non-final level, and a combiner
  `α + β·x` vanishing at a queried point `x` (G:1460, 1693, 1810, 1817; G = `lean_ethereum.py` at
  leanVM `98ceacf2`), as copies of the verifier's programs with a `require` at each. The
  statement's honest child refuses a zero challenge anywhere
  (`VerifierProgram.refusingZeroChallenge`, `Statement/LeanVmGuestCompleteness.lean`).
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

/-- `foldRound` refusing a zero `γ`: the guest divides by the `γ`s past level 0 in its residual
pass (G:1810). -/
def foldRoundNZ (s : WhirState) : VerifierProgram (WhirState × FoldRound) := do
  VerifierProgram.grindProofOfWork Whir.foldGrindingBits
  let theta ← VerifierProgram.sampleChallenge
  let u0 ← VerifierProgram.readScalar
  let v0 ← VerifierProgram.readScalar
  let c0 ← VerifierProgram.readScalar
  let v1 ← VerifierProgram.readScalar
  let c1 ← VerifierProgram.readScalar
  let u1 := s.claim + v0 + theta * u0
  VerifierProgram.grindProofOfWork Whir.foldGrindingBits
  let gamma ← VerifierProgram.sampleChallenge
  VerifierProgram.require (gamma ≠ 0)
  let alpha ← VerifierProgram.sampleChallenge
  let beta ← VerifierProgram.sampleChallenge
  let claim := (1 + gamma) * (u0 + alpha * v0 + beta * c0) + gamma * (u1 + alpha * v1 + beta * c1)
  return ({ s with claim := claim, gammas := s.gammas ++ [gamma] }, ⟨theta, alpha, beta⟩)

/-- `foldRounds` refusing a zero `γ`. -/
def foldRoundsNZ : ℕ → WhirState → VerifierProgram (WhirState × List FoldRound)
  | 0, s => return (s, [])
  | n + 1, s => do
    let (s, round) ← foldRoundNZ s
    let (s, rounds) ← foldRoundsNZ n s
    return (s, round :: rounds)

/-- `sumcheck` refusing a zero challenge: the closing rounds' challenges, which the residual pass
divides by (G:1817). -/
def sumcheckNZ (claim : E) (count : ℕ) : List (Option E) → VerifierProgram (List E × E)
  | [] => return ([], claim)
  | equality :: equalities => do
    let message ← sumcheckRoundPoly count claim equality
    let challenge ← VerifierProgram.sampleChallenge
    VerifierProgram.require (challenge ≠ 0)
    let (point, final) ← sumcheckNZ (polyEval message challenge) count equalities
    return (challenge :: point, final)

/-- No round's combiner `α + β·x` vanishes at a queried point `x`: an opened row's fold divides
by it (`opening_query`, G:1460). -/
def CombinersNZ (queries : List ℕ) (rounds : List FoldRound) : Prop :=
  ∀ q ∈ queries, ∀ r ∈ rounds, r.alpha + r.beta * ofK (K.ofBits q) ≠ 0

instance (queries : List ℕ) (rounds : List FoldRound) : Decidable (CombinersNZ queries rounds) :=
  inferInstanceAs (Decidable (∀ q ∈ queries, ∀ r ∈ rounds, _))

/-- `whirLevels` refusing a zero `γ`, closing-round challenge or non-final `λ`, and a vanishing
combiner at a queried point. -/
def whirLevelsNZ (logN laneFolds : ℕ) (evaluateBasis : List E → E) :
    ℕ → List Whir.Level → WhirState → VerifierProgram Unit
  | _, [], _ => VerifierProgram.fail
  | index, level :: rest, s => do
    let (s, rounds) ← foldRoundsNZ level.fold s
    let mu := logN - s.gammas.length
    let depth := mu + level.logInvRate
    let lanesOf : List K → List E := fun row ↦
      if index = 0 then row.reverse.map ofK else extRow row
    match rest with
    | [] => do
      let folded ← VerifierProgram.readScalars (2 ^ mu + level.fold)
      VerifierProgram.grindProofOfWork Whir.queryGrindingBits
      let queries ← sampleQueries depth level.queries
      VerifierProgram.require (CombinersNZ queries rounds)
      let words ← VerifierProgram.queryOpenings index queries
      VerifierProgram.require ((List.zip queries words).all fun (query, row) ↦
        foldRow (lanesOf row) (K.ofBits query) rounds =
          novelEval folded (subspaceAt mu (K.ofBits query)))
      let (tail, claim) ← sumcheckNZ s.claim 3 (List.replicate mu none)
      let point := s.gammas ++ tail
      let weight := s.glued.foldl
        (fun weight glued ↦ weight + glued.scalar * glued.weightAt (point.drop glued.foldStart))
        (evaluateBasis (point.drop laneFolds ++ point.take laneFolds))
      VerifierProgram.require (weight * multilinearEval (folded.take (2 ^ mu)) tail = claim)
    | next :: _ => do
      let (height, width) := levelShape mu next (2 * 2 ^ next.fold)
      VerifierProgram.readCommitment height width
      let high ← VerifierProgram.readScalars level.fold
      let oodPoints ← sampleOodPoints mu Whir.oodSamples
      let oodValues ← VerifierProgram.readScalars Whir.oodSamples
      VerifierProgram.grindProofOfWork Whir.queryGrindingBits
      let queries ← sampleQueries depth level.queries
      VerifierProgram.require (CombinersNZ queries rounds)
      VerifierProgram.grindProofOfWork Whir.batchGrindingBits
      let lam ← VerifierProgram.sampleChallenge
      VerifierProgram.require (lam ≠ 0)
      let queryWeights := powers lam queries.length
      let words ← VerifierProgram.queryOpenings index queries
      let batched := sumE (List.zipWith (fun (query, row) queryWeight ↦
        let what := subspaceAt mu (K.ofBits query)
        queryWeight * (foldRow (lanesOf row) (K.ofBits query) rounds +
          novelEval high what * ofK (what.getD mu 0))) (List.zip queries words) queryWeights)
      let s := glueLevel s lam mu oodPoints oodValues queries queryWeights batched
      whirLevelsNZ logN laneFolds evaluateBasis (index + 1) rest s

/-- `verifyWhir` refusing what makes the guest divide by zero. -/
def verifyWhirNZ (logN logInvRate : ℕ) (target : E) (evaluateBasis : List E → E) : VerifierProgram
    Unit := do
  let config ← liftOption (Whir.ladder logN logInvRate)
  whirLevelsNZ logN ((config.head?.map (·.fold)).getD 0) evaluateBasis 0 config ⟨target, [], []⟩

/-- `verifyStackedOpening` refusing what makes the guest divide by zero. -/
def verifyStackedOpeningNZ (stackLog logInvRate : ℕ) (claims : List StackClaim) : VerifierProgram
    Unit := do
  VerifierProgram.require (claims.length ≤ maxStackedClaims)
  let scales := powers (← VerifierProgram.sampleChallenge) claims.length
  verifyWhirNZ stackLog logInvRate (dot scales (claims.map (·.2)))
    fun point ↦ dot scales (claims.map fun c ↦ c.1 point)

/-- `verifyExecution` whose stacked opening refuses what makes the guest divide by zero. -/
def verifyExecutionNZ (bytecodeValue : List K → List E → E → VerifierProgram Unit)
    (bytecode : List K) (publicInput : Digest) : VerifierProgram Unit := do
  let (layout, logInverseRate) ← readAnnouncedSizes bytecode
  commitStack layout.stackLog logInverseRate
  let ood ← readOod layout.stackLog
  let bus ← verifyBusBalance bytecodeValue layout
  let evaluations ← tablePhase layout bus
  let claims := bus.claims ++ tableColumnClaims evaluations
  let publicClaims ← publicInputPhase layout publicInput
  let claims := claims ++ publicClaims
  let (outputs, keccakPoint, keccakSlices) ← keccakPhase layout evaluations
  let claims := claims ++ outputs
  let (ringTarget, ringWeight) ← ringSwitch keccakPoint keccakSlices
  verifyStackedOpeningNZ layout.stackLog logInverseRate
    (ringSwitchClaim layout ringTarget ringWeight :: claims.filterMap (·.onStack layout) ++ [ood])

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
