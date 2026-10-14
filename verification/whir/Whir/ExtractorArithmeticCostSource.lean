import Whir.PCSRewindSourceProgram
import Whir.CountedCandidateCheckOriginalResources
import Whir.CountedCandidateCheckOriginalMap
import Whir.ExtractorArithmeticCostBounds

/-! Counted actual source extraction. The common-coordinate certificate runs without redundant compressed functional checks; the immutable original checker then checks all 64 slices of every family, all original points and the saved anchor. Each attempt includes its fresh source transformation and the real causal reset collector. -/
namespace Whir.ExtractorArithmeticCostSource
open Concrete Protocol CausalGame KnowledgeExtraction SupportedCandidateExtraction
open AuthenticatedResetSupport PCSRewindExtractor CountedCandidateCheck ExtractorArithmeticCost

set_option maxHeartbeats 4000000
set_option maxRecDepth 4096
attribute [local irreducible] ParameterBounds.config

def decoded (input : Public) (records : List (Record input.config))
    (noWrap : input.config.logN - input.config.folds[0]! + input.config.rates[0]! ≤ 64)
    (checker : Witness input.config input.lanes → Bool × OriginalClaimsChecker.Work) :
    Option (Witness input.config input.lanes) × Nat :=
  let source := decodeRecords input records noWrap
  match source.1 with
  | none => (none, source.2)
  | some w =>
    let certificate := countedFinish {input with claims := #[]} (paddedWitness input.config input.lanes w) records
    match certificate.1 with
    | none => (none, source.2 + certificate.2)
    | some certified =>
      let original := checker certified
      (if original.1 then some certified else none, source.2 + certificate.2 + original.2.fieldArithmetic)

theorem decoded_value (input : Public) (records : List (Record input.config))
    (noWrap : input.config.logN - input.config.folds[0]! + input.config.rates[0]! ≤ 64)
    (checker : Witness input.config input.lanes → Bool × OriginalClaimsChecker.Work) :
    (decoded input records noWrap checker).1 =
      PCSRewindSource.decodedWithFinal input records noWrap (fun w => (checker w).1) := by
  unfold decoded PCSRewindSource.decodedWithFinal
  dsimp only
  cases source : (decodeRecords input records noWrap).1 with
  | none => simp
  | some w =>
    simp only [Option.bind_some]
    rw [← countedFinish_value]
    cases certificate : (countedFinish {input with claims := #[]} (paddedWitness input.config input.lanes w) records).1 <;>
      simp

def decodedBound (input : Public) (families points : Nat) : Nat :=
  input.lanes * ConcreteRowExtraction.rowArithmeticPolynomial (blockLength input.config) +
    checkerBound {input with claims := #[]} +
    OriginalClaimsChecker.checkFieldPolynomial (2 ^ input.config.logN) families points

theorem decoded_field (input : Public) (records : List (Record input.config))
    (noWrap : input.config.logN - input.config.folds[0]! + input.config.rates[0]! ≤ 64)
    (redundancy : width input.config < blockLength input.config) (families points : Nat)
    (checker : Witness input.config input.lanes → Bool × OriginalClaimsChecker.Work)
    (originalBound : ∀ w, (checker w).2.fieldArithmetic ≤
      OriginalClaimsChecker.checkFieldPolynomial (2 ^ input.config.logN) families points) :
    (decoded input records noWrap checker).2 ≤ decodedBound input families points := by
  have decoder := decodeRecords_decoder_cost input records noWrap redundancy
  unfold decoded
  dsimp only
  cases source : (decodeRecords input records noWrap).1 with
  | none => dsimp only; unfold decodedBound; omega
  | some w =>
    dsimp only
    have common := countedFinish_cost {input with claims := #[]} (paddedWitness input.config input.lanes w) records
    cases certificate : (countedFinish {input with claims := #[]} (paddedWitness input.config input.lanes w) records).1 with
    | none => dsimp only; unfold decodedBound; omega
    | some certified =>
      have original := originalBound certified
      dsimp only
      unfold decodedBound
      omega

def program (input : Public) (level : Fin input.config.folds.size) (tapes : List (Tape input.config))
    (noWrap : input.config.logN - input.config.folds[0]! + input.config.rates[0]! ≤ 64)
    (checker : Witness input.config input.lanes → Bool × OriginalClaimsChecker.Work) :
    CountedProgram input.config input.lanes :=
  countedCollect input level (input.config.logN - input.config.folds[0]! + input.config.rates[0]!) tapes 0
    (fun records total =>
      let checked := decoded input (baseRecords records) noWrap checker
      .finish checked.1 (total + checked.2))

theorem continueCollect_finish (input : Public) (level : Fin input.config.folds.size) (depth : Nat)
    (tapes : List (Tape input.config))
    (finish : List (Fin (2 ^ depth) × Array E) → Option (Witness input.config input.lanes)) :
    continueCollect input level depth tapes (fun records => .finish (finish records)) =
      collectAcceptedProgram input level depth tapes finish := by
  induction tapes generalizing finish with
  | nil => rfl
  | cons tape tapes ih =>
    simp only [continueCollect, collectAcceptedProgram]
    congr 1
    funext replies
    exact ih _

theorem program_erase (input : Public) (level : Fin input.config.folds.size) (tapes : List (Tape input.config))
    (noWrap : input.config.logN - input.config.folds[0]! + input.config.rates[0]! ≤ 64)
    (checker : Witness input.config input.lanes → Bool × OriginalClaimsChecker.Work) :
    (program input level tapes noWrap checker).erase =
      PCSRewindSource.program input level tapes noWrap (fun w => (checker w).1) := by
  unfold program PCSRewindSource.program
  rw [← continueCollect_finish]
  apply countedCollect_erase
  intro records total
  simp only [CountedProgram.erase, decoded_value]

def runOne {m : Nat} (profile : ParameterBounds.Profile) (rounds lanes : Nat)
    (family : Fin m → RingPCSGame.FamilyClaim) (points : Array RingPCSGame.PointClaim)
    (anchorPoint : Array E) (anchorValue : E)
    (prepared : OriginalClaimsChecker.Prepared (ParameterBounds.config profile) lanes m family points anchorPoint anchorValue)
    (root : BaseOracle) (strategy : RingPCSGame.Prefix → Strategy) (seed : PCSRewindSource.Seed profile rounds) :
    CountedResult (ParameterBounds.config profile) lanes :=
  let inp := OriginalClaimsChecker.countedInput prepared root seed.1
  let result := runCounted inp.1 (strategy seed.1) (streamLength inp.1.config)
    (rounds * streamLength inp.1.config)
    (program inp.1 (initialLevel profile) (seedTapes profile rounds inp.1 rfl seed.2)
      (InitialCandidates.production_initial_facts profile).2.2.1 (OriginalClaimsChecker.countedCheck prepared))
  {result with fieldArithmetic := inp.2.fieldArithmetic + result.fieldArithmetic}

theorem runOne_value {m : Nat} (profile : ParameterBounds.Profile) (rounds lanes : Nat)
    (family : Fin m → RingPCSGame.FamilyClaim) (points : Array RingPCSGame.PointClaim)
    (anchorPoint : Array E) (anchorValue : E)
    (prepared : OriginalClaimsChecker.Prepared (ParameterBounds.config profile) lanes m family points anchorPoint anchorValue)
    (root : BaseOracle) (strategy : RingPCSGame.Prefix → Strategy) (seed : PCSRewindSource.Seed profile rounds) :
    (runOne profile rounds lanes family points anchorPoint anchorValue prepared root strategy seed).output =
      (PCSRewindSource.runOne profile rounds lanes family points anchorPoint anchorValue prepared root strategy seed).output ∧
    (runOne profile rounds lanes family points anchorPoint anchorValue prepared root strategy seed).responseCalls =
      (PCSRewindSource.runOne profile rounds lanes family points anchorPoint anchorValue prepared root strategy seed).responseCalls := by
  unfold runOne PCSRewindSource.runOne
  dsimp only [OriginalClaimsChecker.countedInput]
  have agreement := runCounted_value (OriginalClaimsChecker.input prepared root seed.1) (strategy seed.1)
    (streamLength (ParameterBounds.config profile)) (rounds * streamLength (ParameterBounds.config profile))
    (program (OriginalClaimsChecker.input prepared root seed.1) (initialLevel profile)
      (seedTapes profile rounds (OriginalClaimsChecker.input prepared root seed.1) rfl seed.2)
      (InitialCandidates.production_initial_facts profile).2.2.1 (OriginalClaimsChecker.countedCheck prepared))
  have erased := program_erase (OriginalClaimsChecker.input prepared root seed.1) (initialLevel profile)
    (seedTapes profile rounds (OriginalClaimsChecker.input prepared root seed.1) rfl seed.2)
    (InitialCandidates.production_initial_facts profile).2.2.1 (OriginalClaimsChecker.countedCheck prepared)
  rw [erased] at agreement
  have checkEq : (fun w : Witness (ParameterBounds.config profile) lanes =>
      (OriginalClaimsChecker.countedCheck prepared w).1) = OriginalClaimsChecker.check prepared :=
    funext (OriginalClaimsChecker.countedCheck_value prepared)
  have programs := congrArg (fun checker : Witness (ParameterBounds.config profile) lanes → Bool =>
    PCSRewindSource.program (OriginalClaimsChecker.input prepared root seed.1) (initialLevel profile)
      (seedTapes profile rounds (OriginalClaimsChecker.input prepared root seed.1) rfl seed.2)
      (InitialCandidates.production_initial_facts profile).2.2.1 checker) checkEq
  have machines := congrArg (fun p => runRewind (OriginalClaimsChecker.input prepared root seed.1)
    (strategy seed.1) (streamLength (ParameterBounds.config profile))
    (rounds * streamLength (ParameterBounds.config profile)) p) programs
  exact ⟨agreement.1.trans (congrArg RewindResult.output machines),
    agreement.2.trans (congrArg RewindResult.responseCalls machines)⟩

def runAttempts {m : Nat} (profile : ParameterBounds.Profile) (rounds lanes : Nat)
    (family : Fin m → RingPCSGame.FamilyClaim) (points : Array RingPCSGame.PointClaim)
    (anchorPoint : Array E) (anchorValue : E)
    (prepared : OriginalClaimsChecker.Prepared (ParameterBounds.config profile) lanes m family points anchorPoint anchorValue)
    (root : BaseOracle) (strategy : RingPCSGame.Prefix → Strategy) :
    List (PCSRewindSource.Seed profile rounds) → CountedResult (ParameterBounds.config profile) lanes
  | [] => ⟨none, 0, 0, 0⟩
  | seed :: rest =>
    let first := runOne profile rounds lanes family points anchorPoint anchorValue prepared root strategy seed
    match first.output with
    | some w => {first with output := some w}
    | none =>
      let later := runAttempts profile rounds lanes family points anchorPoint anchorValue prepared root strategy rest
      ⟨later.output, first.fieldArithmetic + later.fieldArithmetic, first.responseCalls + later.responseCalls,
        first.encodedReplyWords + later.encodedReplyWords⟩

theorem runAttempts_value {m : Nat} (profile : ParameterBounds.Profile) (rounds lanes : Nat)
    (family : Fin m → RingPCSGame.FamilyClaim) (points : Array RingPCSGame.PointClaim)
    (anchorPoint : Array E) (anchorValue : E)
    (prepared : OriginalClaimsChecker.Prepared (ParameterBounds.config profile) lanes m family points anchorPoint anchorValue)
    (root : BaseOracle) (strategy : RingPCSGame.Prefix → Strategy) (seeds : List (PCSRewindSource.Seed profile rounds)) :
    (runAttempts profile rounds lanes family points anchorPoint anchorValue prepared root strategy seeds).output =
      (PCSRewindSource.runAttempts profile rounds lanes family points anchorPoint anchorValue prepared root strategy seeds).output ∧
    (runAttempts profile rounds lanes family points anchorPoint anchorValue prepared root strategy seeds).responseCalls =
      (PCSRewindSource.runAttempts profile rounds lanes family points anchorPoint anchorValue prepared root strategy seeds).responseCalls := by
  induction seeds with
  | nil => exact ⟨rfl, rfl⟩
  | cons seed rest ih =>
    have first := runOne_value profile rounds lanes family points anchorPoint anchorValue prepared root strategy seed
    simp only [runAttempts, PCSRewindSource.runAttempts]
    rw [first.1]
    split <;> dsimp only <;> simp_all

def run {m : Nat} (profile : ParameterBounds.Profile) (attempts rounds lanes : Nat)
    (family : Fin m → RingPCSGame.FamilyClaim) (points : Array RingPCSGame.PointClaim)
    (anchorPoint : Array E) (anchorValue : E) (root : BaseOracle)
    (strategy : RingPCSGame.Prefix → Strategy) (seed : PCSRewindSource.RepeatedSeed profile attempts rounds) :
    CountedResult (ParameterBounds.config profile) lanes :=
  let cached := OriginalClaimsChecker.countedPrepare (ParameterBounds.config profile) lanes family points anchorPoint anchorValue
  match cached.1 with
  | none => ⟨none, cached.2.fieldArithmetic, 0, 0⟩
  | some prepared =>
    let result := runAttempts profile rounds lanes family points anchorPoint anchorValue prepared root strategy (List.ofFn seed)
    {result with fieldArithmetic := cached.2.fieldArithmetic + result.fieldArithmetic}

theorem run_value {m : Nat} (profile : ParameterBounds.Profile) (attempts rounds lanes : Nat)
    (family : Fin m → RingPCSGame.FamilyClaim) (points : Array RingPCSGame.PointClaim)
    (anchorPoint : Array E) (anchorValue : E) (root : BaseOracle)
    (strategy : RingPCSGame.Prefix → Strategy) (seed : PCSRewindSource.RepeatedSeed profile attempts rounds) :
    (run profile attempts rounds lanes family points anchorPoint anchorValue root strategy seed).output =
      (PCSRewindSource.run profile attempts rounds lanes family points anchorPoint anchorValue root strategy seed).output ∧
    (run profile attempts rounds lanes family points anchorPoint anchorValue root strategy seed).responseCalls =
      (PCSRewindSource.run profile attempts rounds lanes family points anchorPoint anchorValue root strategy seed).responseCalls := by
  unfold run PCSRewindSource.run
  dsimp only
  rw [OriginalClaimsChecker.countedPrepare_value]
  cases cached : OriginalClaimsChecker.prepare (ParameterBounds.config profile) lanes family points anchorPoint anchorValue with
  | none => trivial
  | some prepared =>
    exact runAttempts_value profile rounds lanes family points anchorPoint anchorValue prepared root strategy _

#print axioms run_value

end Whir.ExtractorArithmeticCostSource
