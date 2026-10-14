import Whir.CountedCandidateCheckOriginal
import Whir.PCSRewindExtractorAttempts

/-! Actual source extraction checks every uncompressed binary slice, every
ordinary/strided point, and the retained anchor on the decoded K word. The
collector still accepts exactly ordinary verifier-accepted trials. Public
compression is freshly sampled at each outer attempt; all original source
statements and the commitment stay fixed. -/
namespace Whir.PCSRewindSource
open Concrete Protocol CausalGame KnowledgeExtraction SupportedCandidateExtraction

set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
attribute [local irreducible] ParameterBounds.config
open PCSRewindExtractor OriginalClaimsChecker AuthenticatedResetSupport

/-- The generic final predicate is used only for the common-coordinate and
shape certificate. Original source functionals are checked separately once. -/
def decodedWithFinal (input : Public) (records : List (Record input.config))
    (noWrap : input.config.logN - input.config.folds[0]! + input.config.rates[0]! ≤ 64)
    (checkOriginal : Witness input.config input.lanes → Bool) : Option (Witness input.config input.lanes) :=
  (decodeRecords input records noWrap).1.bind fun decoded =>
    (finish {input with claims := #[]} (paddedWitness input.config input.lanes decoded) records).bind fun certified =>
      if checkOriginal certified then some certified else none

/-- Removing only the public functional checks preserves the same shape and
common-coordinate certificate and the literal projected witness. -/
theorem finish_claimless (input : Public) (candidate : Array E)
    (records : List (Record input.config)) (w : Witness input.config input.lanes)
    (output : finish input candidate records = some w) :
    finish {input with claims := #[]} candidate records = some w := by
  unfold finish at output
  split at output
  · rename_i good
    have retained : verified {input with claims := #[]} candidate records = true := by
      simp only [verified, Bool.and_eq_true] at good
      simp [verified, good.1.1, good.1.2]
    simpa only [finish, retained, Bool.true_eq, ite_true] using output
  · contradiction

/-- Generic supported recovery transfers to the actual original checker. The
checker truth must be derived from the original statement, not assumed as an
extractor-success event. No decoder or support certificate is replaced. -/
theorem decodedWithFinal_recover (input : Public) (records : List (Record input.config))
    (noWrap : input.config.logN - input.config.folds[0]! + input.config.rates[0]! ≤ 64)
    (checkOriginal : Witness input.config input.lanes → Bool) (w : Witness input.config input.lanes)
    (recovered : (decodeAndCheck input records noWrap).1 = some w)
    (checked : checkOriginal w = true) :
    decodedWithFinal input records noWrap checkOriginal = some w := by
  simp only [decodeAndCheck] at recovered
  obtain ⟨decoded, decodedOutput, certificate⟩ := Option.bind_eq_some_iff.mp recovered
  have retained := finish_claimless input _ records w certificate
  simp only [decodedWithFinal, decodedOutput, Option.bind, retained, checked,
    ite_true]

theorem decodedWithFinal_checked (input : Public) (records : List (Record input.config))
    (noWrap : input.config.logN - input.config.folds[0]! + input.config.rates[0]! ≤ 64)
    (checkOriginal : Witness input.config input.lanes → Bool) (w : Witness input.config input.lanes)
    (output : decodedWithFinal input records noWrap checkOriginal = some w) :
    checkOriginal w = true := by
  simp only [decodedWithFinal, Option.bind_eq_some_iff] at output
  obtain ⟨decoded, _, certified, _, checked⟩ := output
  split at checked
  · rename_i good
    have equal := Option.some.inj checked
    subst w
    exact good
  · contradiction

/-- The stop certificate enforces the actual fixed Root0 candidate relation;
checking unrelated public functionals alone is never considered extraction. -/
theorem decodedWithFinal_root (input : Public) (records : List (Record input.config))
    (noWrap : input.config.logN - input.config.folds[0]! + input.config.rates[0]! ≤ 64)
    (checkOriginal : Witness input.config input.lanes → Bool)
    (authenticated : ∀ record ∈ records, record.2 = input.root[record.1.val]!)
    (foldBound : input.config.folds[0]! ≤ input.config.logN)
    (laneBound : input.lanes ≤ laneCount input.config)
    (threshold : width input.config - 1 < ParameterBounds.threshold input.config 0)
    (w : Witness input.config input.lanes)
    (output : decodedWithFinal input records noWrap checkOriginal = some w) :
    Explains {input with claims := #[]} w := by
  simp only [decodedWithFinal, Option.bind_eq_some_iff] at output
  obtain ⟨decoded, _, certified, certificate, checked⟩ := output
  split at checked
  · have equal := Option.some.inj checked
    subst w
    exact finish_explains {input with claims := #[]} _ records authenticated
      foldBound laneBound noWrap threshold certified certificate
  · contradiction

/-- No accepted-prefix or unchecked-decoder stop is allowed. -/
def program (input : Public) (level : Fin input.config.folds.size)
    (tapes : List (Tape input.config))
    (noWrap : input.config.logN - input.config.folds[0]! + input.config.rates[0]! ≤ 64)
    (checkOriginal : Witness input.config input.lanes → Bool) : RewindProgram input.config input.lanes :=
  collectAcceptedProgram input level
    (input.config.logN - input.config.folds[0]! + input.config.rates[0]!) tapes
    (fun records => decodedWithFinal input (baseRecords records) noWrap checkOriginal)

abbrev Seed (profile : ParameterBounds.Profile) (rounds : Nat) :=
  RingPCSGame.Prefix × PCSRewindExtractor.Seed profile rounds

abbrev RepeatedSeed (profile : ParameterBounds.Profile) (attempts rounds : Nat) :=
  Fin attempts → Seed profile rounds

/-- One legal public-compression prefix and the real Root0 reset collector.
The mutable prover is replayed through the existing strict-prefix machine. -/
def runOne {m : Nat} (profile : ParameterBounds.Profile) (rounds lanes : Nat)
    (family : Fin m → RingPCSGame.FamilyClaim) (points : Array RingPCSGame.PointClaim)
    (anchorPoint : Array E) (anchorValue : E)
    (prepared : Prepared (ParameterBounds.config profile) lanes m family points anchorPoint anchorValue)
    (root : BaseOracle) (strategy : RingPCSGame.Prefix → Strategy) (seed : Seed profile rounds) :
    RewindResult (ParameterBounds.config profile) lanes :=
  let inp := OriginalClaimsChecker.input prepared root seed.1
  runRewind inp (strategy seed.1) (streamLength inp.config)
    (rounds * streamLength inp.config)
    (program inp (initialLevel profile) (seedTapes profile rounds inp rfl seed.2)
      (InitialCandidates.production_initial_facts profile).2.2.1
      (OriginalClaimsChecker.check prepared))

/-- This loop stops only at an actually source-checked output. Failed original
family checks consume their real trial and continue to the next fresh prefix. -/
def runAttempts {m : Nat} (profile : ParameterBounds.Profile) (rounds lanes : Nat)
    (family : Fin m → RingPCSGame.FamilyClaim) (points : Array RingPCSGame.PointClaim)
    (anchorPoint : Array E) (anchorValue : E)
    (prepared : Prepared (ParameterBounds.config profile) lanes m family points anchorPoint anchorValue)
    (root : BaseOracle) (strategy : RingPCSGame.Prefix → Strategy) :
    List (Seed profile rounds) → RewindResult (ParameterBounds.config profile) lanes
  | [] => ⟨none, 0⟩
  | seed :: rest =>
      let first := runOne profile rounds lanes family points anchorPoint anchorValue prepared root strategy seed
      match first.output with
      | some w => ⟨some w, first.responseCalls⟩
      | none =>
          let later := runAttempts profile rounds lanes family points anchorPoint anchorValue prepared root strategy rest
          ⟨later.output, first.responseCalls + later.responseCalls⟩

/-- Executable wrapper: fixed immutable originals, one cached preparation, and
fresh public-prefix plus actual legal collector randomness at each attempt.
Malformed source dimensions fail their literal preparation guard. -/
def run {m : Nat} (profile : ParameterBounds.Profile) (attempts rounds lanes : Nat)
    (family : Fin m → RingPCSGame.FamilyClaim) (points : Array RingPCSGame.PointClaim)
    (anchorPoint : Array E) (anchorValue : E) (root : BaseOracle)
    (strategy : RingPCSGame.Prefix → Strategy) (seed : RepeatedSeed profile attempts rounds) :
    RewindResult (ParameterBounds.config profile) lanes :=
  match prepare (ParameterBounds.config profile) lanes family points anchorPoint anchorValue with
  | none => ⟨none, 0⟩
  | some prepared => runAttempts profile rounds lanes family points anchorPoint anchorValue prepared root strategy (List.ofFn seed)

theorem program_run (prover : CommittedProver)
    (level : Fin prover.input.config.folds.size) (tapes : List (Tape prover.input.config))
    (noWrap : prover.input.config.logN - prover.input.config.folds[0]! + prover.input.config.rates[0]! ≤ 64)
    (checkOriginal : Witness prover.input.config prover.input.lanes → Bool) (maxReplay : Nat)
    (within : ∀ tape ∈ tapes,
      (visibleBatches prover.input.config tape.1 (challenges prover.input.config tape)).length ≤ maxReplay) :
    runRewind prover.input prover.respond maxReplay (collectionFuel prover.input tapes)
      (program prover.input level tapes noWrap checkOriginal) =
      ⟨decodedWithFinal prover.input (baseRecords (collectedRecords prover level
          (prover.input.config.logN - prover.input.config.folds[0]! + prover.input.config.rates[0]!) tapes))
        noWrap checkOriginal, collectionCalls prover.input tapes⟩ :=
  run_collectAcceptedProgram prover level _ maxReplay tapes within _

theorem runOne_value {m : Nat} (profile : ParameterBounds.Profile) (rounds lanes : Nat)
    (family : Fin m → RingPCSGame.FamilyClaim) (points : Array RingPCSGame.PointClaim)
    (anchorPoint : Array E) (anchorValue : E)
    (prepared : Prepared (ParameterBounds.config profile) lanes m family points anchorPoint anchorValue)
    (root : BaseOracle) (strategy : RingPCSGame.Prefix → Strategy) (seed : Seed profile rounds) :
    let inp := OriginalClaimsChecker.input prepared root seed.1
    let tapes := seedTapes profile rounds inp rfl seed.2
    runOne profile rounds lanes family points anchorPoint anchorValue prepared root strategy seed =
      ⟨decodedWithFinal inp (baseRecords (collectedRecords ⟨inp, strategy seed.1⟩
          (initialLevel profile) (initialDepth profile) tapes))
        (InitialCandidates.production_initial_facts profile).2.2.1
        (OriginalClaimsChecker.check prepared), collectionCalls inp tapes⟩ := by
  dsimp only
  unfold runOne
  dsimp only
  rw [← collectionFuel_ofFn (OriginalClaimsChecker.input prepared root seed.1) rounds
    (fun round => fullResetTape (OriginalClaimsChecker.input prepared root seed.1)
      seed.2.1 (initialLevel profile) (initialDepth profile) (initialChunks profile)
      (seed.2.2 round).1 (seed.2.2 round).2)]
  dsimp only [seedTapes]
  refine program_run ⟨OriginalClaimsChecker.input prepared root seed.1, strategy seed.1⟩
    (initialLevel profile) _ _ (OriginalClaimsChecker.check prepared) _ ?_
  intro tape member
  exact (visible_length _ _).le

theorem runOne_checked {m : Nat} (profile : ParameterBounds.Profile) (rounds lanes : Nat)
    (family : Fin m → RingPCSGame.FamilyClaim) (points : Array RingPCSGame.PointClaim)
    (anchorPoint : Array E) (anchorValue : E)
    (prepared : Prepared (ParameterBounds.config profile) lanes m family points anchorPoint anchorValue)
    (root : BaseOracle) (strategy : RingPCSGame.Prefix → Strategy) (seed : Seed profile rounds)
    (w : Witness (ParameterBounds.config profile) lanes)
    (output : (runOne profile rounds lanes family points anchorPoint anchorValue prepared root strategy seed).output = some w) :
    OriginalClaimsChecker.check prepared w = true := by
  rw [runOne_value] at output
  exact decodedWithFinal_checked (OriginalClaimsChecker.input prepared root seed.1)
    _ _ (OriginalClaimsChecker.check prepared) w output

theorem runOne_root {m : Nat} (profile : ParameterBounds.Profile) (rounds lanes : Nat)
    (family : Fin m → RingPCSGame.FamilyClaim) (points : Array RingPCSGame.PointClaim)
    (anchorPoint : Array E) (anchorValue : E)
    (prepared : Prepared (ParameterBounds.config profile) lanes m family points anchorPoint anchorValue)
    (root : BaseOracle) (strategy : RingPCSGame.Prefix → Strategy) (seed : Seed profile rounds)
    (laneBound : lanes ≤ laneCount (ParameterBounds.config profile))
    (w : Witness (ParameterBounds.config profile) lanes)
    (output : (runOne profile rounds lanes family points anchorPoint anchorValue prepared root strategy seed).output = some w) :
    Explains (ExecutionShapes.Input profile lanes root #[]) w := by
  rw [runOne_value] at output
  exact decodedWithFinal_root _ _ _ _
    (collected_base_authenticated profile lanes root
      (OriginalClaimsChecker.input prepared root seed.1).claims (strategy seed.1) _)
    (InitialCandidates.production_initial_facts profile).2.1 laneBound
    (InitialCandidates.production_initial_facts profile).2.2.2 w output

theorem runAttempts_checked {m : Nat} (profile : ParameterBounds.Profile) (rounds lanes : Nat)
    (family : Fin m → RingPCSGame.FamilyClaim) (points : Array RingPCSGame.PointClaim)
    (anchorPoint : Array E) (anchorValue : E)
    (prepared : Prepared (ParameterBounds.config profile) lanes m family points anchorPoint anchorValue)
    (root : BaseOracle) (strategy : RingPCSGame.Prefix → Strategy)
    (seeds : List (Seed profile rounds)) (w : Witness (ParameterBounds.config profile) lanes)
    (output : (runAttempts profile rounds lanes family points anchorPoint anchorValue prepared root strategy seeds).output = some w) :
    OriginalClaimsChecker.check prepared w = true := by
  induction seeds with
  | nil => simp [runAttempts] at output
  | cons seed rest ih =>
    dsimp only [runAttempts] at output
    cases first : (runOne profile rounds lanes family points anchorPoint anchorValue prepared root strategy seed).output with
    | none =>
      simp only [first] at output
      exact ih output
    | some candidate =>
      simp only [first] at output
      cases Option.some.inj output
      exact runOne_checked _ _ _ _ _ _ _ _ _ _ _ w first

theorem runAttempts_root {m : Nat} (profile : ParameterBounds.Profile) (rounds lanes : Nat)
    (family : Fin m → RingPCSGame.FamilyClaim) (points : Array RingPCSGame.PointClaim)
    (anchorPoint : Array E) (anchorValue : E)
    (prepared : Prepared (ParameterBounds.config profile) lanes m family points anchorPoint anchorValue)
    (root : BaseOracle) (strategy : RingPCSGame.Prefix → Strategy)
    (laneBound : lanes ≤ laneCount (ParameterBounds.config profile))
    (seeds : List (Seed profile rounds)) (w : Witness (ParameterBounds.config profile) lanes)
    (output : (runAttempts profile rounds lanes family points anchorPoint anchorValue prepared root strategy seeds).output = some w) :
    Explains (ExecutionShapes.Input profile lanes root #[]) w := by
  induction seeds with
  | nil => simp [runAttempts] at output
  | cons seed rest ih =>
    dsimp only [runAttempts] at output
    cases first : (runOne profile rounds lanes family points anchorPoint anchorValue prepared root strategy seed).output with
    | none =>
      simp only [first] at output
      exact ih output
    | some candidate =>
      simp only [first] at output
      cases Option.some.inj output
      exact runOne_root _ _ _ _ _ _ _ _ _ _ _ laneBound w first

/-- Actual source attempts have the same first-success output law as generic
attempts; a failed original checker never stops the outer loop. -/
theorem runAttempts_output {m : Nat} (profile : ParameterBounds.Profile) (rounds lanes : Nat)
    (family : Fin m → RingPCSGame.FamilyClaim) (points : Array RingPCSGame.PointClaim)
    (anchorPoint : Array E) (anchorValue : E)
    (prepared : Prepared (ParameterBounds.config profile) lanes m family points anchorPoint anchorValue)
    (root : BaseOracle) (strategy : RingPCSGame.Prefix → Strategy)
    (seeds : List (Seed profile rounds)) :
    (runAttempts profile rounds lanes family points anchorPoint anchorValue prepared root strategy seeds).output =
      firstOutput (seeds.map fun seed =>
        (runOne profile rounds lanes family points anchorPoint anchorValue prepared root strategy seed).output) := by
  induction seeds with
  | nil => rfl
  | cons seed rest ih =>
    dsimp only [runAttempts, List.map_cons]
    cases first : (runOne profile rounds lanes family points anchorPoint anchorValue prepared root strategy seed).output <;>
      simp only [List.map_cons, first, firstOutput, ih]

/-- A source run fails exactly when every actual independently seeded attempt
fails, including attempts rejected only by an original-family check. -/
theorem runAttempts_output_none_iff {m : Nat} (profile : ParameterBounds.Profile) (rounds lanes : Nat)
    (family : Fin m → RingPCSGame.FamilyClaim) (points : Array RingPCSGame.PointClaim)
    (anchorPoint : Array E) (anchorValue : E)
    (prepared : Prepared (ParameterBounds.config profile) lanes m family points anchorPoint anchorValue)
    (root : BaseOracle) (strategy : RingPCSGame.Prefix → Strategy)
    (seeds : List (Seed profile rounds)) :
    (runAttempts profile rounds lanes family points anchorPoint anchorValue prepared root strategy seeds).output = none ↔
      ∀ seed ∈ seeds,
        (runOne profile rounds lanes family points anchorPoint anchorValue prepared root strategy seed).output = none := by
  induction seeds with
  | nil => simp [runAttempts]
  | cons seed rest ih =>
    dsimp only [runAttempts]
    cases first : (runOne profile rounds lanes family points anchorPoint anchorValue prepared root strategy seed).output <;>
      simp [first, ih]

/-- Early success charges only executed attempts; otherwise each actual
collector's full response count is added, including failed original checks. -/
theorem runAttempts_responseCalls_le {m : Nat} (profile : ParameterBounds.Profile) (rounds lanes : Nat)
    (family : Fin m → RingPCSGame.FamilyClaim) (points : Array RingPCSGame.PointClaim)
    (anchorPoint : Array E) (anchorValue : E)
    (prepared : Prepared (ParameterBounds.config profile) lanes m family points anchorPoint anchorValue)
    (root : BaseOracle) (strategy : RingPCSGame.Prefix → Strategy)
    (seeds : List (Seed profile rounds)) :
    (runAttempts profile rounds lanes family points anchorPoint anchorValue prepared root strategy seeds).responseCalls ≤
      (seeds.map fun seed =>
        (runOne profile rounds lanes family points anchorPoint anchorValue prepared root strategy seed).responseCalls).sum := by
  induction seeds with
  | nil => simp [runAttempts]
  | cons seed rest ih =>
    dsimp only [runAttempts]
    cases first : (runOne profile rounds lanes family points anchorPoint anchorValue prepared root strategy seed).output <;>
      simp only [List.map_cons, List.sum_cons]
    · exact Nat.add_le_add_left ih _
    · exact Nat.le_add_right _ _

/-- If no output is returned, every attempt ran and the response count is
exactly the sum of the actual per-attempt collector counts. -/
theorem runAttempts_responseCalls_of_none {m : Nat} (profile : ParameterBounds.Profile) (rounds lanes : Nat)
    (family : Fin m → RingPCSGame.FamilyClaim) (points : Array RingPCSGame.PointClaim)
    (anchorPoint : Array E) (anchorValue : E)
    (prepared : Prepared (ParameterBounds.config profile) lanes m family points anchorPoint anchorValue)
    (root : BaseOracle) (strategy : RingPCSGame.Prefix → Strategy)
    (seeds : List (Seed profile rounds))
    (output : (runAttempts profile rounds lanes family points anchorPoint anchorValue prepared root strategy seeds).output = none) :
    (runAttempts profile rounds lanes family points anchorPoint anchorValue prepared root strategy seeds).responseCalls =
      (seeds.map fun seed =>
        (runOne profile rounds lanes family points anchorPoint anchorValue prepared root strategy seed).responseCalls).sum := by
  induction seeds with
  | nil => rfl
  | cons seed rest ih =>
    dsimp only [runAttempts] at output ⊢
    cases first : (runOne profile rounds lanes family points anchorPoint anchorValue prepared root strategy seed).output with
    | none =>
      simp only [first] at output ⊢
      simp only [List.map_cons, List.sum_cons, ih output]
    | some w => simp only [first, Option.some_ne_none] at output

#print axioms decodedWithFinal_checked
#print axioms decodedWithFinal_root
#print axioms program_run
#print axioms runOne_value
#print axioms runAttempts_checked
#print axioms runAttempts_root
#print axioms finish_claimless
#print axioms decodedWithFinal_recover
#print axioms runAttempts_output
#print axioms runAttempts_output_none_iff
#print axioms runAttempts_responseCalls_le
#print axioms runAttempts_responseCalls_of_none
end Whir.PCSRewindSource
