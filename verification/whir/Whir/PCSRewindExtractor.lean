import Whir.PCSRewindExtraction
import Whir.SupportedCandidateCancellation
import Whir.AuthenticatedResetSupport
import Whir.ResetAcceptanceAmplification
import Whir.SupportedCandidateParameters

/-! Root0 occupied-witness Gao decoding and deterministic verified output.
The input is a finite authenticated record list, not an ideal root preimage.
The executable extractor decodes only the live K lanes at Root0; the independent
extension-field GS backend is not invoked by this algorithm. The counter below
measures decoder field arithmetic only; whole-extractor accounting is supplied
by the value-connected instrumentation in `ExtractorArithmeticCost`. -/
namespace Whir.PCSRewindExtractor
open Concrete Protocol CausalGame KnowledgeExtraction SupportedCandidateExtraction

/-- Parse each recorded coordinate once, shared by all live decoder lanes. -/
def filledRecords (input : Public) (records : List (Record input.config)) :
    Array (Option (Array K)) :=
  Array.ofFn fun q : Fin (blockLength input.config) => RewindRowExtraction.lookup records q

def receivedLaneCached (input : Public) (filled : Array (Option (Array K)))
    (lane : Fin input.lanes) : Fin (blockLength input.config) → E := fun q =>
  match filled[q.val]! with
  | none => 0
  | some row => E.ofK (recordLane input.lanes row lane.val)

/-- All missing coordinates are zero-filled. This does not assume they agree
with the committed word: the precise error radius is a recovery hypothesis. -/
def receivedLane (input : Public) (records : List (Record input.config)) (lane : Fin input.lanes) :
    Fin (blockLength input.config) → E :=
  receivedLaneCached input (filledRecords input records) lane

/-- The actual instrumented Gao/novel/base-word pipeline is run once per live lane. -/
def decodeRecords (input : Public) (records : List (Record input.config))
    (noWrap : input.config.logN - input.config.folds[0]! + input.config.rates[0]! ≤ 64) :
    Option (Witness input.config input.lanes) × Nat :=
  let filled := filledRecords input records
  let decoded := Array.ofFn fun lane : Fin input.lanes =>
    ConcreteRowExtraction.countedExtractRow (input.config.logN - input.config.folds[0]!)
      input.config.rates[0]! noWrap
      ⟨Array.ofFn (receivedLaneCached input filled lane), by simp⟩
  (PCSRewindExtraction.assembleWitness input (fun lane =>
      (decoded[lane.val]'(by simp [decoded])).1),
    (decoded.map Prod.snd).toList.sum)

open scoped BigOperators in
/-- Value-connected field-arithmetic bound for decoding ALL occupied K lanes. -/
theorem decodeRecords_decoder_cost (input : Public) (records : List (Record input.config))
    (noWrap : input.config.logN - input.config.folds[0]! + input.config.rates[0]! ≤ 64)
    (redundancy : width input.config < blockLength input.config) :
    (decodeRecords input records noWrap).2 ≤
      input.lanes * ConcreteRowExtraction.rowArithmeticPolynomial (blockLength input.config) := by
  simp only [decodeRecords, Array.toList_map, Array.toList_ofFn, List.map_ofFn, List.sum_ofFn]
  calc
    _ ≤ ∑ _lane : Fin input.lanes,
      ConcreteRowExtraction.rowArithmeticPolynomial (blockLength input.config) := by
      apply Finset.sum_le_sum
      intro lane _
      exact ConcreteRowExtraction.countedExtractRow_polynomial_cost _ _ noWrap redundancy _
    _ = _ := by simp

/-- Recovery runs the decoder, rather than selecting a known witness. Its
radius premises describe the actual zero-filled received lanes. -/
theorem decodeRecords_recovers (input : Public) (records : List (Record input.config))
    (noWrap : input.config.logN - input.config.folds[0]! + input.config.rates[0]! ≤ 64)
    (redundancy : width input.config < blockLength input.config)
    (w : Witness input.config input.lanes)
    (radius : ∀ lane : Fin input.lanes,
      2 * hammingDist
        (Vector.mk (Array.ofFn (receivedLane input records lane)) (by simp) :
          Vector E (ConcreteRowExtraction.domain
            (input.config.logN - input.config.folds[0]! + input.config.rates[0]!) noWrap).n).get
        (fun i => (encode (input.config.logN - input.config.folds[0]!) input.config.rates[0]!
          ((PCSRewindExtraction.witnessLane input w lane).map E.ofK))[i.val]!) ≤
        blockLength input.config - width input.config) :
    (decodeRecords input records noWrap).1 = some w := by
  apply PCSRewindExtraction.assembleWitness_recovers
  intro lane
  simp only [Array.getElem_ofFn]
  exact (ConcreteRowExtraction.countedExtractRow_recovers _ _ noWrap redundancy
    (PCSRewindExtraction.witnessLane input w lane) (by simp [PCSRewindExtraction.witnessLane])
    _ (radius lane)).1

/-- Output is checked on a common authenticated coordinate certificate and ALL
original public claims. It is not checked against a recomputed honest root. -/
def decodeAndCheck (input : Public) (records : List (Record input.config))
    (noWrap : input.config.logN - input.config.folds[0]! + input.config.rates[0]! ≤ 64) :
    Option (Witness input.config input.lanes) × Nat :=
  let decoded := decodeRecords input records noWrap
  (decoded.1.bind (fun w =>
    SupportedCandidateExtraction.finish input (paddedWitness input.config input.lanes w) records),
    decoded.2)

/-- Guarded conversion of accepted extension rows back to literal base leaves. -/
def baseRow (row : Array E) : Option (Array K) :=
  if row.all (fun e => e.c1 == 0 && e.c2 == 0) then some (row.map E.c0) else none

def baseRecords {N : Nat} (records : List (Fin N × Array E)) : List (Fin N × Array K) :=
  records.filterMap (fun record => (baseRow record.2).map (record.1, ·))

theorem baseRow_sound (row : Array E) (base : Array K) (success : baseRow row = some base) :
    row = base.map E.ofK := by
  unfold baseRow at success
  split at success
  · rename_i guard
    have equal := Option.some.inj success
    rw [← equal, Array.map_map]
    apply Array.ext
    · simp
    · intro i hi hj
      have h := Array.all_eq_true.mp guard i hi
      simp only [Bool.and_eq_true, beq_iff_eq] at h
      cases entry : row[i]
      simp_all [E.ofK, Function.comp_apply]
  · contradiction

theorem baseRow_embedded (row : Array K) : baseRow (row.map E.ofK) = some row := by
  simp [baseRow, E.ofK, Array.map_map, Function.comp_def]

theorem baseRecords_authenticated {N : Nat} (root : BaseOracle)
    (records : List (Fin N × Array E))
    (authenticated : ∀ record ∈ records, record.2 = (root[record.1.val]!).map E.ofK) :
    ∀ record ∈ baseRecords records, record.2 = root[record.1.val]! := by
  intro record member
  obtain ⟨original, memberOriginal, projected⟩ := List.mem_filterMap.mp member
  rw [authenticated original memberOriginal, baseRow_embedded] at projected
  have equal := Option.some.inj projected
  subst record
  rfl

theorem decodeAndCheck_sound (input : Public) (records : List (Record input.config))
    (noWrap : input.config.logN - input.config.folds[0]! + input.config.rates[0]! ≤ 64)
    (authenticated : ∀ record ∈ records, record.2 = input.root[record.1.val]!)
    (foldBound : input.config.folds[0]! ≤ input.config.logN)
    (laneBound : input.lanes ≤ laneCount input.config)
    (threshold : width input.config - 1 < ParameterBounds.threshold input.config 0)
    (w : Witness input.config input.lanes)
    (output : (decodeAndCheck input records noWrap).1 = some w) : Explains input w := by
  simp only [decodeAndCheck] at output
  obtain ⟨decoded, _, checked⟩ := Option.bind_eq_some_iff.mp output
  exact finish_explains input _ records authenticated foldBound laneBound noWrap threshold w checked

/-- Every trial is run through the black box with strict-prefix replay. Only
fully accepted trials contribute rows to the candidate check. -/
def extractionProgram (input : Public) (level : Fin input.config.folds.size)
    (tapes : List (Tape input.config))
    (noWrap : input.config.logN - input.config.folds[0]! + input.config.rates[0]! ≤ 64) :
    RewindProgram input.config input.lanes :=
  AuthenticatedResetSupport.collectAcceptedProgram input level
    (input.config.logN - input.config.folds[0]! + input.config.rates[0]!) tapes
    (fun records => (decodeAndCheck input (baseRecords records) noWrap).1)

theorem extractionProgram_run (prover : CommittedProver)
    (level : Fin prover.input.config.folds.size) (tapes : List (Tape prover.input.config))
    (noWrap : prover.input.config.logN - prover.input.config.folds[0]! +
      prover.input.config.rates[0]! ≤ 64)
    (maxReplay : Nat)
    (within : ∀ tape ∈ tapes,
      (visibleBatches prover.input.config tape.1 (challenges prover.input.config tape)).length ≤ maxReplay) :
    runRewind prover.input prover.respond maxReplay
      (AuthenticatedResetSupport.collectionFuel prover.input tapes)
      (extractionProgram prover.input level tapes noWrap) =
      ⟨(decodeAndCheck prover.input (baseRecords (AuthenticatedResetSupport.collectedRecords
        prover level (prover.input.config.logN - prover.input.config.folds[0]! +
          prover.input.config.rates[0]!) tapes)) noWrap).1,
        AuthenticatedResetSupport.collectionCalls prover.input tapes⟩ :=
  AuthenticatedResetSupport.run_collectAcceptedProgram prover level _ maxReplay tapes within _

def initialLevel (profile : ParameterBounds.Profile) :
    Fin (ParameterBounds.config profile).folds.size :=
  ⟨0, by have valid := (ParameterBounds.production_config_valid profile).2.1; omega⟩

theorem collected_initial_embedded (profile : ParameterBounds.Profile) (lanes : Nat)
    (root : BaseOracle) (claims : Array Claim) (strategy : Strategy)
    (tapes : List (Tape (ParameterBounds.config profile))) :
    let input := ExecutionShapes.Input profile lanes root claims
    ∀ record ∈ AuthenticatedResetSupport.collectedRecords
      ⟨input, strategy⟩ (initialLevel profile)
      (input.config.logN - input.config.folds[0]! + input.config.rates[0]!) tapes,
      record.2 = (root[record.1.val]!).map E.ofK := by
  dsimp only
  intro record member
  obtain ⟨tape, _, member⟩ := List.mem_flatMap.mp member
  have shape : (CausalExecution.foldAt (ExecutionShapes.Input profile lanes root claims)
      strategy tape (initialLevel profile) (ParameterBounds.config profile).folds[0]!).n +
      (ParameterBounds.config profile).rates[0]! =
      (ParameterBounds.config profile).logN - (ParameterBounds.config profile).folds[0]! +
        (ParameterBounds.config profile).rates[0]! := by
    have dimensions := (ExecutionShapes.foldAt_shape profile lanes root claims strategy tape
      (initialLevel profile) (ParameterBounds.config profile).folds[0]! (by rfl)).1
    simp only [initialLevel, Nat.sub_self, Nat.add_zero] at dimensions
    simp only [initialLevel]
    rw [dimensions, (InitialCandidates.production_initial_facts profile).1]
  have authentic := AuthenticatedResetSupport.trialRecords_authenticated
    ⟨ExecutionShapes.Input profile lanes root claims, strategy⟩ tape (initialLevel profile) _ shape record member
  change record.2 = (liftRoot root)[record.1.val]! at authentic
  rw [authentic]
  by_cases within : record.1.val < root.size
  · simp [liftRoot, getElem!_pos, within]
  · simp [liftRoot, getElem!_neg, within]
    change (#[] : Array E) = (#[] : Array K).map E.ofK
    simp

theorem collected_base_authenticated (profile : ParameterBounds.Profile) (lanes : Nat)
    (root : BaseOracle) (claims : Array Claim) (strategy : Strategy)
    (tapes : List (Tape (ParameterBounds.config profile))) :
    let input := ExecutionShapes.Input profile lanes root claims
    ∀ record ∈ baseRecords (AuthenticatedResetSupport.collectedRecords
      ⟨input, strategy⟩ (initialLevel profile)
      (input.config.logN - input.config.folds[0]! + input.config.rates[0]!) tapes),
      record.2 = root[record.1.val]! := by
  dsimp only
  exact baseRecords_authenticated root _ (collected_initial_embedded profile lanes root claims strategy tapes)


def streamLength (c : Config) : Nat :=
  1 + ((List.range c.folds.size).map (fun i => c.folds[i]! + oodCount c i + 1)).sum +
    (c.logN - c.folds.toList.sum - 1)

theorem visible_length (c : Config) (tape : Tape c) :
    (visibleBatches c tape.1 (challenges c tape)).length = streamLength c := by
  simp only [visibleBatches, List.length_append, List.length_singleton, List.length_ofFn,
    List.length_flatMap, challenges, Array.size_ofFn]
  congr 2
  congr 1
  apply List.map_congr_left
  intro i hi
  have bound : i < c.folds.size := List.mem_range.mp hi
  simp [levelBatches, getElem!_pos, bound, Nat.add_assoc]

deriving instance DecidableEq for Config

abbrev initialDepth (profile : ParameterBounds.Profile) :=
  (ParameterBounds.config profile).logN - (ParameterBounds.config profile).folds[0]! +
    (ParameterBounds.config profile).rates[0]!

theorem initialChunks (profile : ParameterBounds.Profile) :
    queryChunks (ParameterBounds.config profile) (initialLevel profile) =
      (((ParameterBounds.config profile).queries[0]! + 192 / initialDepth profile - 1) /
        (192 / initialDepth profile)) := by
  simp only [queryChunks, initialLevel]
  rw [(InitialCandidates.production_initial_facts profile).1]

abbrev TrialSeed (profile : ParameterBounds.Profile) :=
  RewindCoverage.QueryTape (initialDepth profile) (ParameterBounds.config profile).queries[0]! ×
    (E × Tape (ParameterBounds.config profile))

abbrev Seed (profile : ParameterBounds.Profile) (rounds : Nat) :=
  Tape (ParameterBounds.config profile) × (Fin rounds → TrialSeed profile)

/-- Uses the collector's exact stratified-query and independent full-suffix
sampling law, including the invisible final verifier challenge. -/
def seedTapes (profile : ParameterBounds.Profile) (rounds : Nat) (input : Public)
    (equal : input.config = ParameterBounds.config profile) (seed : Seed profile rounds) :
    List (Tape input.config) :=
  equal.symm ▸ (List.ofFn fun round => AuthenticatedResetSupport.fullResetTape
    ⟨ParameterBounds.config profile, input.lanes, input.root, input.claims⟩ seed.1
    (initialLevel profile) (initialDepth profile) (initialChunks profile)
    (seed.2 round).1 (seed.2 round).2)

/-- Actual finite-profile extractor. Other configurations are rejected. Every
query is a legal full trial against the fixed committed public input/prover. -/
def extractor (profile : ParameterBounds.Profile) (rounds : Nat) : Extractor (Seed profile rounds) where
  program input seed :=
    if equal : input.config = ParameterBounds.config profile then
      extractionProgram input (equal.symm ▸ initialLevel profile)
        (seedTapes profile rounds input equal seed) (by
          simpa only [equal] using (InitialCandidates.production_initial_facts profile).2.2.1)
    else .finish none
  rewindRounds := rounds * streamLength (ParameterBounds.config profile)
  maxReplay := streamLength (ParameterBounds.config profile)

theorem extractor_program (profile : ParameterBounds.Profile) (rounds lanes : Nat)
    (root : BaseOracle) (claims : Array Claim) (seed : Seed profile rounds) :
    let input := ExecutionShapes.Input profile lanes root claims
    (extractor profile rounds).program input seed =
      extractionProgram input (initialLevel profile) (seedTapes profile rounds input rfl seed)
        (InitialCandidates.production_initial_facts profile).2.2.1 := by
  simp only [extractor]
  rfl

theorem collectionFuel_ofFn (input : Public) (rounds : Nat) (tapes : Fin rounds → Tape input.config) :
    AuthenticatedResetSupport.collectionFuel input (List.ofFn tapes) =
      rounds * streamLength input.config := by
  simp [AuthenticatedResetSupport.collectionFuel, visible_length, List.map_ofFn, List.sum_ofFn]

theorem extractor_run (profile : ParameterBounds.Profile) (rounds lanes : Nat)
    (root : BaseOracle) (claims : Array Claim) (strategy : Strategy) (seed : Seed profile rounds) :
    let input := ExecutionShapes.Input profile lanes root claims
    let tapes := seedTapes profile rounds input rfl seed
    runRewind input strategy (extractor profile rounds).maxReplay (extractor profile rounds).rewindRounds
      ((extractor profile rounds).program input seed) =
      ⟨(decodeAndCheck input (baseRecords (AuthenticatedResetSupport.collectedRecords
        ⟨input, strategy⟩ (initialLevel profile)
        (input.config.logN - input.config.folds[0]! + input.config.rates[0]!) tapes))
          (InitialCandidates.production_initial_facts profile).2.2.1).1,
        AuthenticatedResetSupport.collectionCalls input tapes⟩ := by
  dsimp only
  rw [extractor_program]
  change runRewind _ _ (streamLength (ParameterBounds.config profile))
    (rounds * streamLength (ParameterBounds.config profile)) _ = _
  rw [← collectionFuel_ofFn (ExecutionShapes.Input profile lanes root claims) rounds
    (fun round => AuthenticatedResetSupport.fullResetTape
      (ExecutionShapes.Input profile lanes root claims) seed.1 (initialLevel profile)
      (initialDepth profile) (initialChunks profile) (seed.2 round).1 (seed.2 round).2)]
  dsimp only [seedTapes]
  apply extractionProgram_run (prover := ⟨ExecutionShapes.Input profile lanes root claims, strategy⟩)
  intro tape member
  exact (visible_length _ _).le

theorem extractor_output_explains (profile : ParameterBounds.Profile) (rounds lanes : Nat)
    (root : BaseOracle) (claims : Array Claim) (strategy : Strategy) (seed : Seed profile rounds)
    (laneBound : lanes ≤ 2 ^ (ParameterBounds.config profile).folds[0]!)
    (w : Witness (ParameterBounds.config profile) lanes)
    (output : (runRewind (ExecutionShapes.Input profile lanes root claims) strategy
      (extractor profile rounds).maxReplay (extractor profile rounds).rewindRounds
      ((extractor profile rounds).program (ExecutionShapes.Input profile lanes root claims) seed)).output = some w) :
    Explains (ExecutionShapes.Input profile lanes root claims) w := by
  rw [extractor_run] at output
  exact decodeAndCheck_sound _ _ _ (collected_base_authenticated profile lanes root claims strategy _)
    (InitialCandidates.production_initial_facts profile).2.1 laneBound
    (InitialCandidates.production_initial_facts profile).2.2.2 w output

#print axioms baseRow_sound
end Whir.PCSRewindExtractor
