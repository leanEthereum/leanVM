import Whir.PCSRewindExtractor

/-! Prefix amplification is implemented inside the bounded black-box machine.
Attempts stop only on a decoded-and-certified witness, never merely acceptance.
All prefix/suffix samples have the actual collector's finite product law. -/
namespace Whir.PCSRewindExtractor
open Concrete Protocol CausalGame KnowledgeExtraction AuthenticatedResetSupport

set_option maxHeartbeats 4000000

/-- Generalize the accepted-trial collector's finishing continuation so an
unsuccessful prefix can continue to another independent prefix. -/
def continueCollect (input : Public) (level : Fin input.config.folds.size) (depth : Nat) :
    List (Tape input.config) →
      (List (Fin (2 ^ depth) × Array E) → RewindProgram input.config input.lanes) →
        RewindProgram input.config input.lanes
  | [], finish => finish []
  | tape :: tapes, finish =>
      trialProgram input [] (visibleBatches input.config tape.1 (challenges input.config tape))
        (fun replies => continueCollect input level depth tapes
          (fun records => finish (acceptedRecords input tape level depth replies ++ records)))

theorem run_continueCollect (prover : CommittedProver)
    (level : Fin prover.input.config.folds.size) (depth maxReplay extra : Nat)
    (tapes : List (Tape prover.input.config))
    (within : ∀ tape ∈ tapes,
      (visibleBatches prover.input.config tape.1 (challenges prover.input.config tape)).length ≤ maxReplay)
    (finish : List (Fin (2 ^ depth) × Array E) → RewindProgram prover.input.config prover.input.lanes) :
    runRewind prover.input prover.respond maxReplay (collectionFuel prover.input tapes + extra)
      (continueCollect prover.input level depth tapes finish) =
      let result := runRewind prover.input prover.respond maxReplay extra
        (finish (collectedRecords prover level depth tapes))
      ⟨result.output, result.responseCalls + collectionCalls prover.input tapes⟩ := by
  induction tapes generalizing finish with
  | nil => simp [continueCollect, collectionFuel, collectionCalls, collectedRecords]
  | cons tape tapes ih =>
    simp only [continueCollect, collectionFuel, List.map_cons, List.sum_cons, Nat.add_assoc]
    rw [run_trialProgram _ _ [] _ maxReplay _ (by simpa using within tape (by simp))]
    dsimp only
    erw [ih (fun t ht => within t (by simp [ht]))]
    simp [replayPast, collectedRecords, trialRecords, collectionCalls, Nat.add_assoc, Nat.add_comm]

def repeatedProgram (profile : ParameterBounds.Profile) (rounds : Nat) (input : Public)
    (equal : input.config = ParameterBounds.config profile) :
    List (Seed profile rounds) → RewindProgram input.config input.lanes
  | [] => .finish none
  | seed :: seeds =>
      continueCollect input (equal.symm ▸ initialLevel profile)
        (input.config.logN - input.config.folds[0]! + input.config.rates[0]!)
        (seedTapes profile rounds input equal seed) (fun records =>
          match (decodeAndCheck input (baseRecords records) (by
            simpa only [equal] using (InitialCandidates.production_initial_facts profile).2.2.1)).1 with
          | some witness => .finish (some witness)
          | none => repeatedProgram profile rounds input equal seeds)

abbrev RepeatedSeed (profile : ParameterBounds.Profile) (attempts rounds : Nat) :=
  Fin attempts → Seed profile rounds

def repeatedExtractor (profile : ParameterBounds.Profile) (attempts rounds : Nat) :
    Extractor (RepeatedSeed profile attempts rounds) where
  program input seed :=
    if equal : input.config = ParameterBounds.config profile then
      repeatedProgram profile rounds input equal (List.ofFn seed)
    else .finish none
  rewindRounds := attempts * (rounds * streamLength (ParameterBounds.config profile))
  maxReplay := streamLength (ParameterBounds.config profile)

def firstOutput {α : Type*} : List (Option α) → Option α
  | [] => none
  | some value :: _ => some value
  | none :: rest => firstOutput rest

theorem repeatedProgram_output (profile : ParameterBounds.Profile) (rounds lanes : Nat)
    (root : BaseOracle) (claims : Array Claim) (strategy : Strategy)
    (seeds : List (Seed profile rounds)) :
    let input := ExecutionShapes.Input profile lanes root claims
    (runRewind input strategy (streamLength (ParameterBounds.config profile))
      (seeds.length * (rounds * streamLength (ParameterBounds.config profile)))
      (repeatedProgram profile rounds input rfl seeds)).output =
      firstOutput (seeds.map (fun seed =>
        (runRewind input strategy (extractor profile rounds).maxReplay
          (extractor profile rounds).rewindRounds ((extractor profile rounds).program input seed)).output)) := by
  dsimp only
  induction seeds with
  | nil => simp [repeatedProgram, runRewind, firstOutput]
  | cons seed seeds ih =>
    let input := ExecutionShapes.Input profile lanes root claims
    have fuel : collectionFuel input (seedTapes profile rounds input rfl seed) =
        rounds * streamLength (ParameterBounds.config profile) :=
      collectionFuel_ofFn _ _ _
    simp only [repeatedProgram, List.length_cons, Nat.succ_mul, List.map_cons]
    rw [Nat.add_comm, ← fuel, run_continueCollect
      (prover := ⟨input, strategy⟩) (within := fun tape _ => (visible_length _ _).le)]
    rw [extractor_run]
    dsimp only
    cases decoded : (decodeAndCheck input (baseRecords (collectedRecords ⟨input, strategy⟩
        (initialLevel profile) (initialDepth profile) (seedTapes profile rounds input rfl seed)))
        (InitialCandidates.production_initial_facts profile).2.2.1).1 with
    | none => simpa only [decoded, firstOutput, fuel] using ih
    | some witness => simp only [runRewind, firstOutput]

theorem repeatedExtractor_output (profile : ParameterBounds.Profile) (attempts rounds lanes : Nat)
    (root : BaseOracle) (claims : Array Claim) (strategy : Strategy)
    (seed : RepeatedSeed profile attempts rounds) :
    let input := ExecutionShapes.Input profile lanes root claims
    (runRewind input strategy (repeatedExtractor profile attempts rounds).maxReplay
      (repeatedExtractor profile attempts rounds).rewindRounds
      ((repeatedExtractor profile attempts rounds).program input seed)).output =
      firstOutput (List.ofFn fun i =>
        (runRewind input strategy (extractor profile rounds).maxReplay (extractor profile rounds).rewindRounds
          ((extractor profile rounds).program input (seed i))).output) := by
  simpa [repeatedExtractor, List.map_ofFn, Function.comp_def] using
    repeatedProgram_output profile rounds lanes root claims strategy (List.ofFn seed)

/-- Every actual black-box response call, including rejected attempts and all
strict-prefix replays, is charged by the concrete repeated extractor. -/
theorem repeatedExtractor_responseCalls (profile : ParameterBounds.Profile) (attempts rounds : Nat)
    (prover : CommittedProver) (seed : RepeatedSeed profile attempts rounds) :
    (runRewind prover.input prover.respond (repeatedExtractor profile attempts rounds).maxReplay
      (repeatedExtractor profile attempts rounds).rewindRounds
      ((repeatedExtractor profile attempts rounds).program prover.input seed)).responseCalls ≤
      attempts * (rounds * streamLength (ParameterBounds.config profile)) *
        (streamLength (ParameterBounds.config profile) + 1) :=
  responseCalls_le _ _ _ _ _

theorem firstOutput_some_mem {α : Type*} (outputs : List (Option α)) (w : α)
    (output : firstOutput outputs = some w) : some w ∈ outputs := by
  induction outputs with
  | nil => simp [firstOutput] at output
  | cons value rest ih =>
    cases value with
    | none => exact List.mem_cons_of_mem _ (ih output)
    | some value =>
      have equal : value = w := Option.some.inj output
      simp [equal]

theorem repeatedExtractor_output_explains (profile : ParameterBounds.Profile)
    (attempts rounds lanes : Nat) (root : BaseOracle) (claims : Array Claim)
    (strategy : Strategy) (seed : RepeatedSeed profile attempts rounds)
    (laneBound : lanes ≤ 2 ^ (ParameterBounds.config profile).folds[0]!)
    (w : Witness (ParameterBounds.config profile) lanes)
    (output : (runRewind (ExecutionShapes.Input profile lanes root claims) strategy
      (repeatedExtractor profile attempts rounds).maxReplay
      (repeatedExtractor profile attempts rounds).rewindRounds
      ((repeatedExtractor profile attempts rounds).program
        (ExecutionShapes.Input profile lanes root claims) seed)).output = some w) :
    Explains (ExecutionShapes.Input profile lanes root claims) w := by
  rw [repeatedExtractor_output] at output
  obtain ⟨attempt, accepted⟩ := List.mem_ofFn.mp (firstOutput_some_mem _ w output)
  exact extractor_output_explains profile rounds lanes root claims strategy
    (seed attempt) laneBound w accepted

/-- Every original public functional is preserved, including the input anchor
functional whenever it is present among the original claims. -/
theorem repeatedExtractor_original_claim (profile : ParameterBounds.Profile)
    (attempts rounds lanes : Nat) (root : BaseOracle) (claims : Array Claim)
    (strategy : Strategy) (seed : RepeatedSeed profile attempts rounds)
    (laneBound : lanes ≤ 2 ^ (ParameterBounds.config profile).folds[0]!)
    (w : Witness (ParameterBounds.config profile) lanes)
    (output : (runRewind (ExecutionShapes.Input profile lanes root claims) strategy
      (repeatedExtractor profile attempts rounds).maxReplay
      (repeatedExtractor profile attempts rounds).rewindRounds
      ((repeatedExtractor profile attempts rounds).program
        (ExecutionShapes.Input profile lanes root claims) seed)).output = some w)
    (original : Claim) (member : original ∈ claims.toList) :
    dot (paddedWitness (ParameterBounds.config profile) lanes w) original.weight = original.value :=
  (repeatedExtractor_output_explains profile attempts rounds lanes root claims strategy seed laneBound w output).2
    original member

#print axioms run_continueCollect
#print axioms repeatedExtractor_responseCalls
#print axioms repeatedExtractor_output_explains
end Whir.PCSRewindExtractor
