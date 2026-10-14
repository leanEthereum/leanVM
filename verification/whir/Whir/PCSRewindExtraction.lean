import Whir.RewindRowExtraction
import Whir.RewindCoverage
import Whir.UniqueRadiusSampling

/-! Fixed-public, occupied-lane extraction using only replayed query replies. The root in the ideal public type is never read by this algorithm. Reset availability, authenticated response availability, and an initial common-lane unique radius are distinct access/proximity obligations. The existing interactive list-loss theorem supplies existence of an explaining list member, not this stronger radius. -/
namespace Whir.PCSRewindExtraction
open Concrete Protocol CausalGame CausalProbability KnowledgeExtraction RewindRowExtraction
set_option maxHeartbeats 800000

abbrev rowWidth (input : Public) := 2 ^ (input.config.logN - input.config.folds[0]!)

def witnessLane (input : Public) (w : Witness input.config input.lanes)
    (lane : Fin input.lanes) : Array K :=
  Array.ofFn fun j : Fin (rowWidth input) => w ⟨lane.val * rowWidth input + j.val, by
    have positive : 0 < rowWidth input := by unfold rowWidth; positivity
    have bound := lane.isLt
    have jb := j.isLt
    have scaled := Nat.mul_le_mul_right (rowWidth input) (Nat.succ_le_of_lt bound)
    nlinarith⟩

/-- Assembly fails on missing or wrongly sized decoded lanes. No padded or invented witness coefficients are emitted. -/
def assembleWitness (input : Public) (results : Fin input.lanes → Option (Array K)) :
    Option (Witness input.config input.lanes) :=
  if complete : ∀ lane, (results lane).isSome = true ∧
      (results lane).map Array.size = some (rowWidth input) then
    some fun j =>
      let lane : Fin input.lanes := ⟨j.val / rowWidth input, by
        have positive : 0 < rowWidth input := by unfold rowWidth; positivity
        exact (Nat.div_lt_iff_lt_mul positive).mpr j.isLt⟩
      ((results lane).get (complete lane).1)[j.val % rowWidth input]!
  else none

theorem assembleWitness_recovers (input : Public) (w : Witness input.config input.lanes)
    (results : Fin input.lanes → Option (Array K))
    (correct : ∀ lane, results lane = some (witnessLane input w lane)) :
    assembleWitness input results = some w := by
  have complete : ∀ lane, (results lane).isSome = true ∧
      (results lane).map Array.size = some (rowWidth input) := by
    intro lane
    simp [correct lane, witnessLane]
  simp only [assembleWitness, dite_eq_left complete]
  congr 1
  funext j
  have positive : 0 < rowWidth input := by unfold rowWidth; positivity
  simp [correct, witnessLane, getElem!_pos, Nat.mod_lt _ positive,
    Nat.div_add_mod']

def decodeWitness (input : Public) (requests : List QueryRequest) (answers : List Reply)
    (noWrap : input.config.logN - input.config.folds[0]! + input.config.rates[0]! ≤ 64) :
    Option (Witness input.config input.lanes) :=
  let decoded := Array.ofFn fun lane : Fin input.lanes =>
    extractReplies (input.config.logN - input.config.folds[0]!)
      input.config.rates[0]! noWrap input.config.queries[0]!
      (input.lanes - 1 - lane.val) requests answers
  assembleWitness input fun lane => decoded[lane.val]'(by
    simpa only [decoded, Array.size_ofFn] using lane.isLt)

/-- Every occupied lane is decoded from the same collected replies. Leaf lanes are reversed exactly as in the verifier's initial lane layout. -/
def extractWitness (prover : CommittedProver) (tape : Tape prover.input.config)
    (level : Fin prover.input.config.folds.size) (_initialLevel : level.val = 0) (rounds : Nat)
    (seed : Fin rounds → Sample (.query level))
    (noWrap : prover.input.config.logN - prover.input.config.folds[0]! +
      prover.input.config.rates[0]! ≤ 64) : Option (Witness prover.input.config prover.input.lanes) :=
  let requests := List.ofFn fun round => resetRequest prover.input level (seed round)
  let answers := (collectResets prover tape level rounds seed).replies
  decodeWitness prover.input requests answers noWrap

/-- The implemented whole occupied-witness extractor composes the supported-row decoder outputs. This interface exposes the exact missing common-lane recovery obligation rather than assuming PCS soundness. -/
theorem extractWitness_recovers (prover : CommittedProver) (tape : Tape prover.input.config)
    (level : Fin prover.input.config.folds.size) (initialLevel : level.val = 0) (rounds : Nat)
    (seed : Fin rounds → Sample (.query level))
    (noWrap : prover.input.config.logN - prover.input.config.folds[0]! +
      prover.input.config.rates[0]! ≤ 64)
    (w : Witness prover.input.config prover.input.lanes)
    (lanesRecovered : ∀ lane : Fin prover.input.lanes,
      extractReplies (prover.input.config.logN - prover.input.config.folds[0]!)
        prover.input.config.rates[0]! noWrap prover.input.config.queries[0]!
        (prover.input.lanes - 1 - lane.val)
        (List.ofFn fun round => resetRequest prover.input level (seed round))
        (collectResets prover tape level rounds seed).replies =
          some (witnessLane prover.input w lane)) :
    extractWitness prover tape level initialLevel rounds seed noWrap = some w := by
  apply assembleWitness_recovers
  intro lane
  simpa only [Array.getElem_ofFn] using lanesRecovered lane

/-- The same algorithm as a bounded rewind-machine program. The finishing continuation is given only response records. -/
def extractionProgram (input : Public) (tape : Tape input.config)
    (level : Fin input.config.folds.size) (_initialLevel : level.val = 0) (rounds : Nat)
    (seed : Fin rounds → Sample (.query level))
    (noWrap : input.config.logN - input.config.folds[0]! + input.config.rates[0]! ≤ 64) :
    RewindProgram input.config input.lanes :=
  let requests := List.ofFn fun round => resetRequest input level (seed round)
  collectProgram input (queryPrefix input tape level) requests
    (fun answers => decodeWitness input requests answers noWrap)

theorem extractionProgram_run (prover : CommittedProver) (tape : Tape prover.input.config)
    (level : Fin prover.input.config.folds.size) (initialLevel : level.val = 0) (rounds : Nat)
    (seed : Fin rounds → Sample (.query level))
    (noWrap : prover.input.config.logN - prover.input.config.folds[0]! +
      prover.input.config.rates[0]! ≤ 64) :
    runRewind prover.input prover.respond (queryPrefix prover.input tape level).length rounds
      (extractionProgram prover.input tape level initialLevel rounds seed noWrap) =
        ⟨extractWitness prover tape level initialLevel rounds seed noWrap,
          rounds * ((queryPrefix prover.input tape level).length + 1)⟩ := by
  have replay := run_collectProgram prover.input prover.respond
    (queryPrefix prover.input tape level) (queryPrefix prover.input tape level).length le_rfl
    (List.ofFn fun round => resetRequest prover.input level (seed round))
    (fun answers => decodeWitness prover.input
      (List.ofFn fun round => resetRequest prover.input level (seed round)) answers noWrap)
  simpa only [List.length_ofFn, extractionProgram, extractWitness, collectResets,
    collect_responseCalls] using replay

/-- Actual acceptance without an explaining output is covered by an existing causal bad prefix or by failure of the stated occupied-lane recovery condition. The second event is not bounded by the existing list-loss soundness theorem. -/
theorem accepted_without_output_cover (p : ParameterBounds.Profile) (lanes : Nat)
    (root : BaseOracle) (claims : Array Claim) (strategy : Strategy)
    (tape : Tape (ParameterBounds.config p))
    (output : Option (Witness (ParameterBounds.config p) lanes))
    (accepted : experiment (ExecutionShapes.Input p lanes root claims) strategy tape = true)
    (failed : ¬ ∃ w, output = some w ∧ Explains (ExecutionShapes.Input p lanes root claims) w) :
    (∃ q, CausalBadEvents.Bad (ExecutionShapes.Input p lanes root claims) strategy q tape) ∨
      (∃ w, Explains (ExecutionShapes.Input p lanes root claims) w ∧ output ≠ some w) := by
  classical
  by_cases bad : ∃ q, CausalBadEvents.Bad (ExecutionShapes.Input p lanes root claims) strategy q tape
  · exact Or.inl bad
  · obtain ⟨w, explains⟩ := accepted_safe_explanation p lanes root claims strategy tape accepted
      (fun q event => bad ⟨q, event⟩)
    exact Or.inr ⟨w, explains, fun equal => failed ⟨w, equal, explains⟩⟩

/-- The unexplained-acceptance event for the implemented extractor, not an arbitrary output observer. The remaining term is concrete supported-row decoding failure for an explaining commitment-time witness. -/
theorem accepted_without_extracted_witness_cover (p : ParameterBounds.Profile) (lanes : Nat)
    (root : BaseOracle) (claims : Array Claim) (strategy : Strategy)
    (tape : Tape (ParameterBounds.config p))
    (level : Fin (ParameterBounds.config p).folds.size) (initialLevel : level.val = 0)
    (rounds : Nat) (seed : Fin rounds → Sample (.query level))
    (noWrap : (ParameterBounds.config p).logN - (ParameterBounds.config p).folds[0]! +
      (ParameterBounds.config p).rates[0]! ≤ 64)
    (accepted : experiment (ExecutionShapes.Input p lanes root claims) strategy tape = true)
    (failed : ¬ ∃ w,
      extractWitness ⟨ExecutionShapes.Input p lanes root claims, strategy⟩ tape
        level initialLevel rounds seed noWrap = some w ∧
      Explains (ExecutionShapes.Input p lanes root claims) w) :
    (∃ q, CausalBadEvents.Bad (ExecutionShapes.Input p lanes root claims) strategy q tape) ∨
      ∃ w lane, Explains (ExecutionShapes.Input p lanes root claims) w ∧
        extractReplies ((ParameterBounds.config p).logN - (ParameterBounds.config p).folds[0]!)
          (ParameterBounds.config p).rates[0]! noWrap (ParameterBounds.config p).queries[0]!
          (lanes - 1 - lane.val)
          (List.ofFn fun round => resetRequest (ExecutionShapes.Input p lanes root claims) level (seed round))
          (collectResets ⟨ExecutionShapes.Input p lanes root claims, strategy⟩ tape level rounds seed).replies ≠
            some (witnessLane (ExecutionShapes.Input p lanes root claims) w lane) := by
  classical
  obtain bad | ⟨w, explains, missed⟩ := accepted_without_output_cover
    p lanes root claims strategy tape _ accepted failed
  · exact Or.inl bad
  · right
    have notRecovered : ¬ ∀ lane : Fin lanes,
        extractReplies ((ParameterBounds.config p).logN - (ParameterBounds.config p).folds[0]!)
          (ParameterBounds.config p).rates[0]! noWrap (ParameterBounds.config p).queries[0]!
          (lanes - 1 - lane.val)
          (List.ofFn fun round => resetRequest (ExecutionShapes.Input p lanes root claims) level (seed round))
          (collectResets ⟨ExecutionShapes.Input p lanes root claims, strategy⟩ tape level rounds seed).replies =
            some (witnessLane (ExecutionShapes.Input p lanes root claims) w lane) :=
      fun recovered => by
        have recoveredFull := extractWitness_recovers
          ⟨ExecutionShapes.Input p lanes root claims, strategy⟩ tape level initialLevel
          rounds seed noWrap w recovered
        exact missed recoveredFull
    push Not at notRecovered
    obtain ⟨lane, failedLane⟩ := notRecovered
    exact ⟨w, lane, explains, failedLane⟩

#print axioms assembleWitness_recovers
#print axioms extractWitness_recovers
#print axioms extractionProgram_run
#print axioms accepted_without_output_cover
#print axioms accepted_without_extracted_witness_cover

end Whir.PCSRewindExtraction
