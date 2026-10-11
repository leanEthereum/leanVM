import Whir.PCSRewindKnowledgeHeavy
import Whir.PCSRewindSourceRelation
import Whir.CountedCandidateCheckOriginalResources

/-! Straight-line Root0 extraction. Root rows are indexed directly: no record
collection, reset, strategy, or verifier randomness is an input. The common
support check uses the unchanged dense encoder and the original list threshold.
Malformed physical roots and public metadata are rejected before decoding. -/
namespace Whir.PCSRoundByRoundSource
open Concrete Protocol CausalGame KnowledgeExtraction SupportedCandidateExtraction
open scoped BigOperators
set_option maxHeartbeats 4000000

/-- Literal physical availability, not equality with an honest commitment. -/
def FullRoot (c : Config) (lanes : Nat) (root : BaseOracle) : Prop :=
  root.size = blockLength c ∧ ∀ i : Fin root.size, root[i].size = lanes
instance (c : Config) (lanes : Nat) (root : BaseOracle) : Decidable (FullRoot c lanes root) := by
  unfold FullRoot
  infer_instance

def receivedLane (input : Public) (lane : Fin input.lanes) : Fin (blockLength input.config) → E :=
  fun q => E.ofK (recordLane input.lanes input.root[q.val]! lane.val)

/-- One counted Gao/novel/base-word run per occupied lane; only lane vectors
are materialized. Root leaves are neither copied nor searched. -/
def decodeRoot (input : Public)
    (noWrap : input.config.logN - input.config.folds[0]! + input.config.rates[0]! ≤ 64) :
    Option (Witness input.config input.lanes) × Nat :=
  let decoded := Array.ofFn fun lane : Fin input.lanes =>
    ConcreteRowExtraction.countedExtractRow (input.config.logN - input.config.folds[0]!)
      input.config.rates[0]! noWrap ⟨Array.ofFn (receivedLane input lane), by simp⟩
  (PCSRewindExtraction.assembleWitness input fun lane =>
    (decoded[lane.val]'(by simp [decoded])).1,
    (decoded.map Prod.snd).toList.sum)

def matchingRows (input : Public) (w : Witness input.config input.lanes) :
    Finset (Fin (blockLength input.config)) :=
  let encoded := encodedLanes input.config (paddedWitness input.config input.lanes w)
  Finset.univ.filter fun q => rowMatches input.config input.lanes encoded (q, input.root[q.val]!)

/-- A deterministic common support predicate on the actual fixed Root0 array. -/
def StrongRootSupport (profile : ParameterBounds.Profile) (lanes : Nat) (root : BaseOracle)
    (w : Witness (ParameterBounds.config profile) lanes) : Prop :=
  PCSRewindExtractor.heavyAgreementCap profile <
    (matchingRows ⟨ParameterBounds.config profile, lanes, root, #[]⟩ w).card

/-- Instrument the actual source encoder; filtering visits each root coordinate
once and never constructs a full-root record table. -/
def countedSupport (input : Public) (w : Witness input.config input.lanes) : Nat × Nat :=
  let encoded := CountedCandidateCheck.countedEncodedLanes input.config
    (paddedWitness input.config input.lanes w)
  ((Finset.univ.filter fun q : Fin (blockLength input.config) =>
    rowMatches input.config input.lanes encoded.1 (q, input.root[q.val]!)).card, encoded.2)

theorem countedSupport_value (input : Public) (w : Witness input.config input.lanes) :
    (countedSupport input w).1 = (matchingRows input w).card := by
  simp [countedSupport, matchingRows, CountedCandidateCheck.countedEncodedLanes_value]

theorem decodeRoot_cost (input : Public)
    (noWrap : input.config.logN - input.config.folds[0]! + input.config.rates[0]! ≤ 64)
    (redundancy : width input.config < blockLength input.config) :
    (decodeRoot input noWrap).2 ≤ input.lanes *
      ConcreteRowExtraction.rowArithmeticPolynomial (blockLength input.config) := by
  simp only [decodeRoot, Array.toList_map, Array.toList_ofFn, List.map_ofFn, List.sum_ofFn]
  calc
    _ ≤ ∑ _lane : Fin input.lanes,
        ConcreteRowExtraction.rowArithmeticPolynomial (blockLength input.config) := by
      apply Finset.sum_le_sum
      intro lane _
      exact ConcreteRowExtraction.countedExtractRow_polynomial_cost _ _ noWrap redundancy _
    _ = _ := by simp

def runForConfig {m : Nat} (c : Config)
    (noWrap : c.logN - c.folds[0]! + c.rates[0]! ≤ 64) (lanes : Nat)
    (family : Fin m → RingPCSGame.FamilyClaim) (points : Array RingPCSGame.PointClaim)
    (anchorPoint : Array E) (anchorValue : E) (root : BaseOracle) :
    Option (Witness c lanes) :=
  if m ≤ 2^64 ∧ points.size ≤ 2^64 ∧ FullRoot c lanes root then
    (OriginalClaimsChecker.prepare c lanes family points anchorPoint anchorValue).bind fun prepared =>
      let input : Public := ⟨c, lanes, root, #[]⟩
      (decodeRoot input noWrap).1.bind fun w =>
        let support := countedSupport input w
        if ParameterBounds.threshold input.config 0 ≤ support.1 ∧
            OriginalClaimsChecker.check prepared w = true then some w else none
  else none

def run {m : Nat} (profile : ParameterBounds.Profile) (lanes : Nat)
    (family : Fin m → RingPCSGame.FamilyClaim) (points : Array RingPCSGame.PointClaim)
    (anchorPoint : Array E) (anchorValue : E) (root : BaseOracle) :
    Option (Witness (ParameterBounds.config profile) lanes) :=
  runForConfig (ParameterBounds.config profile) (InitialCandidates.production_initial_facts profile).2.2.1
    lanes family points anchorPoint anchorValue root

end Whir.PCSRoundByRoundSource
