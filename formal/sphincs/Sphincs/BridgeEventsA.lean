import Sphincs.BridgeExpose

/-! Events of the refined classification for small budgets. A cached answer that hits its target
is a first-order event unless its input is a root-tree chain step that is not at or above the
prepared word of a landed leaf, or a forest chain step. Hits of those inputs become forgery events
only in pairs: a contact below the word together with an encoding marker or a second contact at the
same leaf, two consecutive edges into the frontier, a forest chain contact at a revealed position, a
contact completing a near cover of the forgery's digest (every chain covered but one, which is
contacted), or two forest contacts at one index. -/

open OracleComp OracleSpec ENNReal

namespace Sphincs.Security.HiddenBridge

open Concrete HiddenGraph

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
attribute [local instance] Classical.propDecidable

variable [Params]

section Events

variable (parameter : PublicParameter) (results : Index → Option (Counter × Encoding))
  (table : HiddenGraph.Table) (cache : QueryCache HashSpec)

/-- A root-tree chain input. -/
def chainInput (leaf : Index) (chain : ChainIndex) (step : ChainStep) (payload : Digest) : HashInput :=
  tweakableHashInput parameter (.chain topLayer rootTree leaf chain step) (bytesLE 16 payload)

/-- A forest chain step input. -/
def fchainInput (index : Index) (c : Coord) (s : SuperIdx) (j : SubIdx) (a : ChildIdx) (i : FChain) (t : FStep)
    (payload : Digest) : HashInput :=
  tweakableHashInput parameter (.fchain index c s j a i t) (bytesLE 16 payload)

/-- Inputs whose single hit is not a forgery event by itself: a chain step other than a root-tree
step at or above the prepared word of a landed leaf, and a forest chain step. -/
def SecondOrderInput (input : HashInput) : Prop :=
  (∃ (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex) (chain : ChainIndex) (step : ChainStep) (payload : Digest),
    input = tweakableHashInput parameter (.chain lay tree leaf chain step) (bytesLE 16 payload) ∧
    ¬(lay = topLayer ∧ tree = rootTree ∧ Landed parameter leaf ∧ (preparedWord results leaf chain).val ≤ step.val)) ∨
  ∃ index c s j a i t payload, input = fchainInput parameter index c s j a i t payload

/-- First-order targets. -/
noncomputable def targetsA (tab : TargetAssignment.Table) (input : HashInput) : Finset Digest :=
  if SecondOrderInput parameter results input then ∅ else TargetAssignment.targets parameter tab input

/-- The table value at a chain position. -/
def chainValue (leaf : Index) (chain : ChainIndex) (position : Digit) : Digest :=
  table (.chain topLayer rootTree leaf chain position)

/-- The table value at the prepared word: the frontier. -/
noncomputable def frontierValue (leaf : Index) (chain : ChainIndex) : Digest :=
  chainValue table leaf chain (preparedWord results leaf chain)

/-- A cached step just below the word, from a non-canonical payload, reaches the frontier. -/
def ContactAt (leaf : Index) (chain : ChainIndex) : Prop :=
  ∃ (step : ChainStep) (payload : Digest) (answer : HashOutput),
    step.val + 1 = (preparedWord results leaf chain).val ∧
    payload ≠ chainValue table leaf chain ⟨step.val, by have := step.isLt; omega⟩ ∧
    cache (chainInput parameter leaf chain step payload) = some answer ∧
    truncateHash answer = frontierValue results table leaf chain

/-- Two cached consecutive steps below the word reach the frontier. -/
def TwoEdgeAt (leaf : Index) (chain : ChainIndex) : Prop :=
  ∃ (first second : ChainStep) (payload : Digest) (answer answer' : HashOutput),
    first.val + 1 = second.val ∧ second.val + 1 = (preparedWord results leaf chain).val ∧
    cache (chainInput parameter leaf chain first payload) = some answer ∧
    cache (chainInput parameter leaf chain second (truncateHash answer)) = some answer' ∧
    truncateHash answer' = frontierValue results table leaf chain

/-- A cached encoding answer of the leaf decodes to a unit neighbour lowering the chain. -/
def MarkerAt (leaf : Index) (chain : ChainIndex) : Prop :=
  ∃ (message : ForestKey) (counter : Counter) (answer : HashOutput) (candidate : Encoding),
    cache (Wots.encodingInput parameter topLayer rootTree leaf message counter) = some answer ∧
    TargetSum.decodeDigest (truncateHash answer) = some candidate ∧
    EncodingCode.UnitNeighborAt (preparedWord results leaf) candidate chain

/-- The WOTS events of a landed leaf. -/
def WotsEventAt (leaf : Index) : Prop :=
  (∃ chain, TwoEdgeAt parameter results table cache leaf chain) ∨
  (∃ chain, ContactAt parameter results table cache leaf chain ∧ MarkerAt parameter results cache leaf chain) ∨
  ∃ chain chain', chain ≠ chain' ∧ ContactAt parameter results table cache leaf chain ∧
    ContactAt parameter results table cache leaf chain'

def WotsEvent : Prop := ∃ leaf, Landed parameter leaf ∧ WotsEventAt parameter results table cache leaf

/-- A cached forest chain answer from a non-canonical payload equals the next canonical value. -/
def FContactAt (index : Index) (c : Coord) (s : SuperIdx) (j : SubIdx) (a : ChildIdx) (i : FChain) (t : FStep) : Prop :=
  ∃ (payload : Digest) (answer : HashOutput), payload ≠ table (.fchain index c s j a i ⟨t.val, by omega⟩) ∧
    cache (fchainInput parameter index c s j a i t payload) = some answer ∧
    truncateHash answer = table (.fchain index c s j a i ⟨t.val + 1, by omega⟩)

/-- A forest contact at a chain step whose input position is revealed (at or below). -/
def RevealedContact (reveals : List Coordinate) : Prop :=
  ∃ index c s j a i t, (∃ q : FPos, q.val ≤ t.val ∧ Coordinate.fchain index c s j a i q ∈ reveals) ∧
    FContactAt parameter table cache index c s j a i t

/-- Two forest contacts at different chains of one index. -/
def TwoForestContacts : Prop :=
  ∃ index c s j a i t c' s' j' a' i' t', (c, j, i) ≠ (c', j', i') ∧
    FContactAt parameter table cache index c s j a i t ∧ FContactAt parameter table cache index c' s' j' a' i' t'

/-- A cached, landed, unsigned forgery digest covered at every chain but one, which is contacted. -/
def ForestNear (root : Digest) (outcome : Outcome) (reveals : List Coordinate) : Prop :=
  SigningTranscript.Valid outcome.2.1 ∧
  ∃ digest, cachedDigest cache parameter root outcome.1.message outcome.1.signature.randomness = some digest ∧
    Landed parameter (digestIndex digest) ∧
    (∀ entry ∈ outcome.2.1, ∀ signature, entry.2 = some signature →
      ¬(entry.1 = outcome.1.message ∧ signature.randomness = outcome.1.signature.randomness)) ∧
    ∃ c j i t, FContactAt parameter table cache (digestIndex digest) c (digestMarks digest c).super j
        ((digestMarks digest c).child j) i t ∧
      ∀ c' j' i', (c', j', i') ≠ (c, j, i) → ChainCov (revealedSet reveals) (fullDigestView digest) c' j' i'

end Events

/-- The refined bad event of one table. -/
def badA (parameterOutput : HashOutput) (fixed : HiddenGraph.Table) (highs : CoordinateHighs)
    (remaining : RemainingOutputs) (results : Index → Option (Counter × Encoding)) (table : Coordinate → Digest)
    (v : ((Option HiddenBridge.Outcome × List Coordinate) × List (HiddenCost.Entry HashInput)) × QueryCache HashSpec) :
    Prop :=
  CacheMatch.Bad (targetsA (truncateHash parameterOutput) results
      (compTable parameterOutput fixed highs remaining table results)) v.2 ∨
    WotsEvent (truncateHash parameterOutput) results table v.2 ∨
    RevealedContact (truncateHash parameterOutput) table v.2 v.1.1.2 ∨
    TwoForestContacts (truncateHash parameterOutput) table v.2 ∨
    ∃ outcome, v.1.1.1 = some outcome ∧
      (ForestNear (truncateHash parameterOutput) table v.2 (sampleData parameterOutput fixed highs remaining).root
          outcome v.1.1.2 ∨
        ForestCover (truncateHash parameterOutput) (sampleData parameterOutput fixed highs remaining).root
          outcome v.1.1.2 v.2)

end Sphincs.Security.HiddenBridge
