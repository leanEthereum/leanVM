import FORS.LazyRun.Expose

/-! Events of the refined classification for small budgets. A cached answer that hits its target
is a first-order event unless its input is a chain step that is not at or above the prepared word
of a retained key, or a FORS leaf. Hits of those inputs become forgery events only in pairs: a
contact below the word together with an encoding marker or a second contact at the same key, two
consecutive edges into the frontier, a FORS leaf contact at a revealed secret, a contact completing
a near cover of the forgery's digest (every tree covered but one, which is contacted), or two FORS
leaf contacts at one index. -/

open OracleComp OracleSpec ENNReal

namespace FORS.Security.HiddenBridge

variable [Params]

open Concrete HiddenGraph

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
attribute [local instance] Classical.propDecidable


section Events

variable (parameter : PublicParameter) (results : OtsKey → Option (Counter × Encoding))
  (table : HiddenGraph.Table) (cache : QueryCache HashSpec)

/-- A chain input of a key. -/
def chainInput (key : OtsKey) (chain : ChainIndex) (step : ChainStep) (payload : Digest) : HashInput :=
  tweakableHashInput parameter (.chain key.1 key.2.1 key.2.2 chain step) (bytesLE 16 payload)

/-- A FORS leaf input: the hash of a selected secret. -/
def fleafInput (index : Index) (κ : FTree) (leaf : FLeaf) (payload : Digest) : HashInput :=
  tweakableHashInput parameter (.forsLeaf index κ leaf) (bytesLE 16 payload)

/-- Inputs whose single hit is not a forgery event by itself: a chain step other than a step of a
retained key at or above its prepared word, and a FORS leaf. -/
def SecondOrderInput (input : HashInput) : Prop :=
  (∃ (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex) (chain : ChainIndex) (step : ChainStep) (payload : Digest),
    input = tweakableHashInput parameter (.chain lay tree leaf chain step) (bytesLE 16 payload) ∧
    ¬(PrunedGraph.KeyActive parameter lay tree leaf ∧
      (preparedWord results (lay, tree, leaf) chain).val ≤ step.val)) ∨
  ∃ index κ leaf payload, input = fleafInput parameter index κ leaf payload

/-- First-order targets. -/
noncomputable def targetsA (tab : TargetAssignment.Table) (input : HashInput) : Finset Digest :=
  if SecondOrderInput parameter results input then ∅ else TargetAssignment.targets parameter tab input

/-- The table value at a chain position. -/
def chainValue (key : OtsKey) (chain : ChainIndex) (position : Digit) : Digest :=
  table (.chain key.1 key.2.1 key.2.2 chain position)

/-- The table value at the prepared word: the frontier. -/
noncomputable def frontierValue (key : OtsKey) (chain : ChainIndex) : Digest :=
  chainValue table key chain (preparedWord results key chain)

/-- A cached step just below the word, from a non-canonical payload, reaches the frontier. -/
def ContactAt (key : OtsKey) (chain : ChainIndex) : Prop :=
  ∃ (step : ChainStep) (payload : Digest) (answer : HashOutput),
    step.val + 1 = (preparedWord results key chain).val ∧
    payload ≠ chainValue table key chain ⟨step.val, by have := step.isLt; omega⟩ ∧
    cache (chainInput parameter key chain step payload) = some answer ∧
    truncateHash answer = frontierValue results table key chain

/-- Two cached consecutive steps below the word reach the frontier. -/
def TwoEdgeAt (key : OtsKey) (chain : ChainIndex) : Prop :=
  ∃ (first second : ChainStep) (payload : Digest) (answer answer' : HashOutput),
    first.val + 1 = second.val ∧ second.val + 1 = (preparedWord results key chain).val ∧
    cache (chainInput parameter key chain first payload) = some answer ∧
    cache (chainInput parameter key chain second (truncateHash answer)) = some answer' ∧
    truncateHash answer' = frontierValue results table key chain

/-- A cached encoding answer of the key decodes to a unit neighbour lowering the chain. -/
def MarkerAt (key : OtsKey) (chain : ChainIndex) : Prop :=
  ∃ (message : HashInput) (counter : Counter) (answer : HashOutput) (candidate : Encoding),
    cache (Wots.encodingInput parameter key.1 key.2.1 key.2.2 message counter) = some answer ∧
    TargetSum.decodeDigest (truncateHash answer) = some candidate ∧
    EncodingCode.UnitNeighborAt (preparedWord results key) candidate chain

/-- The WOTS events of a retained key. -/
def WotsEventAt (key : OtsKey) : Prop :=
  (∃ chain, TwoEdgeAt parameter results table cache key chain) ∨
  (∃ chain, ContactAt parameter results table cache key chain ∧ MarkerAt parameter results cache key chain) ∨
  ∃ chain chain', chain ≠ chain' ∧ ContactAt parameter results table cache key chain ∧
    ContactAt parameter results table cache key chain'

def WotsEvent : Prop :=
  ∃ key : OtsKey, PrunedGraph.KeyActive parameter key.1 key.2.1 key.2.2 ∧
    WotsEventAt parameter results table cache key

/-- A cached FORS leaf answer from a non-canonical secret equals the canonical leaf value. -/
def FContactAt (index : Index) (κ : FTree) (leaf : FLeaf) : Prop :=
  ∃ (payload : Digest) (answer : HashOutput), payload ≠ table (.fors index κ leaf 0) ∧
    cache (fleafInput parameter index κ leaf payload) = some answer ∧
    truncateHash answer = table (.fors index κ leaf 1)

/-- A FORS leaf contact whose secret is revealed. -/
def RevealedContact (reveals : List Coordinate) : Prop :=
  ∃ index κ leaf, Coordinate.fors index κ leaf 0 ∈ reveals ∧ FContactAt parameter table cache index κ leaf

/-- Two FORS leaf contacts at different leaves of one index. -/
def TwoForsContacts : Prop :=
  ∃ index κ leaf κ' leaf', (κ, leaf) ≠ (κ', leaf') ∧
    FContactAt parameter table cache index κ leaf ∧ FContactAt parameter table cache index κ' leaf'

/-- A cached, landed, unsigned forgery digest covered at every tree but one, which is contacted. -/
def ForsNear (root : Digest) (outcome : Outcome) (reveals : List Coordinate) : Prop :=
  SigningTranscript.Valid outcome.2.1 ∧
  ∃ digest, cachedDigest cache parameter root outcome.1.message outcome.1.signature.randomness = some digest ∧
    Landed parameter (digestIndex digest) ∧
    (∀ entry ∈ outcome.2.1, ∀ signature, entry.2 = some signature →
      ¬(entry.1 = outcome.1.message ∧ signature.randomness = outcome.1.signature.randomness)) ∧
    ∃ κ, FContactAt parameter table cache (digestIndex digest) κ (digestLeaves digest κ) ∧
      ∀ κ' ≠ κ, TreeCov (revealedSet reveals) (fullDigestView digest) κ'

end Events

/-- The refined bad event of one table. -/
def badA (parameterOutput : HashOutput) (fixed : HiddenGraph.Table) (highs : CoordinateHighs)
    (remaining : RemainingOutputs) (results : OtsKey → Option (Counter × Encoding)) (table : Coordinate → Digest)
    (v : ((Option HiddenBridge.Outcome × List Coordinate) × List (HiddenCost.Entry HashInput)) × QueryCache HashSpec) :
    Prop :=
  CacheMatch.Bad (targetsA (truncateHash parameterOutput) results
      (compTable parameterOutput fixed highs remaining table results)) v.2 ∨
    WotsEvent (truncateHash parameterOutput) results table v.2 ∨
    RevealedContact (truncateHash parameterOutput) table v.2 v.1.1.2 ∨
    TwoForsContacts (truncateHash parameterOutput) table v.2 ∨
    ∃ outcome, v.1.1.1 = some outcome ∧
      (ForsNear (truncateHash parameterOutput) table v.2 (sampleData parameterOutput fixed highs remaining).root
          outcome v.1.1.2 ∨
        ForsCover (truncateHash parameterOutput) (sampleData parameterOutput fixed highs remaining).root
          outcome v.1.1.2 v.2)

end FORS.Security.HiddenBridge
