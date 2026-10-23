import Sphincs.SecurityReferenceSignature
import Sphincs.ForestCoverage

set_option backward.isDefEq.respectTransparency false

/-! The stopped hidden-row proof uses one hidden predecessor guess or one noncanonical
output match at a chain address. The older two-edge/contact extraction implies this simpler
event without a small-query assumption or an honest-signature premise. -/

open OracleComp OracleSpec

namespace Sphincs.Security.Wots
open Concrete Chain

variable (f : QueryImpl HashSpec Id) (parameter : PublicParameter) (lay : Layer)
  (tree : TreeIndex) (leaf : LeafIndex) (reference : Encoding) (secret : ChainIndex → Digest)

def HiddenPredecessor (trace : List HashInput) : Prop :=
  ∃ (index : ChainIndex) (step : ChainStep), step.val < (reference index).val ∧
    tweakableHashInput parameter (.chain lay tree leaf index step)
      (bytesLE 16 (honestChain f parameter lay tree leaf index (secret index) step.val)) ∈ trace

def ChainOutputMatch (trace : List HashInput) : Prop :=
  ∃ (index : ChainIndex) (step : ChainStep) (payload : Digest),
    tweakableHashInput parameter (.chain lay tree leaf index step) (bytesLE 16 payload) ∈ trace ∧
    ChainHit f parameter lay tree leaf index (secret index) step.val step.isLt payload

theorem contact_hidden_or_output (trace : List HashInput) (index : ChainIndex)
    (h : Contact f parameter lay tree leaf index (reference index)
      (frontier f parameter lay tree leaf reference secret index) trace) :
    HiddenPredecessor f parameter lay tree leaf reference secret trace ∨
      ChainOutputMatch f parameter lay tree leaf secret trace := by
  obtain ⟨step, payload, hstep, htrace, hvalue⟩ := h
  by_cases heq : payload = honestChain f parameter lay tree leaf index (secret index) step.val
  · exact Or.inl ⟨index, step, by omega, heq ▸ htrace⟩
  · refine Or.inr ⟨index, step, payload, htrace, heq, ?_⟩
    simpa only [frontier, hstep] using hvalue

/-- Each old chain exceptional case exposes an actual hidden-input guess or a distinct-input
hit on the canonical next value. No probability estimate is used in this conversion. -/
theorem ChainException.hidden_or_output {trace : List HashInput}
    (h : ChainException f parameter lay tree leaf reference secret trace) :
    HiddenPredecessor f parameter lay tree leaf reference secret trace ∨
      ChainOutputMatch f parameter lay tree leaf secret trace := by
  rcases h with ⟨index, step, payload, _, htrace, hhit⟩ |
    ⟨index, first, second, payload, middle, _, hsecond, _, htrace, _, hvalue⟩ |
    ⟨left, right, _, hcontact, _⟩ | ⟨index, _, hcontact⟩
  · exact Or.inr ⟨index, step, payload, htrace, hhit⟩
  · exact contact_hidden_or_output f parameter lay tree leaf reference secret trace index
      ⟨second, middle, hsecond, htrace, hvalue⟩
  · exact contact_hidden_or_output f parameter lay tree leaf reference secret trace left hcontact
  · exact contact_hidden_or_output f parameter lay tree leaf reference secret trace index hcontact

end Sphincs.Security.Wots

namespace Sphincs.Security.Forest
open Concrete

/-- An unrevealed honest forest chain value at its own chain step was queried. -/
def HiddenChainQuery (f : QueryImpl HashSpec Id) (parameter : PublicParameter)
    (seed : MasterSeed) (revealed : Disclosures) (trace : List HashInput) : Prop :=
  ∃ (index : Index) (c : Coord) (s : SuperIdx) (j : SubIdx) (a : ChildIdx) (i : FChain) (p : FStep),
    (∀ q ∈ revealed index c s j a i, p.val < q.val) ∧
    tweakableHashInput parameter (.fchain index c s j a i p)
      (bytesLE 16 (Completeness.chainValueOf f parameter index c s j a i seed p.val)) ∈ trace

/-- A canonical opening outside the disclosure coverage hashes an unrevealed honest chain value
during the actual verification. The disclosure table can depend on the whole past. -/
theorem Opening.covered_or_hidden (f : QueryImpl HashSpec Id) (parameter : PublicParameter)
    (index : Index) (seed : MasterSeed) (fields : Coord → FieldVal) (opening : Coord → CoordOpening)
    (revealed : Disclosures) (trace : List HashInput)
    (hopening : Opening f parameter index seed (fun c => decodeMark (fields c)) opening)
    (hrun : ContainsRun f trace (forestRecover parameter index (fun c => decodeMark (fields c)) opening)) :
    Covered revealed (index, fields) ∨ HiddenChainQuery f parameter seed revealed trace := by
  classical
  by_cases hcovered : Covered revealed (index, fields)
  · exact Or.inl hcovered
  · right
    simp only [Covered, ChainCov, not_forall, not_or, not_exists, not_and, not_le] at hcovered
    obtain ⟨c, j, i, hneed, hnot⟩ := hcovered
    have hpos : 0 < (lut ((decodeMark (fields c)).word j) i).val := Nat.pos_of_ne_zero hneed
    have hrange : chainTop - (lut ((decodeMark (fields c)).word j) i).val + 0 < chainTop := by
      have := (lut ((decodeMark (fields c)).word j) i).isLt
      simp only [chainTop] at this ⊢
      omega
    have hmem := chainInput_mem f parameter index (fun c => decodeMark (fields c)) opening c j i 0 hpos hrange
    refine ⟨index, c, (decodeMark (fields c)).super, j, (decodeMark (fields c)).child j, i,
      ⟨chainTop - (lut ((decodeMark (fields c)).word j) i).val + 0, hrange⟩, fun q hq => hnot q hq, ?_⟩
    refine hrun _ ?_
    convert hmem using 3
    simp only [walkValue, forestWalk, evalWithAnswerFn_pure, Nat.add_zero]
    exact ((hopening c).1 j i).symm

end Sphincs.Security.Forest
