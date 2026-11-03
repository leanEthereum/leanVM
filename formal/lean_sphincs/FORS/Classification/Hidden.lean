import FORS.Classification.Reference
import FORS.Scheme.DigestView

/-! The stopped hidden-row proof uses one hidden predecessor guess or one noncanonical
output match at a chain address, and one query of an unrevealed FORS secret. The older two-edge/contact extraction implies this simpler
event without a small-query assumption or an honest-signature premise. -/

open OracleComp OracleSpec

namespace FORS.Security.Wots

variable [Params]
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

end FORS.Security.Wots

namespace FORS.Security.Fors

variable [Params]
open Concrete

/-- An unrevealed honest FORS secret was queried at its leaf. -/
def HiddenSecretQuery (f : QueryImpl HashSpec Id) (parameter : PublicParameter)
    (seed : MasterSeed) (revealed : Disclosures) (trace : List HashInput) : Prop :=
  ∃ (index : Index) (κ : FTree) (leaf : FLeaf), leaf ∉ revealed index κ ∧
    tweakableHashInput parameter (.forsLeaf index κ leaf)
      (bytesLE 16 (Completeness.forsSecretValue f parameter index κ seed leaf)) ∈ trace

/-- A canonical opening outside the disclosure coverage hashes an unrevealed honest secret during
the actual verification. The disclosure table can depend on the whole past. -/
theorem Opening.covered_or_hidden (f : QueryImpl HashSpec Id) (parameter : PublicParameter)
    (index : Index) (seed : MasterSeed) (leaves : FTree → FLeaf) (opening : FTree → TreeOpening)
    (revealed : Disclosures) (trace : List HashInput)
    (hopening : Opening f parameter index seed leaves opening)
    (hrun : ContainsRun f trace (forsRecover parameter index leaves opening)) :
    Covered revealed (index, leaves) ∨ HiddenSecretQuery f parameter seed revealed trace := by
  classical
  by_cases hcovered : Covered revealed (index, leaves)
  · exact Or.inl hcovered
  · right
    simp only [Covered, not_forall] at hcovered
    obtain ⟨κ, hnot⟩ := hcovered
    refine ⟨index, κ, leaves κ, hnot, hrun _ ?_⟩
    have hmem := leafInput_mem f parameter index leaves opening κ
    rwa [(hopening κ).1] at hmem

end FORS.Security.Fors
