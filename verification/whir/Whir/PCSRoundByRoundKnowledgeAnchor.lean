import Whir.PCSRoundByRoundSourceDecoderCorrectness
import Whir.CommitmentAnchor

/-! Immutable original-anchor applicability for the actual straight-line
extractor. Ambiguity is an outer, once-per-commitment event under the genuine
fresh-after-root point law, not a conditional per-opening RBR error. -/
namespace Whir.PCSRoundByRoundKnowledge
open Concrete Protocol CausalGame ParameterBounds
open Classical

set_option maxRecDepth 100000
set_option maxHeartbeats 800000
attribute [local irreducible] ParameterBounds.config

/-- Actual returned words are members of the saved original anchor selector;
the selector is mathematical binding state, never the extraction algorithm. -/
theorem extract_saved_anchor {m : Nat} (p : Profile) (commitment : CommitmentAnchor.Commitment p)
    (family : Fin m → RingPCSGame.FamilyClaim) (points : Array RingPCSGame.PointClaim)
    (w : Witness (config p) commitment.lanes)
    (output : PCSRoundByRoundSource.run p commitment.lanes family points
      (Array.ofFn commitment.point) commitment.value commitment.root = some w) :
    w ∈ CommitmentAnchor.selected p commitment.lanes commitment.root commitment.point commitment.value := by
  classical
  have original := PCSRoundByRoundSource.run_output_explains p commitment.lanes family points
    (Array.ofFn commitment.point) commitment.value commitment.root w output
  exact Finset.mem_filter.mpr ⟨original.rootCandidate, original.anchor⟩

/-- Across arbitrary original families, stacking statements and point openings,
the unchanged saved point/value forces actual extracted outputs to coincide. -/
theorem extracted_words_same_saved_anchor {m n : Nat} (p : Profile)
    (commitment : CommitmentAnchor.Commitment p)
    (clean : ¬ CommitmentAnchor.Ambiguous p commitment.lanes commitment.root commitment.point)
    (family₁ : Fin m → RingPCSGame.FamilyClaim) (family₂ : Fin n → RingPCSGame.FamilyClaim)
    (points₁ points₂ : Array RingPCSGame.PointClaim)
    (w₁ w₂ : Witness (config p) commitment.lanes)
    (left : PCSRoundByRoundSource.run p commitment.lanes family₁ points₁
      (Array.ofFn commitment.point) commitment.value commitment.root = some w₁)
    (right : PCSRoundByRoundSource.run p commitment.lanes family₂ points₂
      (Array.ofFn commitment.point) commitment.value commitment.root = some w₂) : w₁ = w₂ :=
  CommitmentAnchor.cross_session p commitment clean w₁ w₂
    (extract_saved_anchor p commitment family₁ points₁ w₁ left)
    (extract_saved_anchor p commitment family₂ points₂ w₂ right)

/-- For every fixed root/shape before the genuinely uniform anchor point,
the exact outer ambiguity fiber is bounded by the fixed-list pair count. The
saved advertised value and all later original statements may be adaptive. -/
theorem original_anchor_conditional_loss (p : Profile) (lanes : Nat) (root : BaseOracle)
    (laneBound : lanes ≤ 2^(config p).folds[0]!) :
    Soundness.uniformProb (Finset.univ.filter fun point : Fin (config p).logN → E =>
      CommitmentAnchor.Ambiguous p lanes root point) ≤
      ((InitialCandidates.witnesses (config p) lanes root).card.choose 2 : ℚ) *
        ((config p).logN : ℚ) / 2^192 :=
  CommitmentAnchor.ambiguity_probability p lanes root laneBound

#print axioms extract_saved_anchor
#print axioms extracted_words_same_saved_anchor
#print axioms original_anchor_conditional_loss
end Whir.PCSRoundByRoundKnowledge
