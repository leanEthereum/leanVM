import Whir.PCSBCSChallengeOracleEnteredErasure
import Whir.PCSBCSCallerBinding
import Whir.PCSStateRestorationLatent

/-! Concrete additive-RBR transition fibers for the literal duplex's whole
source packets, including every data-valued live caller entry at the public
boundary. Ghost reconstruction reads only other packet fibers and strict
predecessors; arbitrary off-image observer requests remain in the same game.
A source parser must still justify the metadata builder and accepted path. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
namespace Whir.PCSBCSChallengeOracle.Restoration
open Concrete Protocol CausalGame CausalProbability PCSBCSRounds
open FiatShamirGame RawOracleCoupling
open PCSBCSChallengeOracle PCSBCSCallerBinding PCSBCSRestorationHazard
attribute [local irreducible] PCSBCSCallerBinding.callerCertificate
  PCSBCSCallerBinding.fixedCertificate EnteredPacket.metadataFromOther

variable (p : ParameterBounds.Profile) (Q : Nat) (iv : Digest32) (boundary : Nat)

abbrev Key := (EnteredPacket.partition (p := p) (Q := Q) (iv := iv) (boundary := boundary)).Key
abbrev Answer := (EnteredPacket.partition (p := p) (Q := Q) (iv := iv) (boundary := boundary)).Answer
  (D := Digest32)

noncomputable local instance (key : Key p Q iv boundary) : Fintype (Answer p Q iv boundary key) :=
  match key with
  | .inl _ => inferInstance
  | .inr _ => inferInstance

abbrev Builder := (current : EnteredPacket p Q iv boundary) →
  current.OtherValues → (∀ earlier : current.Earlier, Raw earlier.val) → CallerData p

open Classical in
noncomputable def model (build : Builder p Q iv boundary) :
    PCSStateRestoration.Latent.NodeModel (Key p Q iv boundary) (Answer p Q iv boundary)
      (Option (CallerData p)) where
  reconstruct key other := match key with
    | .inl current => some (current.metadataFromOther (build current) other)
    | .inr _ => none
  before data key := match key, data with
    | .inl current, some caller => (callerCertificate p).before caller current.2.coord
    | _, _ => false
  after data key answer := match key with
    | .inl current => match data with
      | some caller => (callerCertificate p).after caller current.2.coord (grouped current.2.coord answer)
      | none => false
    | .inr _ => false

/-- Whole output blocks induce exactly the checked RBR alphabet. The incoming
state is fixed before every bit of the selected packet, including unused bits. -/
theorem whole_packet_fiber (caller : CallerData p) (current : EnteredPacket p Q iv boundary)
    (undoomed : (callerCertificate p).before caller current.2.coord = false) :
    Soundness.uniformProb (Finset.univ.filter fun full :
      Fin (blocks (rawWidth current.2.coord)) → Digest32 =>
      (callerCertificate p).after caller current.2.coord (grouped current.2.coord full) = true) ≤
        PCSRoundByRoundKnowledge.rbrError := by
  classical
  have law := grouped_uniform current.2.coord (fun answer =>
    (callerCertificate p).after caller current.2.coord answer = true)
  rw [SamplingProbability.probability_eq_uniformProb,
    SamplingProbability.probability_eq_uniformProb] at law
  have exactLaw := (Rat.cast_inj (α := ℝ)).mp law
  exact exactLaw.trans_le (caller_fiber p caller current.2.coord undoomed)

/-- Derived from the actual grouped alphabet and additive RBR fiber, not an
assumed primitive or final failure-probability bound. -/
theorem conditional_hazard (build : Builder p Q iv boundary) :
    PCSStateRestoration.Latent.ConditionalHazard (model p Q iv boundary build)
      PCSRoundByRoundKnowledge.rbrError := by
  classical
  intro key other undoomed
  cases key with
  | inl current =>
    change (callerCertificate p).before
      (current.metadataFromOther (build current) other) current.2.coord = false at undoomed
    have bound := whole_packet_fiber p Q iv boundary
      (current.metadataFromOther (build current) other) current undoomed
    unfold Soundness.uniformProb at bound ⊢
    simp only [model,Fintype.card_eq_nat_card] at bound ⊢
    convert bound using 1
    congr 2
  | inr garbage =>
    simp only [model,Bool.false_eq_true,Finset.filter_false,Soundness.uniformProb,
      Finset.card_empty,Nat.cast_zero,zero_div]
    unfold PCSRoundByRoundKnowledge.rbrError SupportedCandidateExtraction.radiusEnvelope
    positivity

#print axioms whole_packet_fiber
#print axioms conditional_hazard
end Whir.PCSBCSChallengeOracle.Restoration
