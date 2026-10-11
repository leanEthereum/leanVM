import Whir.AnchoredPhysicalDriver
import Whir.AnchorPrefixRefinementCaller

/-! Pinned 32c accepted-event refinement. Caller geometry and the supported anchor batch are derived from actual source decoding in either boundary. The remaining hypotheses are the physical authenticated-row/root properties, not claim coverage or an assumed acceptance payload. Their cryptographic transport belongs to the physical Merkle/mode bridge. -/
namespace Whir.AnchoredPhysicalAcceptance
open Concrete Protocol FiatShamirGame AnchoredHeaderCodec AnchoredPhysicalDriver

theorem accepted_anchored_shapes {ctx : RawWHIRKeys.Context} {Q cap : Nat}
    {packet : RawWHIRKeys.Packet ctx Q} {record : Record}
    (accepted : Accepted ctx Q cap packet record) (seed : RingPCSGame.Prefix) (lambda : E) :
    let c := ParameterBounds.config packet.val.profile
    let claims := AnchorPrefixRefinement.anchoredClaims c record accepted.request.claims.family accepted.request.claims.points seed
    (claims.all (fun claim => shapeValid c record.shape.lanes claim.weight) = true) ∧
      shapeValid c record.shape.lanes (CausalGame.batchClaims (2^c.logN) claims lambda).weight = true := by
  obtain ⟨boundary,model,answers,same,parsed⟩ := accepted.origin
  exact request_anchored_shapes boundary cap packet.val.profile model record accepted.configuration same
    (RawWHIRKeys.entry ctx packet.val) answers accepted.request parsed seed lambda

/-- Any actual accepted source result refines to the dense causal WHIR verifier with the same original anchor. Row authenticity is exposed rather than replaced by a universal bad-event-cover assumption. -/
theorem accepted_protocol {ctx : RawWHIRKeys.Context} {Q cap : Nat}
    {packet : RawWHIRKeys.Packet ctx Q} {record : Record}
    (accepted : Accepted ctx Q cap packet record) (root : Oracle)
    (rootShape : oracleValid root
      (2^((ParameterBounds.config packet.val.profile).logN-(ParameterBounds.config packet.val.profile).folds[0]!+
        (ParameterBounds.config packet.val.profile).rates[0]!)) record.shape.lanes = true)
    (roots : ∀ proof, CausalGame.opening (ParameterBounds.config packet.val.profile)
      (CausalGame.challenges (ParameterBounds.config packet.val.profile) accepted.wire.tape) accepted.wire.replies = .ok proof →
        WHIRNativeArithmetic.RootShapes (ParameterBounds.config packet.val.profile) proof)
    (authenticated : ∀ proof, CausalGame.opening (ParameterBounds.config packet.val.profile)
      (CausalGame.challenges (ParameterBounds.config packet.val.profile) accepted.wire.tape) accepted.wire.replies = .ok proof →
        WHIRNativeArithmetic.AuthenticatedRows (ParameterBounds.config packet.val.profile)
          (CausalGame.challenges (ParameterBounds.config packet.val.profile) accepted.wire.tape) proof root) :
    ∃ seed lambda proof, accepted.wire.initial = some (seed,lambda) ∧
      CausalGame.opening (ParameterBounds.config packet.val.profile)
        (CausalGame.challenges (ParameterBounds.config packet.val.profile) accepted.wire.tape) accepted.wire.replies = .ok proof ∧
      let c := ParameterBounds.config packet.val.profile
      let claims := AnchorPrefixRefinement.anchoredClaims c record accepted.request.claims.family accepted.request.claims.points seed
      Protocol.verify c (CausalGame.challenges c accepted.wire.tape) record.shape.lanes root
        (CausalGame.batchClaims (2^c.logN) claims lambda).weight
        (CausalGame.batchClaims (2^c.logN) claims lambda).value proof = .ok () := by
  obtain ⟨⟨seed,lambda⟩,proof,initial,parsed,native⟩ := accepted.acceptance
  refine ⟨seed,lambda,proof,initial,parsed,?_⟩
  obtain ⟨families,points⟩ := accepted_nativeShapes accepted
  apply AnchorPrefixRefinement.sourceVerify_refines record accepted.request.claims.family accepted.request.claims.points
    seed lambda _ _ proof root accepted.configuration.1 accepted.configuration.2.1 accepted.configuration.2.2.1
    families _ (accepted_anchored_shapes accepted seed lambda).2 rootShape (roots proof parsed) (authenticated proof parsed) native
  intro i
  exact points _ (by simp)

#print axioms accepted_anchored_shapes
#print axioms accepted_protocol
end Whir.AnchoredPhysicalAcceptance
