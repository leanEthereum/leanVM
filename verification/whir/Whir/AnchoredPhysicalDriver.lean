import Whir.AnchoredSourceCaller
import Whir.AnchoredSourceFreshCaller
import Whir.AnchoredSourceRegistry
import Whir.AnchoredPhysicalTranscript
import Whir.AnchoredPhysicalAnchor
import Whir.WHIRPhysicalDriver
import Whir.CommitmentAnchor

/-! Pinned 32c anchored acceptance endpoint. The old physical decoder is used only for the unchanged WHIR opening suffix and authenticated rows. Its unanchored caller header, claim resolver and terminal acceptance function are not called here. Every acceptance is produced by the occupied-prefix native arithmetic after an exact immutable-record caller parse. -/
namespace Whir.AnchoredPhysicalDriver
open Concrete Protocol FiatShamirGame WHIRSourceChronology
open AnchoredHeaderCodec WHIRPhysicalVerifier
open MerkleTransport MerkleTransport.Commitments

/-- Exact profile/configuration guard before any WHIR gamma/map/lambda output. The point-count bound includes the family and the new anchor power. -/
def configuration (p : ParameterBounds.Profile) (r : Record) : Prop :=
  r.Valid ∧ r.shape.logN = (ParameterBounds.config p).logN ∧
    r.shape.logBatch = (ParameterBounds.config p).folds[0]! ∧
    r.shape.logRate = (ParameterBounds.config p).rates[0]!
instance (p : ParameterBounds.Profile) (r : Record) : Decidable (configuration p r) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _))

inductive Boundary where
  | original
  | fresh
  deriving DecidableEq

def decodeCaller (boundary : Boundary) (layout : WHIRCallerClaims.CallerLayout) (record : Record)
    (entry : FramedHistory) (answers : Coordinate → Digest32) : Option AnchoredSourceCaller.Claims :=
  match boundary with
  | .original => AnchoredSourceCaller.decode layout record.context entry answers
  | .fresh => AnchoredSourceFreshCaller.decode layout record entry answers

theorem decodeCaller_geometry (boundary : Boundary) (model : WHIRCallerSupport.ProductionLayout) (record : Record)
    (entry : FramedHistory) (answers : Coordinate → Digest32) (decoded : AnchoredSourceCaller.Claims)
    (parsed : decodeCaller boundary model.layout record entry answers = some decoded) :
    WHIRCallerGeometry.ClaimsValid
      (fun i d => WHIRCallerSupport.columnFits model.sources i d = true)
      (fun o d => WHIRCallerSupport.ringFits model.sources o d = true)
      (WHIRCallerClaims.callerPlacements model.layout) decoded.caller := by
  cases boundary with
  | original => exact AnchoredSourceCaller.decode_geometry model record.context entry answers decoded parsed
  | fresh => exact AnchoredSourceFreshCaller.decode_geometry model record entry answers decoded parsed

/-- Decoder inputs are physical prior answers. Missing keys reject rather than becoming arbitrary scalar defaults. Original context and identity come from the native original receiver; transport cannot replace them. -/
def request (boundary : Boundary) (cap : Nat) (p : ParameterBounds.Profile) (layout : WHIRCallerClaims.CallerLayout)
    (record : Record) (entry : FramedHistory) (answers : Coordinate → Option Digest32) :
    Option (CausalBindingState.ClaimRequest cap p) :=
  if (WHIRCallerOutputs.callerOutputs entry).all (fun q => (answers q).isSome) then do
    let decoded ← decodeCaller boundary layout record entry
      (fun q => (answers q).getD DuplexRefinement.zeroDigest)
    if decoded.record ≠ record then none else do
      if laneBound : record.shape.lanes ≤ 2^(ParameterBounds.config p).folds[0]! then
        if familyBound : decoded.caller.families.length ≤ cap then
          if pointBound : decoded.caller.points.size+2 ≤ 2^64 then
            some ⟨record.root,record.shape.lanes,laneBound,
              ⟨decoded.caller.families.length,fun i => decoded.caller.families[i],familyBound,
                decoded.caller.points,by omega⟩⟩
          else none
        else none
      else none
  else none

theorem opening_metadata (model : WHIRCallerSupport.ProductionLayout) (p : ParameterBounds.Profile)
    (record : Record) (configured : configuration p record)
    (same : record.shape = AnchoredSourceCaller.shape model.layout) :
    WHIRCallerClaims.openingMatches p record.shape.lanes model.layout = true := by
  simp only [WHIRCallerClaims.openingMatches,Bool.and_eq_true,beq_iff_eq]
  exact ⟨⟨congrArg Shape.lanes same,
    (WHIRCallerSupport.config_initial_geometry p).1.symm.trans
      (configured.2.1.symm.trans (congrArg Shape.logN same))⟩,
    (AnchoredSourceCaller.config_initial_rate p).symm.trans
      (configured.2.2.2.symm.trans (congrArg Shape.logRate same))⟩

theorem request_origin (boundary : Boundary) (cap : Nat) (p : ParameterBounds.Profile) (layout : WHIRCallerClaims.CallerLayout)
    (record : Record) (entry : FramedHistory) (answers : Coordinate → Option Digest32)
    (result : CausalBindingState.ClaimRequest cap p)
    (accepted : request boundary cap p layout record entry answers = some result) :
    ∃ decoded, decodeCaller boundary layout record entry
      (fun q => (answers q).getD DuplexRefinement.zeroDigest) = some decoded ∧
      decoded.record = record ∧ result.root = record.root ∧ result.lanes = record.shape.lanes := by
  unfold request at accepted
  split at accepted
  next present =>
    cases parsed : decodeCaller boundary layout record entry
        (fun q => (answers q).getD DuplexRefinement.zeroDigest) with
    | none => simp [parsed] at accepted
    | some decoded =>
      simp only [parsed,bind,Option.bind] at accepted
      split at accepted
      next mismatch => contradiction
      next same =>
        split at accepted
        next lanes =>
          split at accepted
          next families =>
            split at accepted
            next points =>
              cases Option.some.inj accepted
              exact ⟨decoded,rfl,not_ne_iff.mp same,rfl,rfl⟩
            next => contradiction
          next => contradiction
        next => contradiction
  next => contradiction

theorem request_nativeShapes (boundary : Boundary) (cap : Nat) (p : ParameterBounds.Profile)
    (model : WHIRCallerSupport.ProductionLayout) (record : Record)
    (configured : configuration p record) (same : record.shape = AnchoredSourceCaller.shape model.layout)
    (entry : FramedHistory) (answers : Coordinate → Option Digest32)
    (result : CausalBindingState.ClaimRequest cap p)
    (accepted : request boundary cap p model.layout record entry answers = some result) :
    SuccinctRingWeight.FamilyShape (ParameterBounds.config p).logN result.claims.family ∧
    (∀ point ∈ result.claims.points.toList,
      SuccinctPointWeight.Shape (ParameterBounds.config p).logN point) := by
  unfold request at accepted
  split at accepted
  next present =>
    cases parsed : decodeCaller boundary model.layout record entry
        (fun q => (answers q).getD DuplexRefinement.zeroDigest) with
    | none => simp [parsed] at accepted
    | some decoded =>
      simp only [parsed,bind,Option.bind] at accepted
      split at accepted
      next mismatch => contradiction
      next matched =>
        split at accepted
        next lanes =>
          split at accepted
          next families =>
            split at accepted
            next points =>
              cases Option.some.inj accepted
              exact WHIRCallerSupport.geometry_nativeShapes model p record.shape.lanes
                (opening_metadata model p record configured same) lanes decoded.caller
                (decodeCaller_geometry boundary model record entry _ decoded parsed)
            next => contradiction
          next => contradiction
        next => contradiction
  next => contradiction

theorem request_anchored_shapes (boundary : Boundary) (cap : Nat) (p : ParameterBounds.Profile)
    (model : WHIRCallerSupport.ProductionLayout) (record : Record)
    (configured : configuration p record) (same : record.shape = AnchoredSourceCaller.shape model.layout)
    (entry : FramedHistory) (answers : Coordinate → Option Digest32)
    (result : CausalBindingState.ClaimRequest cap p)
    (accepted : request boundary cap p model.layout record entry answers = some result)
    (seed : RingPCSGame.Prefix) (lambda : E) :
    let c := ParameterBounds.config p
    let claims := (RingPCSGame.transformedClaims (2^c.logN) result.claims.family result.claims.points seed).push
      ⟨CommitmentAnchor.weight c record.shape.lanes record.point.toArray,record.value⟩
    (claims.all (fun claim => Protocol.shapeValid c record.shape.lanes claim.weight) = true) ∧
      Protocol.shapeValid c record.shape.lanes (CausalGame.batchClaims (2^c.logN) claims lambda).weight = true := by
  unfold request at accepted
  split at accepted
  next present =>
    cases parsed : decodeCaller boundary model.layout record entry
        (fun q => (answers q).getD DuplexRefinement.zeroDigest) with
    | none => simp [parsed] at accepted
    | some decoded =>
      simp only [parsed,bind,Option.bind] at accepted
      split at accepted
      next mismatch => contradiction
      next matched =>
        split at accepted
        next lanes =>
          split at accepted
          next families =>
            split at accepted
            next points =>
              cases Option.some.inj accepted
              exact AnchoredSourceCaller.geometry_anchored_shapes model p record.shape.lanes
                (opening_metadata model p record configured same) lanes decoded
                (decodeCaller_geometry boundary model record entry _ decoded parsed) seed lambda record.point.toArray record.value
            next => contradiction
          next => contradiction
        next => contradiction
  next => contradiction

structure Accepted (ctx : RawWHIRKeys.Context) (Q cap : Nat) (packet : RawWHIRKeys.Packet ctx Q)
    (record : Record) where
  request : CausalBindingState.ClaimRequest cap packet.val.profile
  wire : WireState packet.val.profile
  history : List (Sigma (RawOracleCoupling.Concrete.GroupAnswer ctx Q))
  configuration : configuration packet.val.profile record
  origin : ∃ boundary : Boundary, ∃ model : WHIRCallerSupport.ProductionLayout, ∃ answers : Coordinate → Option Digest32,
    record.shape = AnchoredSourceCaller.shape model.layout ∧
    AnchoredPhysicalDriver.request boundary cap packet.val.profile model.layout record
      (RawWHIRKeys.entry ctx packet.val) answers = some request
  acceptance : ∃ (seedBatch : RingPCSGame.Prefix × E) (proof : Opening),
    wire.initial = some seedBatch ∧
    CausalGame.opening (ParameterBounds.config packet.val.profile)
      (CausalGame.challenges (ParameterBounds.config packet.val.profile) wire.tape) wire.replies = .ok proof ∧
    AnchoredPhysicalAnchor.sourceVerify record request.claims.family request.claims.points seedBatch.1 seedBatch.2
      (ParameterBounds.config packet.val.profile)
      (CausalGame.challenges (ParameterBounds.config packet.val.profile) wire.tape) proof = .ok ()

def finish (ctx : RawWHIRKeys.Context) (Q cap : Nat) (packet : RawWHIRKeys.Packet ctx Q)
    (record : Record) (configured : configuration packet.val.profile record)
    (request : CausalBindingState.ClaimRequest cap packet.val.profile) (state : WireState packet.val.profile)
    (history : List (Sigma (RawOracleCoupling.Concrete.GroupAnswer ctx Q)))
    (origin : ∃ boundary : Boundary, ∃ model : WHIRCallerSupport.ProductionLayout, ∃ answers : Coordinate → Option Digest32,
      record.shape = AnchoredSourceCaller.shape model.layout ∧
      AnchoredPhysicalDriver.request boundary cap packet.val.profile model.layout record
        (RawWHIRKeys.entry ctx packet.val) answers = some request) :
    Option (Accepted ctx Q cap packet record) :=
  match initial : state.initial with
  | none => none
  | some (seed,lambda) =>
    let c := ParameterBounds.config packet.val.profile
    let challenges := CausalGame.challenges c state.tape
    match parsed : CausalGame.opening c challenges state.replies with
    | .error _ => none
    | .ok proof =>
      match accepted : AnchoredPhysicalAnchor.sourceVerify record request.claims.family request.claims.points
          seed lambda c challenges proof with
      | .error _ => none
      | .ok () => some ⟨request,state,history,configured,origin,⟨(seed,lambda),proof,initial,parsed,accepted⟩⟩

/-- Trusted native continuation for either the original caller entry or a later fresh entry. The fresh boundary never receives or samples the original commitment again. Full record comparison finishes before readPhysicalPackets obtains opening gamma/map/lambda. -/
def verifySource (cap : Nat) (boundary : Boundary) (model : WHIRCallerSupport.ProductionLayout)
    (ctx : RawWHIRKeys.Context) (stack : ctx.mode = .stack) (Q : Nat)
    (packet : RawWHIRKeys.Packet ctx Q) (record : Record) (proofs : Array PrunedMerklePaths) :
    Source cap (Option (Accepted ctx Q cap packet record)) :=
  if configured : configuration packet.val.profile record then
    if mismatch : record.shape ≠ AnchoredSourceCaller.shape model.layout then .done none else
      .commit record.root (readCallerInputs ctx Q packet (WHIRModeFinal.callerPositions ctx Q packet)
        (fun _ => none) (fun answers =>
          match parsed : request boundary cap packet.val.profile model.layout record (RawWHIRKeys.entry ctx packet.val) answers with
          | none => .done none
          | some request =>
            .claims packet.val.profile (RawWHIRKeys.entry ctx packet.val) request
              (readPhysicalPackets ctx stack Q packet.val.profile record.shape.lanes proofs none
                (RawOracleCoupling.Concrete.completion ctx Q packet) (completion_profiles ctx Q packet)
                (initialWireState packet.val.profile record.root)
                (fun state history => .done (finish ctx Q cap packet record configured request state history
                  ⟨boundary,model,answers,not_ne_iff.mp mismatch,parsed⟩)))))
  else .done none

theorem verifySource_rejected_configuration (cap : Nat) (boundary : Boundary)
    (model : WHIRCallerSupport.ProductionLayout) (ctx : RawWHIRKeys.Context) (stack : ctx.mode = .stack)
    (Q : Nat) (packet : RawWHIRKeys.Packet ctx Q) (record : Record) (proofs : Array PrunedMerklePaths)
    (invalid : ¬ configuration packet.val.profile record) :
    verifySource cap boundary model ctx stack Q packet record proofs = .done none := by
  simp [verifySource,invalid]

theorem verifySource_rejected_shape (cap : Nat) (boundary : Boundary)
    (model : WHIRCallerSupport.ProductionLayout) (ctx : RawWHIRKeys.Context) (stack : ctx.mode = .stack)
    (Q : Nat) (packet : RawWHIRKeys.Packet ctx Q) (record : Record) (proofs : Array PrunedMerklePaths)
    (foreign : record.shape ≠ AnchoredSourceCaller.shape model.layout) :
    verifySource cap boundary model ctx stack Q packet record proofs = .done none := by
  by_cases configured : configuration packet.val.profile record
  · simp [verifySource,configured,foreign]
  · simp [verifySource,configured]

theorem verifySource_counted (cap : Nat) (boundary : Boundary) (model : WHIRCallerSupport.ProductionLayout)
    (ctx : RawWHIRKeys.Context) (stack : ctx.mode = .stack) (Q : Nat)
    (packet : RawWHIRKeys.Packet ctx Q) (record : Record) (proofs : Array PrunedMerklePaths) :
    Counts (sourceBudget ctx Q packet) (verifySource cap boundary model ctx stack Q packet record proofs) := by
  unfold verifySource
  split
  · split
    · trivial
    · change Counts _ (readCallerInputs _ _ _ _ _ _)
      apply readCallerInputs_counted
      intro answers
      split
      · trivial
      · change Counts _ (readPhysicalPackets ctx stack Q packet.val.profile record.shape.lanes proofs none _ _ _ _)
        apply readPhysicalPackets_counted ctx stack Q packet.val.profile
          _ proofs none _ (completion_profiles ctx Q packet) _ _ 0
        intro state history
        trivial
  · trivial

/-- Failure is false on rejection. Successful claims are the original decoded native caller claims, and the selector is one immutable record across all sessions. The physical Merkle and mode bridges are separate obligations, not assumed claim coverage. -/
def nativeWrong (p : ParameterBounds.Profile) (commitment : CommitmentAnchor.Commitment p)
    (claims : CausalBindingState.OriginalClaims cap) : Prop :=
  ¬ ∃ witness, CommitmentAnchor.boundWitness p commitment = some witness ∧
    RingPCSGame.Honest (ParameterBounds.config p) commitment.lanes claims.family claims.points witness

/-- The root list is computed only from the existing first frozen record table. Neither the original point nor the advertised value contributes to its reconstruction. -/
noncomputable def anchoredView (p : ParameterBounds.Profile) (state : CausalBindingState.State cap)
    (record : Record) (configured : configuration p record) : CommitmentAnchor.Commitment p where
  lanes := record.shape.lanes
  root := (CausalBindingState.capture state p record.root record.shape.lanes
    (by rw [← configured.2.2.1]; exact configured.1.1.2.2.2.2.2)).base
  point := fun i => record.point[i.val]'(by rw [configured.1.2.2,configured.2.1]; exact i.isLt)
  value := record.value
  occupied := ⟨configured.1.1.2.2.2.2.1,by
    rw [← configured.2.2.1]; exact configured.1.1.2.2.2.2.2⟩

def failure {ctx : RawWHIRKeys.Context} {Q cap : Nat} {packet : RawWHIRKeys.Packet ctx Q} {record : Record}
    (state : CausalBindingState.State cap) :
    Option (Accepted ctx Q cap packet record) → Prop
  | none => False
  | some accepted => nativeWrong packet.val.profile
      (anchoredView packet.val.profile state record accepted.configuration) accepted.request.claims

theorem anchored_list_bound (p : ParameterBounds.Profile) (state : CausalBindingState.State cap)
    (record : Record) (configured : configuration p record) :
    (InitialCandidates.witnesses (ParameterBounds.config p) record.shape.lanes
      (anchoredView p state record configured).root).card ≤ 2^32 :=
  InitialCandidates.production_witnesses_card p _ _

/-- Outside one original-point ambiguity event, all later fresh sessions and all their adaptive claim choices share this one selector. -/
theorem honest_anchor_selects (p : ParameterBounds.Profile) (commitment : CommitmentAnchor.Commitment p)
    (clean : ¬ CommitmentAnchor.Ambiguous p commitment.lanes commitment.root commitment.point)
    (claims : CausalBindingState.OriginalClaims cap)
    (w : CausalGame.Witness (ParameterBounds.config p) commitment.lanes)
    (candidate : w ∈ InitialCandidates.witnesses (ParameterBounds.config p) commitment.lanes commitment.root)
    (anchor : CommitmentAnchor.value (ParameterBounds.config p) commitment.lanes w
      (Array.ofFn commitment.point) = commitment.value)
    (honest : RingPCSGame.Honest (ParameterBounds.config p) commitment.lanes claims.family claims.points w) :
    ¬ nativeWrong p commitment claims := by
  intro wrong
  have selected : w ∈ CommitmentAnchor.selected p commitment.lanes commitment.root
      commitment.point commitment.value := Finset.mem_filter.mpr ⟨candidate,anchor⟩
  exact wrong ⟨w,CommitmentAnchor.boundWitness_eq p commitment clean w selected,honest⟩

/-- Every accepted result carries the literal native occupied-anchor check, with the same retained record. This theorem exposes no caller-chosen evaluator or acceptance-proof input. -/
theorem accepted_native {ctx : RawWHIRKeys.Context} {Q cap : Nat}
    {packet : RawWHIRKeys.Packet ctx Q} {record : Record} (accepted : Accepted ctx Q cap packet record) :
    ∃ seed lambda proof,
      AnchoredPhysicalAnchor.sourceVerify record accepted.request.claims.family accepted.request.claims.points
        seed lambda (ParameterBounds.config packet.val.profile)
        (CausalGame.challenges (ParameterBounds.config packet.val.profile) accepted.wire.tape) proof = .ok () := by
  obtain ⟨⟨seed,lambda⟩,proof,_,_,native⟩ := accepted.acceptance
  exact ⟨seed,lambda,proof,native⟩

theorem accepted_record_origin {ctx : RawWHIRKeys.Context} {Q cap : Nat}
    {packet : RawWHIRKeys.Packet ctx Q} {record : Record} (accepted : Accepted ctx Q cap packet record) :
    ∃ (boundary : Boundary) (layout : WHIRCallerClaims.CallerLayout)
      (answers : Coordinate → Option Digest32) (decoded : AnchoredSourceCaller.Claims), decodeCaller boundary layout record
      (RawWHIRKeys.entry ctx packet.val) (fun q => (answers q).getD DuplexRefinement.zeroDigest) = some decoded ∧
      decoded.record = record ∧ accepted.request.root = record.root ∧ accepted.request.lanes = record.shape.lanes := by
  obtain ⟨boundary,model,answers,_,parsed⟩ := accepted.origin
  obtain ⟨decoded,parsed,matched,root,lanes⟩ :=
    request_origin boundary cap packet.val.profile model.layout record (RawWHIRKeys.entry ctx packet.val) answers
      accepted.request parsed
  exact ⟨boundary,model.layout,answers,decoded,parsed,matched,root,lanes⟩

theorem accepted_nativeShapes {ctx : RawWHIRKeys.Context} {Q cap : Nat}
    {packet : RawWHIRKeys.Packet ctx Q} {record : Record} (accepted : Accepted ctx Q cap packet record) :
    SuccinctRingWeight.FamilyShape (ParameterBounds.config packet.val.profile).logN accepted.request.claims.family ∧
    (∀ point ∈ accepted.request.claims.points.toList,
      SuccinctPointWeight.Shape (ParameterBounds.config packet.val.profile).logN point) := by
  obtain ⟨boundary,model,answers,same,parsed⟩ := accepted.origin
  exact request_nativeShapes boundary cap packet.val.profile model record accepted.configuration same
    (RawWHIRKeys.entry ctx packet.val) answers accepted.request parsed

end Whir.AnchoredPhysicalDriver
