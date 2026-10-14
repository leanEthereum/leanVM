import Whir.AnchoredPhysicalKnowledgeAcceptance
import Whir.CountedCandidateCheckOriginalCorrectness

/-! Original-claim preparation is computed from the exact executed anchored
request. No separately chosen public caller or semantic matching certificate is
used. PCS public metadata/capture matching remains a separate boundary. -/
namespace Whir.AnchoredPhysicalPreparation
open Concrete Protocol FiatShamirGame DuplexModeGame
open WHIRCallerClaims WHIRCallerSupport AnchoredPhysicalDriver
open WHIRPhysicalVerifier WHIRPhysicalReplay WHIRSourceChronology PublicMerkleProgram
open MerkleTransport
set_option maxHeartbeats 800000

private def extentOf (bound : Nat) : RingPCSGame.PointClaim → Prop
  | .point offset point _ => offset + 2^point.size ≤ bound
  | .strided offset _ stride point _ => offset + 2^(stride+point.size) ≤ bound

private theorem point_extent (sources : Array Source) (ps : Array Placement)
    (built : placementsOf sources = some ps) (column : ColumnClaim) (placement : Placement)
    (atColumn : ps[column.column]? = some placement)
    (fits : columnFits sources column.column column.point.length = true)
    (claim : RingPCSGame.PointClaim) (placed : placeClaim placement column = some claim) :
    extentOf (placedWords sources) claim := by
  have hp := placementsOf_get sources ps built column.column placement atColumn
  by_cases sliced : sources[column.column]? = some .sliced
  · simp [WHIRCallerSupport.placement,sliced] at hp
    subst placement
    simp [placeClaim] at placed
  · have dimension : ∃ rows, columnDimension sources column.column = some rows ∧ column.point.length ≤ rows := by
      unfold columnFits at fits
      simp only [Bool.and_eq_true] at fits
      cases hs : sources[column.column]? with
      | none => simp [columnDimension,hs] at fits
      | some source =>
        cases source with
        | sliced => exact False.elim (sliced hs)
        | committed d =>
          cases hd : columnDimension sources column.column with
          | none => simp [hd] at fits
          | some rows => exact ⟨rows,rfl,by simpa [hd] using fits.2⟩
        | port packed slot stride =>
          cases hd : columnDimension sources column.column with
          | none => simp [hd] at fits
          | some rows => exact ⟨rows,rfl,by simpa [hd] using fits.2⟩
    obtain ⟨rows,hd,length⟩ := dimension
    have extent := placement_extent sources column.column rows placement hp hd
    cases placement with
    | committed offset dimension =>
      simp only [placeClaim,Option.some.injEq] at placed
      subst claim
      change rows ≤ dimension ∧ offset + 2^dimension ≤ placedWords sources at extent
      have power : 2^column.point.length ≤ 2^dimension :=
        Nat.pow_le_pow_right (by decide) (length.trans extent.1)
      simp only [extentOf,List.size_toArray]
      omega
    | port offset slot stride =>
      simp only [placeClaim,Option.some.injEq] at placed
      subst claim
      change offset + 2^(stride+rows) ≤ placedWords sources at extent
      have power : 2^(stride+column.point.length) ≤ 2^(stride+rows) :=
        Nat.pow_le_pow_right (by decide) (Nat.add_le_add_left length stride)
      simp only [extentOf,List.size_toArray]
      omega
    | sliced => simp [placeClaim] at placed

private theorem decoded_guards (p : ParameterBounds.Profile) (model : ProductionLayout)
    (record : AnchoredHeaderCodec.Record) (configured : configuration p record)
    (same : record.shape = AnchoredSourceCaller.shape model.layout)
    (decoded : AnchoredSourceCaller.Claims)
    (geometry : WHIRCallerGeometry.ClaimsValid
      (fun i d => columnFits model.sources i d = true)
      (fun o d => ringFits model.sources o d = true) (callerPlacements model.layout) decoded.caller) :
    OriginalClaimsChecker.Guards (ParameterBounds.config p) record.shape.lanes
      (fun i : Fin decoded.caller.families.length => decoded.caller.families[i])
      decoded.caller.points record.point.toArray := by
  have metadata := opening_metadata model p record configured same
  have laneBound : record.shape.lanes ≤ 2^(ParameterBounds.config p).folds[0]! := by
    rw [← configured.2.2.1]
    exact configured.1.1.2.2.2.2.2
  have shapes := geometry_nativeShapes model p record.shape.lanes metadata laneBound decoded.caller geometry
  have support := geometry_support model decoded.caller geometry
  have occupied := openingMatches_occupied model.layout p record.shape.lanes metadata
  have valid := configured.1
  refine ⟨?_,?_,?_,laneBound,?_,?_,?_⟩
  · rw [← configured.2.2.1,← configured.2.1]
    exact Nat.le_of_lt valid.1.1
  · rw [← configured.2.1]
    exact Nat.le_of_lt valid.1.2.1
  · exact lt_of_lt_of_le (by decide : 0 < 1) valid.1.2.2.2.2.1
  · simpa only [List.size_toArray] using valid.2.2.trans configured.2.1
  · intro j
    have native := shapes.1 j
    exact ⟨native.1,native.2.1,(support.1 _ (by simp)).trans occupied⟩
  · intro i
    have native := shapes.2 decoded.caller.points[i] (by simp)
    obtain ⟨column,placement,atColumn,placed,fits⟩ := geometry.2 decoded.caller.points[i] (by simp)
    have extent := point_extent model.sources (callerPlacements model.layout) model.constructed
      column placement atColumn fits _ placed
    rw [← callerWords_placementsOf model.sources model.layout model.constructed] at extent
    cases claimEq : decoded.caller.points[i] with
    | point offset point value =>
      rw [claimEq] at native extent
      obtain ⟨dimension,aligned,range⟩ := (SuccinctPointWeight.Shape.point_iff _ _ _ _).mp native
      change offset + 2^point.size ≤ callerWords model.layout at extent
      exact ⟨dimension,aligned,extent.trans occupied⟩
    | strided offset slot stride point value =>
      rw [claimEq] at native extent
      obtain ⟨dimension,aligned,range,slotBound⟩ := (SuccinctPointWeight.Shape.strided_iff _ _ _ _ _ _).mp native
      change offset + 2^(stride+point.size) ≤ callerWords model.layout at extent
      exact ⟨dimension,slotBound,aligned,extent.trans occupied⟩

/-- Exact parser success, not `Accepted.origin`, supplies preparation guards. -/
 theorem request_guards (boundary : Boundary) (cap : Nat) (p : ParameterBounds.Profile)
    (model : ProductionLayout) (record : AnchoredHeaderCodec.Record)
    (configured : configuration p record) (same : record.shape = AnchoredSourceCaller.shape model.layout)
    (entry : FramedHistory) (answers : Coordinate → Option Digest32)
    (result : CausalBindingState.ClaimRequest cap p)
    (accepted : AnchoredPhysicalDriver.request boundary cap p model.layout record entry answers = some result) :
    OriginalClaimsChecker.Guards (ParameterBounds.config p) record.shape.lanes
      result.claims.family result.claims.points record.point.toArray := by
  unfold AnchoredPhysicalDriver.request at accepted
  split at accepted
  next present =>
    cases parsed : AnchoredPhysicalDriver.decodeCaller boundary model.layout record entry
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
              exact decoded_guards p model record configured same decoded
                (decodeCaller_geometry boundary model record entry _ decoded parsed)
            next => contradiction
          next => contradiction
        next => contradiction
  next => contradiction

/-- Preparation and its exact public-input equality follow from actual receiver
execution. This statement works for both receiver boundaries, without equating
the original and fresh decoders. -/
 theorem verifySource_preparation (cap : Nat) (boundary : Boundary)
    (model : ProductionLayout) (ctx : RawWHIRKeys.Context) (stack : ctx.mode = .stack)
    (Q : Nat) (packet : RawWHIRKeys.Packet ctx Q) (record : AnchoredHeaderCodec.Record)
    (proofs : Array PrunedMerklePaths) (observations : List Observation)
    (a : Accepted ctx Q cap packet record)
    (run : Runs (erase (AnchoredPhysicalDriver.verifySource cap boundary model ctx stack Q packet record proofs))
      observations (some a)) :
    ∃ prepared : OriginalClaimsChecker.Prepared (ParameterBounds.config packet.val.profile) record.shape.lanes
      a.request.claims.count a.request.claims.family a.request.claims.points record.point.toArray record.value,
      OriginalClaimsChecker.prepare (ParameterBounds.config packet.val.profile) record.shape.lanes
        a.request.claims.family a.request.claims.points record.point.toArray record.value = some prepared ∧
      ∀ (state : CausalBindingState.State cap) (seed : RingPCSGame.Prefix),
        OriginalClaimsChecker.input prepared (AnchoredPhysicalKnowledgeAcceptance.original a state).root seed =
          AnchoredPhysicalKnowledgeAcceptance.input a state seed := by
  obtain ⟨configured,same,before,after,request,_,_,_,parsed,_⟩ :=
    AnchoredPhysicalExecution.verifySource_success cap boundary model ctx stack Q packet record proofs observations a run
  obtain ⟨⟨before',after',_,_,_,actual⟩,_,_,_,_⟩ :=
    AnchoredPhysicalExecution.verifySource_execution cap boundary model ctx stack Q packet record proofs observations a run
  have guards := request_guards boundary cap packet.val.profile model record configured same
    (RawWHIRKeys.entry ctx packet.val) (WHIRPhysicalCaller.latestAnswers before') a.request actual
  cases hp : OriginalClaimsChecker.prepare (ParameterBounds.config packet.val.profile) record.shape.lanes
      a.request.claims.family a.request.claims.points record.point.toArray record.value with
  | none => simp [OriginalClaimsChecker.prepare,dite_eq_left guards] at hp
  | some cached =>
    refine ⟨cached,rfl,?_⟩
    intro state seed
    exact congrArg (fun claims => CausalGame.Public.mk (ParameterBounds.config packet.val.profile)
      record.shape.lanes (AnchoredPhysicalKnowledgeAcceptance.original a state).root claims)
      (OriginalClaimsChecker.input_claims cached (AnchoredPhysicalKnowledgeAcceptance.original a state).root seed)

/-- Successful anchored opening parsing forces completion of the actual packet
schedule, including its possible hidden terminal sample. -/
theorem accepted_completed_depth {ctx : RawWHIRKeys.Context} {stack : ctx.mode = .stack} {Q cap : Nat}
    {packet : RawWHIRKeys.Packet ctx Q} {record : AnchoredHeaderCodec.Record}
    (a : Accepted ctx Q cap packet record) (complete : Completed stack packet a.wire a.history) :
    packet.val.messages.length = WHIRHistory.depth (ParameterBounds.config packet.val.profile) := by
  obtain ⟨_,_,_,_,_,_,_,_,_,_,size,_,_⟩ := complete
  obtain ⟨_,proof,_,parsed,_⟩ := a.acceptance
  have count := CausalRefinement.checkReplies_length _ _
    ((CausalRefinement.opening_ok_iff _ _ _ _).mp parsed).1
  have stream := congrArg List.length
    (CausalProbability.visibleCoordinates_map (ParameterBounds.config packet.val.profile) a.wire.tape)
  simp only [List.length_map] at stream
  have length : a.wire.replies.size =
      (CausalProbability.visibleCoordinates (ParameterBounds.config packet.val.profile)).length := by
    calc
      a.wire.replies.size = (CausalGame.visibleBatches (ParameterBounds.config packet.val.profile)
        E.zero (CausalGame.challenges (ParameterBounds.config packet.val.profile) a.wire.tape)).length := count
      _ = (CausalGame.visibleBatches (ParameterBounds.config packet.val.profile)
        a.wire.tape.1 (CausalGame.challenges (ParameterBounds.config packet.val.profile) a.wire.tape)).length := by
        simp only [CausalGame.visibleBatches,List.length_append,List.length_singleton]
      _ = _ := stream.symm
  have max := RawWHIRKeys.packet_depth ctx Q packet
  have hidden : (WHIRHistory.hiddenTail (ParameterBounds.config packet.val.profile)).length ≤ 1 := by
    unfold WHIRHistory.hiddenTail
    split <;> simp
  simp only [WHIRHistory.depth,WHIRHistory.schedule,List.length_append] at max ⊢
  omega

/-- End-to-end deterministic endpoint on the actual request's prepared original
claims, the restored replies, and the same physical tape. The remaining public
PCS capture/metadata identity is not smuggled in as a matching certificate. -/
theorem verifySource_prepared_experiment (cap : Nat) (boundary : Boundary)
    (model : ProductionLayout) (ctx : RawWHIRKeys.Context) (stack : ctx.mode = .stack)
    (Q : Nat) (packet : RawWHIRKeys.Packet ctx Q) (record : AnchoredHeaderCodec.Record)
    (proofs : Array PrunedMerklePaths) (observations : List Observation)
    (a : Accepted ctx Q cap packet record)
    (run : Runs (erase (AnchoredPhysicalDriver.verifySource cap boundary model ctx stack Q packet record proofs))
      observations (some a))
    (C : PrimitiveOracle) (iv : Digest32)
    (answers : ∀ o ∈ observations, o.answer = realAnswer C iv o.query)
    (state : CausalBindingState.State cap) (invariant : WHIRPhysicalSnapshots.Invariant C state)
    (initial : ∃ snap, Commitments.lookup record.root state.registry = some snap)
    (registered : CausalBindingState.Prepared state packet.val.profile ⟨packet.val.statement,packet.val.messages,[]⟩)
    (quiet : ∀ opening ∈ a.wire.openings, ∀ oldLog, state.frozenLog opening.root = some oldLog →
      ¬ PublicMerkleBinding.OpenPrimitiveBad C oldLog opening.root opening.result.paths) :
    ∃ prepared : OriginalClaimsChecker.Prepared (ParameterBounds.config packet.val.profile) record.shape.lanes
        a.request.claims.count a.request.claims.family a.request.claims.points record.point.toArray record.value,
      ∃ (replay : StackWHIRReplay.Replay packet.val.profile cap) (proof : Opening),
        OriginalClaimsChecker.prepare (ParameterBounds.config packet.val.profile) record.shape.lanes
          a.request.claims.family a.request.claims.points record.point.toArray record.value = some prepared ∧
        packet.val.messages.length = WHIRHistory.depth (ParameterBounds.config packet.val.profile) ∧
        replay.original = AnchoredPhysicalKnowledgeAcceptance.original a state ∧
        a.wire.initial = some replay.initial ∧ a.wire.tape.1 = replay.initial.2 ∧
        replay.whir.replies.map WHIRPhysicalErasure.eraseReply = a.wire.replies ∧
        CausalGame.opening (ParameterBounds.config packet.val.profile)
          (CausalGame.challenges (ParameterBounds.config packet.val.profile) a.wire.tape) replay.whir.replies = .ok proof ∧
        (let claims := (OriginalClaimsChecker.input prepared
          (AnchoredPhysicalKnowledgeAcceptance.original a state).root replay.initial.1).claims
         let claim := CausalGame.batchClaims (2^(ParameterBounds.config packet.val.profile).logN) claims a.wire.tape.1
         Protocol.verify (ParameterBounds.config packet.val.profile)
           (CausalGame.challenges (ParameterBounds.config packet.val.profile) a.wire.tape) record.shape.lanes
           (CausalGame.liftRoot (AnchoredPhysicalKnowledgeAcceptance.original a state).root)
           claim.weight claim.value proof = .ok ()) ∧
        CausalGame.experiment
          (OriginalClaimsChecker.input prepared (AnchoredPhysicalKnowledgeAcceptance.original a state).root replay.initial.1)
          (CausalStrategy.indexedStrategy replay.whir.replies) a.wire.tape = true := by
  obtain ⟨prepared,preparedEq,inputEq⟩ := verifySource_preparation cap boundary model ctx stack Q packet record
    proofs observations a run
  obtain ⟨replay,proof,originalEq,seed,lambda,erased,parsed,verified,experiment⟩ :=
    AnchoredPhysicalKnowledgeAcceptance.verifySource_experiment cap boundary model ctx stack Q packet record
      proofs observations a run C iv answers state invariant initial registered quiet
  obtain ⟨_,_,_,trace,_⟩ := AnchoredPhysicalExecution.verifySource_execution cap boundary model ctx stack Q
    packet record proofs observations a run
  have complete := trace_completed record.root (completion_chain ctx Q packet) trace
  have claimsEq := congrArg CausalGame.Public.claims (inputEq state replay.initial.1)
  have preparedVerified :
      let claims := (OriginalClaimsChecker.input prepared
        (AnchoredPhysicalKnowledgeAcceptance.original a state).root replay.initial.1).claims
      let claim := CausalGame.batchClaims (2^(ParameterBounds.config packet.val.profile).logN) claims a.wire.tape.1
      Protocol.verify (ParameterBounds.config packet.val.profile)
        (CausalGame.challenges (ParameterBounds.config packet.val.profile) a.wire.tape) record.shape.lanes
        (CausalGame.liftRoot (AnchoredPhysicalKnowledgeAcceptance.original a state).root)
        claim.weight claim.value proof = .ok () := by
    simpa only [claimsEq] using verified
  refine ⟨prepared,replay,proof,preparedEq,accepted_completed_depth a complete,originalEq,seed,lambda,erased,parsed,preparedVerified,?_⟩
  have experimentEq := congrArg (fun claims =>
    CausalGame.experiment
      (CausalGame.Public.mk (ParameterBounds.config packet.val.profile) record.shape.lanes
        (AnchoredPhysicalKnowledgeAcceptance.original a state).root claims)
      (CausalStrategy.indexedStrategy replay.whir.replies) a.wire.tape) claimsEq
  exact experimentEq.trans experiment

private theorem real_answers {R : Type} (C : PrimitiveOracle) (iv : Digest32) (program : Program R) :
    ∀ o ∈ (runReal C iv program).view.observations, o.answer = realAnswer C iv o.query := by
  induction program with
  | done value => simp [runReal]
  | ask query next ih =>
    intro o member
    rcases List.mem_cons.mp member with same | rest
    · subst o
      rfl
    · exact ih (realAnswer C iv query) o rest

/-- Actual compiled real receiver success. Answer consistency is now derived
from execution itself. The observer snapshot registration/capture interface is
the only remaining outer boundary; no PCS public-capture identity is claimed. -/
theorem real_verifySource_prepared_experiment (cap : Nat) (boundary : Boundary)
    (model : ProductionLayout) (ctx : RawWHIRKeys.Context) (stack : ctx.mode = .stack)
    (Q : Nat) (packet : RawWHIRKeys.Packet ctx Q) (record : AnchoredHeaderCodec.Record)
    (proofs : Array PrunedMerklePaths) (C : PrimitiveOracle) (iv : Digest32)
    (a : Accepted ctx Q cap packet record)
    (success : (runReal C iv (compile
      (AnchoredPhysicalDriver.verifySource cap boundary model ctx stack Q packet record proofs))).view.result.value = some a)
    (state : CausalBindingState.State cap) (invariant : WHIRPhysicalSnapshots.Invariant C state)
    (initial : ∃ snap, Commitments.lookup record.root state.registry = some snap)
    (registered : CausalBindingState.Prepared state packet.val.profile ⟨packet.val.statement,packet.val.messages,[]⟩)
    (quiet : ∀ opening ∈ a.wire.openings, ∀ oldLog, state.frozenLog opening.root = some oldLog →
      ¬ PublicMerkleBinding.OpenPrimitiveBad C oldLog opening.root opening.result.paths) :
    ∃ prepared : OriginalClaimsChecker.Prepared (ParameterBounds.config packet.val.profile) record.shape.lanes
        a.request.claims.count a.request.claims.family a.request.claims.points record.point.toArray record.value,
      ∃ (replay : StackWHIRReplay.Replay packet.val.profile cap) (proof : Opening),
        OriginalClaimsChecker.prepare (ParameterBounds.config packet.val.profile) record.shape.lanes
          a.request.claims.family a.request.claims.points record.point.toArray record.value = some prepared ∧
        packet.val.messages.length = WHIRHistory.depth (ParameterBounds.config packet.val.profile) ∧
        replay.original = AnchoredPhysicalKnowledgeAcceptance.original a state ∧
        a.wire.initial = some replay.initial ∧ a.wire.tape.1 = replay.initial.2 ∧
        replay.whir.replies.map WHIRPhysicalErasure.eraseReply = a.wire.replies ∧
        CausalGame.opening (ParameterBounds.config packet.val.profile)
          (CausalGame.challenges (ParameterBounds.config packet.val.profile) a.wire.tape) replay.whir.replies = .ok proof ∧
        (let claims := (OriginalClaimsChecker.input prepared
          (AnchoredPhysicalKnowledgeAcceptance.original a state).root replay.initial.1).claims
         let claim := CausalGame.batchClaims (2^(ParameterBounds.config packet.val.profile).logN) claims a.wire.tape.1
         Protocol.verify (ParameterBounds.config packet.val.profile)
           (CausalGame.challenges (ParameterBounds.config packet.val.profile) a.wire.tape) record.shape.lanes
           (CausalGame.liftRoot (AnchoredPhysicalKnowledgeAcceptance.original a state).root)
           claim.weight claim.value proof = .ok ()) ∧
        CausalGame.experiment
          (OriginalClaimsChecker.input prepared (AnchoredPhysicalKnowledgeAcceptance.original a state).root replay.initial.1)
          (CausalStrategy.indexedStrategy replay.whir.replies) a.wire.tape = true := by
  let source := AnchoredPhysicalDriver.verifySource cap boundary model ctx stack Q packet record proofs
  have run := WHIRPhysicalCaller.real_source_runs C iv source
  change (runReal C iv (compile source)).view.result.value = some a at success
  rw [success] at run
  have answers : ∀ o ∈ observations (runReal C iv (compile source)).view.result.events,
      o.answer = realAnswer C iv o.query := by
    rw [real_source_trace]
    exact real_answers C iv (compile source)
  exact verifySource_prepared_experiment cap boundary model ctx stack Q packet record proofs
    _ a run C iv answers state invariant initial registered quiet

#print axioms real_verifySource_prepared_experiment

#print axioms accepted_completed_depth
#print axioms verifySource_prepared_experiment

#print axioms request_guards
#print axioms verifySource_preparation
end Whir.AnchoredPhysicalPreparation
