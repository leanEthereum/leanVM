import Whir.AnchoredPhysicalExecution
import Whir.AnchorPrefixRefinementCaller
import Whir.WHIRNativeErasure

/-! Deterministic acceptance at the physical observer's first-frozen capture.
The input is constructed from the executed request and immutable anchor. This
is deliberately not a PCS cross-sampler capture-identity theorem. Snapshot
registration and quietness refer to the actual retained opener executions. -/
namespace Whir.AnchoredPhysicalKnowledgeAcceptance
open Concrete Protocol FiatShamirGame DuplexModeGame
open MerkleTransport MerkleTransport.Commitments
open WHIRPhysicalVerifier WHIRPhysicalReplay WHIRPhysicalOpeningRuns WHIRPhysicalSoundness
open PublicMerkleProgram WHIRSourceChronology AnchoredPhysicalDriver
set_option maxHeartbeats 800000

 theorem sourceVerify_erased {m : Nat} (record : AnchoredHeaderCodec.Record)
    (family : Fin m → RingPCSGame.FamilyClaim) (points : Array RingPCSGame.PointClaim)
    (seed : RingPCSGame.Prefix) (lambda : E) (c : Config) (ch : Challenges) (proof : Opening) :
    AnchoredPhysicalAnchor.sourceVerify record family points seed lambda c ch
      (WHIRPhysicalErasure.eraseOracles proof) =
      AnchoredPhysicalAnchor.sourceVerify record family points seed lambda c ch proof :=
  WHIRNativeErasure.nativeVerify_erased c ch record.shape.lanes
    (AnchoredPhysicalAnchor.initialClaim record family points seed lambda)
    (AnchoredPhysicalAnchor.callerAt record family points seed lambda) proof

private theorem opening_unerase (c : Config) (ch : Challenges)
    (replies : Array CausalGame.Reply) (erased : Opening)
    (accepted : CausalGame.opening c ch (replies.map WHIRPhysicalErasure.eraseReply) = .ok erased) :
    ∃ proof, CausalGame.opening c ch replies = .ok proof ∧ WHIRPhysicalErasure.eraseOracles proof = erased := by
  rw [WHIRPhysicalErasure.opening_erase] at accepted
  cases parsed : CausalGame.opening c ch replies with
  | error message => simp [parsed,Except.map] at accepted
  | ok proof =>
    simp [parsed,Except.map] at accepted
    exact ⟨proof,rfl,accepted⟩

noncomputable def original {ctx : RawWHIRKeys.Context} {Q cap : Nat}
    {packet : RawWHIRKeys.Packet ctx Q} {record : AnchoredHeaderCodec.Record}
    (a : Accepted ctx Q cap packet record) (state : CausalBindingState.State cap) :
    WHIRFiatShamir.StackInitial packet.val.profile cap :=
  CausalBindingState.bindClaims
    (CausalBindingState.capture state packet.val.profile a.request.root a.request.lanes a.request.lane_bound)
    a.request.claims

noncomputable def input {ctx : RawWHIRKeys.Context} {Q cap : Nat}
    {packet : RawWHIRKeys.Packet ctx Q} {record : AnchoredHeaderCodec.Record}
    (a : Accepted ctx Q cap packet record) (state : CausalBindingState.State cap)
    (seed : RingPCSGame.Prefix) : CausalGame.Public where
  config := ParameterBounds.config packet.val.profile
  lanes := record.shape.lanes
  root := (original a state).root
  claims := AnchorPrefixRefinement.anchoredClaims (ParameterBounds.config packet.val.profile) record
    a.request.claims.family a.request.claims.points seed

 theorem replies_nonempty {ctx : RawWHIRKeys.Context} {Q cap : Nat}
    {packet : RawWHIRKeys.Packet ctx Q} {record : AnchoredHeaderCodec.Record}
    (a : Accepted ctx Q cap packet record) : a.wire.replies ≠ #[] := by
  intro empty
  obtain ⟨_,_,_,parsed,_⟩ := a.acceptance
  rw [empty] at parsed
  simp [CausalGame.opening,CausalGame.visibleBatches,CausalGame.checkReplies] at parsed

/-- The bound rows are a conclusion of actual opener execution, authentic
retained snapshots, and absence of the executed Merkle bad events. -/
 theorem execution_boundRows {ctx : RawWHIRKeys.Context} {stack : ctx.mode = .stack} {Q cap : Nat}
    (C : PrimitiveOracle) (iv : Digest32) (packet : RawWHIRKeys.Packet ctx Q)
    (record : AnchoredHeaderCodec.Record) (proofs : Array PrunedMerklePaths)
    (a : Accepted ctx Q cap packet record) (observations : List Observation)
    (answers : ∀ o ∈ observations, o.answer = realAnswer C iv o.query)
    (observed : ∀ opening ∈ a.wire.openings, ObservedOpening a.request.lanes proofs observations opening)
    (trace : Trace ctx stack Q packet.val.profile a.request.lanes proofs
      (RawOracleCoupling.Concrete.completion ctx Q packet)
      (initialWireState packet.val.profile a.request.root) a.wire a.history)
    (state : CausalBindingState.State cap) (invariant : WHIRPhysicalSnapshots.Invariant C state)
    (initial : ∃ snap, lookup a.request.root state.registry = some snap)
    (prepared : CausalBindingState.Prepared state packet.val.profile ⟨packet.val.statement,packet.val.messages,[]⟩)
    (quiet : ∀ opening ∈ a.wire.openings, ∀ oldLog, state.frozenLog opening.root = some oldLog →
      ¬ PublicMerkleBinding.OpenPrimitiveBad C oldLog opening.root opening.result.paths) :
    WHIRPhysicalRoots.BoundRows (original a state).root (CausalBindingState.roots state packet.val.profile) a.wire := by
  intro opening member
  have chain := completion_chain ctx Q packet
  obtain ⟨snapshot,known⟩ := trace_opening_registered packet a.request.root chain trace state
    initial prepared opening member
  obtain ⟨retained,oldLog,_,frozen,authentic,history,saturated,table⟩ :=
    invariant.retained opening.root snapshot known
  rcases observed_binding (observed opening member) C iv answers oldLog authentic
    retained history saturated snapshot table with bound | bad
  · rw [frozenQueryOracle_state C state invariant packet.val.profile opening.root snapshot known
      opening.level.val a.request.lanes a.request.lane_bound] at bound
    by_cases base : opening.level.val = 0
    · have rootEq := trace_base_opening_root packet a.request.root chain trace opening member base
      simpa only [base,ite_true,rootEq,original,CausalBindingState.bindClaims] using bound
    · simpa only [ite_eq_right base] using bound
  · exact False.elim (quiet opening member oldLog frozen bad)

/-- Erased physical acceptance is restored to protocol and experiment success
on the same actual tape, at the physical first-frozen captured base. There are
no accepted-experiment, semantic-equivalence, root-shape or authenticated-row
premises. The catalog used in the proof is a local constant decoding scaffold. -/
 theorem verifySource_experiment (cap : Nat) (boundary : Boundary)
    (model : WHIRCallerSupport.ProductionLayout) (ctx : RawWHIRKeys.Context)
    (stack : ctx.mode = .stack) (Q : Nat) (packet : RawWHIRKeys.Packet ctx Q)
    (record : AnchoredHeaderCodec.Record) (proofs : Array PrunedMerklePaths)
    (observations : List Observation) (a : Accepted ctx Q cap packet record)
    (run : Runs (erase (AnchoredPhysicalDriver.verifySource cap boundary model ctx stack Q packet record proofs))
      observations (some a))
    (C : PrimitiveOracle) (iv : Digest32)
    (answers : ∀ o ∈ observations, o.answer = realAnswer C iv o.query)
    (state : CausalBindingState.State cap) (invariant : WHIRPhysicalSnapshots.Invariant C state)
    (initial : ∃ snap, lookup record.root state.registry = some snap)
    (prepared : CausalBindingState.Prepared state packet.val.profile ⟨packet.val.statement,packet.val.messages,[]⟩)
    (quiet : ∀ opening ∈ a.wire.openings, ∀ oldLog, state.frozenLog opening.root = some oldLog →
      ¬ PublicMerkleBinding.OpenPrimitiveBad C oldLog opening.root opening.result.paths) :
    ∃ (replay : StackWHIRReplay.Replay packet.val.profile cap) (proof : Opening),
      replay.original = original a state ∧ a.wire.initial = some replay.initial ∧
      a.wire.tape.1 = replay.initial.2 ∧
      replay.whir.replies.map WHIRPhysicalErasure.eraseReply = a.wire.replies ∧
      CausalGame.opening (ParameterBounds.config packet.val.profile)
        (CausalGame.challenges (ParameterBounds.config packet.val.profile) a.wire.tape) replay.whir.replies = .ok proof ∧
      Protocol.verify (ParameterBounds.config packet.val.profile)
        (CausalGame.challenges (ParameterBounds.config packet.val.profile) a.wire.tape) record.shape.lanes
        (CausalGame.liftRoot (original a state).root)
        (CausalGame.batchClaims (2^(ParameterBounds.config packet.val.profile).logN)
          (input a state replay.initial.1).claims a.wire.tape.1).weight
        (CausalGame.batchClaims (2^(ParameterBounds.config packet.val.profile).logN)
          (input a state replay.initial.1).claims a.wire.tape.1).value proof = .ok () ∧
      CausalGame.experiment (input a state replay.initial.1)
        (CausalStrategy.indexedStrategy replay.whir.replies) a.wire.tape = true := by
  obtain ⟨caller,rootEq,lanesEq,trace,observed⟩ := AnchoredPhysicalExecution.verifySource_execution
    cap boundary model ctx stack Q packet record proofs observations a run
  have trace' : Trace ctx stack Q packet.val.profile a.request.lanes proofs
      (RawOracleCoupling.Concrete.completion ctx Q packet)
      (initialWireState packet.val.profile a.request.root) a.wire a.history := by
    simpa only [rootEq,lanesEq] using trace
  have bound := execution_boundRows C iv packet record proofs a observations answers
    (by simpa only [lanesEq] using observed) trace' state invariant (by simpa only [rootEq] using initial) prepared quiet
  let catalog : StackWHIRReplay.Catalog packet.val.profile cap := fun _ => some (original a state)
  have found : catalog packet.val.statement = some (original a state) := rfl
  have chain := completion_chain ctx Q packet
  have complete := trace_completed a.request.root chain trace'
  obtain ⟨head,past,sample,erased,history,decoded,originalEq,initialSeed,statement,tape,replies⟩ :=
    Completed.decodeStack packet a.wire a.history catalog (original a state) found complete (replies_nonempty a)
  have tail : (localHistory ctx stack Q packet.val.profile a.history).tail = past := by rw [history]; rfl
  have full := decoded
  change WHIRPhysicalHistory.decodeStack packet.val.profile cap catalog WHIRPhysicalErasure.zeroRoots
    (fun i => a.wire.rows[i]!) ⟨packet.val.statement,packet.val.messages,past⟩ = some erased at full
  rw [WHIRPhysicalErasure.decodeStack_zero packet.val.profile cap catalog (CausalBindingState.roots state packet.val.profile)
    (fun i => a.wire.rows[i]!) ⟨packet.val.statement,packet.val.messages,past⟩] at full
  obtain ⟨replay,physical,erasedEq⟩ := Option.map_eq_some_iff.mp full
  subst erased
  change replay.original = original a state at originalEq
  change a.wire.initial = some replay.initial at initialSeed
  change (StackWHIRReplay.finish ⟨packet.val.statement,packet.val.messages,past⟩ replay sample).whir.tape = a.wire.tape at tape
  change replay.whir.replies.map WHIRPhysicalErasure.eraseReply = a.wire.replies at replies
  have agreement := WHIRPhysicalRoots.trace_stackRowsAgree packet a.request.root catalog (original a state)
    (CausalBindingState.roots state packet.val.profile) found chain trace' bound
  rw [tail] at agreement
  have ideal := WHIRPhysicalHistory.decodeStack_success packet.val.profile cap catalog
    (CausalBindingState.roots state packet.val.profile) (fun i => a.wire.rows[i]!)
    ⟨packet.val.statement,packet.val.messages,past⟩ replay agreement physical
  have lambda := StackWHIRReplay.decode_initial_lambda catalog (CausalBindingState.roots state packet.val.profile)
    ⟨packet.val.statement,packet.val.messages,past⟩ replay ideal sample
  rw [tape] at lambda
  change a.wire.tape.1 = replay.initial.2 at lambda
  obtain ⟨seed,nativeProof,seedFound,parsed,native⟩ := a.acceptance
  have sameSeed : seed = replay.initial := Option.some.inj (seedFound.symm.trans initialSeed)
  subst seed
  rw [← replies] at parsed
  obtain ⟨proof,parsedFull,erasedProof⟩ := opening_unerase _ _ replay.whir.replies nativeProof parsed
  have nativeFull : AnchoredPhysicalAnchor.sourceVerify record a.request.claims.family a.request.claims.points
      replay.initial.1 replay.initial.2 (ParameterBounds.config packet.val.profile)
      (CausalGame.challenges (ParameterBounds.config packet.val.profile) a.wire.tape) proof = .ok () := by
    rw [← sourceVerify_erased,erasedProof]
    exact native
  have rootsShape := decodeStack_rootShapes packet.val.profile cap state catalog
    (fun i => a.wire.rows[i]!) ⟨packet.val.statement,packet.val.messages,past⟩ replay physical a.wire.tape proof parsedFull
  have authenticated := trace_authenticatedRows packet a.request.root (original a state).root
    (CausalBindingState.roots state packet.val.profile) chain trace' bound catalog replay
    (by rw [tail]; exact physical) proof parsedFull
  obtain ⟨before,after,_,_,_,callerParsed⟩ := caller
  obtain ⟨_,same,_,_,_,_,_,_,_,_⟩ := AnchoredPhysicalExecution.verifySource_success
    cap boundary model ctx stack Q packet record proofs observations a run
  have shapes := request_anchored_shapes boundary cap packet.val.profile model record a.configuration same
    (RawWHIRKeys.entry ctx packet.val) (WHIRPhysicalCaller.latestAnswers before) a.request callerParsed
    replay.initial.1 replay.initial.2
  have nativeShapes := request_nativeShapes boundary cap packet.val.profile model record a.configuration same
    (RawWHIRKeys.entry ctx packet.val) (WHIRPhysicalCaller.latestAnswers before) a.request callerParsed
  have verified := AnchorPrefixRefinement.sourceVerify_refines record a.request.claims.family a.request.claims.points
    replay.initial.1 replay.initial.2 (ParameterBounds.config packet.val.profile) _ proof
    (CausalGame.liftRoot (original a state).root) a.configuration.1 a.configuration.2.1 a.configuration.2.2.1
    nativeShapes.1 (fun i => nativeShapes.2 _ (by simp)) shapes.2
    (by simpa only [original,CausalBindingState.bindClaims,lanesEq] using
      capture_base_shape state packet.val.profile a.request.root a.request.lanes a.request.lane_bound)
    rootsShape authenticated nativeFull
  have verifiedTape : Protocol.verify (ParameterBounds.config packet.val.profile)
      (CausalGame.challenges (ParameterBounds.config packet.val.profile) a.wire.tape) record.shape.lanes
      (CausalGame.liftRoot (original a state).root)
      (CausalGame.batchClaims (2^(ParameterBounds.config packet.val.profile).logN)
        (input a state replay.initial.1).claims a.wire.tape.1).weight
      (CausalGame.batchClaims (2^(ParameterBounds.config packet.val.profile).logN)
        (input a state replay.initial.1).claims a.wire.tape.1).value proof = .ok () := by
    rw [lambda]
    exact verified
  refine ⟨replay,proof,originalEq,initialSeed,lambda,replies,parsedFull,verifiedTape,?_⟩
  apply experiment_indexed_accepts (input a state replay.initial.1) a.wire.tape replay.whir.replies proof parsedFull
  · exact shapes.1
  · exact verifiedTape

#print axioms sourceVerify_erased
#print axioms execution_boundRows
#print axioms verifySource_experiment
end Whir.AnchoredPhysicalKnowledgeAcceptance
