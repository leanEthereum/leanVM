import Whir.AnchoredPhysicalPreparation
import Whir.PCSBCSMixedOrdinaryMerkle

/-! Acceptance for the historical pre-#607 native anchored source verifier.
Construction answers remain the actual, arbitrary RO packet values. Only the
ordinary verification primitives used by retained Merkle openers must agree
with the seed oracle. This is not a completed PCS/Fiat--Shamir endpoint: the
physical registry, its preparedness, and its first-frozen capture still need
the independent PCS first-capture crosswalk. -/
namespace Whir.AnchoredIdealPhysicalAcceptance
open Concrete Protocol FiatShamirGame DuplexModeGame DuplexFraming
open MerkleTransport MerkleTransport.Commitments
open MerkleBinding
open WHIRPhysicalVerifier WHIRPhysicalReplay WHIRPhysicalOpeningRuns WHIRPhysicalSoundness
open PublicMerkleProgram WHIRSourceChronology AnchoredPhysicalDriver
open AnchoredPhysicalKnowledgeAcceptance (original input replies_nonempty sourceVerify_erased)
open PrunedMerkleProgram
set_option maxHeartbeats 800000

/-- No requirement on construction requests, or on nonordinary primitives. -/
def PrimitiveConsistent (C : PrimitiveOracle) (observations : List Observation) : Prop :=
  ∀ o ∈ observations, ∀ n, o.query = .primitive .verification n → tag n = 0 → o.answer = C n

/-- A syntactic all-reply byte bound, including rejecting continuations. -/
private def HashBounded {R : Type} : HashProgram R → Prop
  | .done _ => True
  | .hash bytes next => bytes.length < 2^56 ∧ ∀ d, HashBounded (next d)

private theorem bounded_bind {R S : Type} (p : HashProgram R) (next : R → HashProgram S)
    (before : HashBounded p) (after : ∀ r, HashBounded (next r)) :
    HashBounded (p.bind next) := by
  induction p with
  | done r => exact after r
  | hash bytes next ih => exact ⟨before.1,fun d => ih d (before.2 d)⟩

private theorem bounded_map {R S : Type} (p : HashProgram R) (f : R → S)
    (bound : HashBounded p) : HashBounded (p.map f) :=
  bounded_bind p _ bound (fun _ => trivial)

private theorem leafHashes_bounded (rowWords leafWords : Nat) (rows : List (List K))
    (fits : rowWords ≤ leafWords) (bound : 8 * leafWords < 2^56) :
    HashBounded (leafHashes rowWords leafWords rows) := by
  induction rows with
  | nil => trivial
  | cons row rows ih =>
    unfold leafHashes
    split
    · rename_i width
      refine ⟨?_,fun digest => bounded_map _ _ ih⟩
      rw [PrunedMerkleProgram.wordsBytes_length,
        leafImage_length 0 leafWords row (width ▸ fits)]
      omega
    · trivial

private theorem emit_bounded (i : Nat) (left right : Digest32) (tail : HashProgram LevelResult)
    (bound : HashBounded tail) : HashBounded (emit i left right tail) := by
  refine ⟨?_,fun _ => bounded_map _ _ bound⟩
  simp only [pairBytes,List.length_ofFn]
  decide

private theorem foldLevel_bounded (nodes : MerkleLevels.Level Digest32) (supplied : List Digest32) :
    HashBounded (foldLevel nodes supplied) := by
  induction nodes using (measure List.length).wf.induction generalizing supplied with
  | _ nodes ih =>
    cases nodes with
    | nil => simp [foldLevel,HashBounded]
    | cons x nodes =>
      rcases x with ⟨i,d⟩
      rw [foldLevel.eq_def]
      dsimp only
      split
      · cases nodes with
        | nil =>
          cases supplied with
          | nil => trivial
          | cons s ss => exact emit_bounded i d s _ (ih [] (by change 0<1; omega) ss)
        | cons y tail =>
          rcases y with ⟨j,e⟩
          dsimp only
          split
          · exact emit_bounded i d e _
              (ih tail (by change tail.length < tail.length+1+1; omega) supplied)
          · cases supplied with
            | nil => trivial
            | cons s ss =>
              exact emit_bounded i d s _
                (ih ((j,e)::tail) (by change tail.length+1 < tail.length+1+1; omega) ss)
      · cases supplied with
        | nil => trivial
        | cons s ss =>
          exact emit_bounded i s d _
            (ih nodes (by change nodes.length < nodes.length+1; omega) ss)

private theorem levels_bounded (n : Nat) (nodes : MerkleLevels.Level Digest32)
    (supplied : List Digest32) : HashBounded (levels n nodes supplied) := by
  induction n generalizing nodes supplied with
  | zero => trivial
  | succ n ih =>
    apply bounded_bind _ _ (foldLevel_bounded nodes supplied)
    intro result
    cases result with
    | none => trivial
    | some triple =>
      rcases triple with ⟨parents,known,rest⟩
      exact bounded_map _ _ (ih parents rest)

private theorem plan_bounded (proof : PrunedMerklePaths) (root : Digest32) (numLeaves : Nat)
    (queries : List Nat) (rowWords leafWords : Nat) (bound : 8 * leafWords < 2^56) :
    HashBounded (plan proof root numLeaves queries rowWords leafWords) := by
  unfold plan
  split
  · trivial
  · split
    · trivial
    · rename_i guards
      apply bounded_bind _ _ (leafHashes_bounded rowWords leafWords proof.leafData (by omega) bound)
      intro hashes
      cases hashes with
      | none => trivial
      | some hashes =>
        dsimp only
        by_cases range : ∃ q ∈ queries, numLeaves ≤ q
        · simp only [range,↓reduceIte]
          trivial
        · simp only [range,↓reduceIte]
          exact bounded_map _ _ (levels_bounded _ _ _)

private theorem lower_ordinary {R : Type} (program : HashProgram R) (bound : HashBounded program)
    (observations : List Observation) (result : R)
    (run : Runs program.lower observations result) :
    ∀ o ∈ observations, ∃ n, o.query = .primitive .verification n ∧ tag n = 0 := by
  induction program generalizing observations result with
  | done r => cases run; simp
  | hash bytes next ih =>
    obtain ⟨before,digest,after,equal,hashed,continued⟩ := (Runs.bind_iff _ _).mp run
    intro o member
    rw [equal] at member
    rcases List.mem_append.mp member with member | member
    · exact PCSBCSMixedOrdinaryMerkle.hash_trace_tag_zero hashed bound.1 o member
    · exact ih digest (bound.2 digest) after result continued o member

/-- Actual opener syntax emits only ordinary verification primitives. The
statement includes unsuccessful executions and does not evaluate challenges. -/
theorem openQuery_ordinary (p : ParameterBounds.Profile)
    (i : Fin (ParameterBounds.config p).folds.size) (lanes : Nat)
    (proof : PrunedMerklePaths) (root : Digest32) (sample : CausalProbability.Sample (.query i))
    (observations : List Observation) (result : Option Opened)
    (run : Runs (openQuery p i lanes proof root sample) observations result) :
    ∀ o ∈ observations, ∃ n, o.query = .primitive .verification n ∧ tag n = 0 := by
  obtain ⟨before,paths,after,equal,opened,finished⟩ := (Runs.bind_iff _ _).mp run
  cases finished
  simp only [List.append_nil] at equal
  subst observations
  exact lower_ordinary _ (plan_bounded proof root _ _ _ _ (production_leaf_byte_tag_zero p i)) _ _ opened

/-- Only the retained opener's primitive subtrace is transferred to the seed;
the caller and source challenge observations are left untouched. -/
theorem observed_real {p : ParameterBounds.Profile} {lanes : Nat} {proofs : Array PrunedMerklePaths}
    {observations : List Observation} {opening : QueryOpening p}
    (observed : ObservedOpening lanes proofs observations opening) (C : PrimitiveOracle) (iv : Digest32)
    (answers : PrimitiveConsistent C observations) :
    ∃ proof, proofs[opening.level.val]? = some proof ∧
      (runReal C iv (openQuery p opening.level lanes proof opening.root opening.sample)).view.result = some opening.result ∧
      ∀ o ∈ (runReal C iv (openQuery p opening.level lanes proof opening.root opening.sample)).view.observations,
        o ∈ observations := by
  obtain ⟨proof,trace,index,run,subset⟩ := observed
  have actual := run.real_result_trace C iv (by
    intro o member
    obtain ⟨n,query,ordinary⟩ := openQuery_ordinary p opening.level lanes proof opening.root opening.sample
      trace _ run o member
    rw [query]
    exact answers o (subset o member) n query ordinary)
  exact ⟨proof,index,actual.1,fun o member => subset o (actual.2 ▸ member)⟩

theorem observed_binding {p : ParameterBounds.Profile} {lanes : Nat}
    {proofs : Array PrunedMerklePaths} {observations : List Observation} {opening : QueryOpening p}
    (observed : ObservedOpening lanes proofs observations opening) (C : PrimitiveOracle) (iv : Digest32)
    (answers : PrimitiveConsistent C observations)
    (oldLog : PublicMerkleLog.PublicLog) (authentic : PublicMerkleLog.AuthenticLog C oldLog)
    (retained : Records)
    (history : ∀ e ∈ retained, ∃ earlier : PublicMerkleLog.PublicLog,
      (∀ q ∈ earlier, q ∈ oldLog) ∧ e ∈ PublicMerkleLog.records earlier)
    (saturated : ∀ bytes d, (bytes,d) ∈ PublicMerkleLog.records oldLog → ∃ first, (bytes,first) ∈ retained)
    (snapshot : Snapshot) (table : snapshot.table = recordDomain retained) :
    opening.result.rows = atQueries
      (frozenQueryOracle (PublicMerkleLog.hash C) snapshot opening.root p opening.level.val lanes)
      (queryIndices p opening.level opening.sample) ∨
      PublicMerkleBinding.OpenPrimitiveBad C oldLog opening.root opening.result.paths := by
  obtain ⟨proof,_,accepted,_⟩ := observed_real observed C iv answers
  exact openQuery_retained C iv oldLog authentic retained history saturated snapshot table
    p opening.level lanes proof opening.root opening.sample opening.result accepted

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

/-- Registry lookup and readiness concern the actual retained physical trace.
They are not semantic state paths or a PCS capture-identity certificate. -/
theorem execution_boundRows {ctx : RawWHIRKeys.Context} {stack : ctx.mode = .stack} {Q cap : Nat}
    (C : PrimitiveOracle) (iv : Digest32) (packet : RawWHIRKeys.Packet ctx Q)
    (record : AnchoredHeaderCodec.Record) (proofs : Array PrunedMerklePaths)
    (a : Accepted ctx Q cap packet record) (observations : List Observation)
    (answers : PrimitiveConsistent C observations)
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

/-- Literal native acceptance restores protocol verification and experiment
success on the very same tape, with arbitrary actual construction replies.
The base is the physical first-frozen capture, not an identified PCS capture. -/
theorem verifySource_experiment (cap : Nat) (boundary : Boundary)
    (model : WHIRCallerSupport.ProductionLayout) (ctx : RawWHIRKeys.Context)
    (stack : ctx.mode = .stack) (Q : Nat) (packet : RawWHIRKeys.Packet ctx Q)
    (record : AnchoredHeaderCodec.Record) (proofs : Array PrunedMerklePaths)
    (observations : List Observation) (a : Accepted ctx Q cap packet record)
    (run : Runs (erase (AnchoredPhysicalDriver.verifySource cap boundary model ctx stack Q packet record proofs))
      observations (some a))
    (C : PrimitiveOracle) (iv : Digest32)
    (answers : PrimitiveConsistent C observations)
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

/-- Preparation is derived from the exact executed native parser. Remaining
physical boundaries are `invariant`, `initial`, `registered`, and `quiet`;
identifying this physical first capture with PCS first capture is not assumed
or concluded. Neither protocol acceptance nor experiment success is a premise. -/
theorem verifySource_prepared_experiment (cap : Nat) (boundary : Boundary)
    (model : WHIRCallerSupport.ProductionLayout) (ctx : RawWHIRKeys.Context) (stack : ctx.mode = .stack)
    (Q : Nat) (packet : RawWHIRKeys.Packet ctx Q) (record : AnchoredHeaderCodec.Record)
    (proofs : Array PrunedMerklePaths) (observations : List Observation)
    (a : Accepted ctx Q cap packet record)
    (run : Runs (erase (AnchoredPhysicalDriver.verifySource cap boundary model ctx stack Q packet record proofs))
      observations (some a))
    (C : PrimitiveOracle) (iv : Digest32) (answers : PrimitiveConsistent C observations)
    (state : CausalBindingState.State cap) (invariant : WHIRPhysicalSnapshots.Invariant C state)
    (initial : ∃ snap, lookup record.root state.registry = some snap)
    (registered : CausalBindingState.Prepared state packet.val.profile ⟨packet.val.statement,packet.val.messages,[]⟩)
    (quiet : ∀ opening ∈ a.wire.openings, ∀ oldLog, state.frozenLog opening.root = some oldLog →
      ¬ PublicMerkleBinding.OpenPrimitiveBad C oldLog opening.root opening.result.paths) :
    ∃ prepared : OriginalClaimsChecker.Prepared (ParameterBounds.config packet.val.profile) record.shape.lanes
        a.request.claims.count a.request.claims.family a.request.claims.points record.point.toArray record.value,
      ∃ (replay : StackWHIRReplay.Replay packet.val.profile cap) (proof : Opening),
        OriginalClaimsChecker.prepare (ParameterBounds.config packet.val.profile) record.shape.lanes
          a.request.claims.family a.request.claims.points record.point.toArray record.value = some prepared ∧
        packet.val.messages.length = WHIRHistory.depth (ParameterBounds.config packet.val.profile) ∧
        replay.original = original a state ∧
        a.wire.initial = some replay.initial ∧ a.wire.tape.1 = replay.initial.2 ∧
        replay.whir.replies.map WHIRPhysicalErasure.eraseReply = a.wire.replies ∧
        CausalGame.opening (ParameterBounds.config packet.val.profile)
          (CausalGame.challenges (ParameterBounds.config packet.val.profile) a.wire.tape) replay.whir.replies = .ok proof ∧
        (let claims := (OriginalClaimsChecker.input prepared (original a state).root replay.initial.1).claims
         let claim := CausalGame.batchClaims (2^(ParameterBounds.config packet.val.profile).logN) claims a.wire.tape.1
         Protocol.verify (ParameterBounds.config packet.val.profile)
           (CausalGame.challenges (ParameterBounds.config packet.val.profile) a.wire.tape) record.shape.lanes
           (CausalGame.liftRoot (original a state).root) claim.weight claim.value proof = .ok ()) ∧
        CausalGame.experiment (OriginalClaimsChecker.input prepared (original a state).root replay.initial.1)
          (CausalStrategy.indexedStrategy replay.whir.replies) a.wire.tape = true := by
  obtain ⟨prepared,preparedEq,inputEq⟩ := AnchoredPhysicalPreparation.verifySource_preparation
    cap boundary model ctx stack Q packet record proofs observations a run
  obtain ⟨replay,proof,originalEq,seed,lambda,erased,parsed,verified,experiment⟩ :=
    verifySource_experiment cap boundary model ctx stack Q packet record
      proofs observations a run C iv answers state invariant initial registered quiet
  obtain ⟨_,_,_,trace,_⟩ := AnchoredPhysicalExecution.verifySource_execution cap boundary model ctx stack Q
    packet record proofs observations a run
  have complete := trace_completed record.root (completion_chain ctx Q packet) trace
  have claimsEq := congrArg CausalGame.Public.claims (inputEq state replay.initial.1)
  refine ⟨prepared,replay,proof,preparedEq,AnchoredPhysicalPreparation.accepted_completed_depth a complete,
    originalEq,seed,lambda,erased,parsed,?_,?_⟩
  · simpa only [claimsEq] using verified
  · have experimentEq := congrArg (fun claims =>
      CausalGame.experiment
        (CausalGame.Public.mk (ParameterBounds.config packet.val.profile) record.shape.lanes
          (original a state).root claims)
        (CausalStrategy.indexedStrategy replay.whir.replies) a.wire.tape) claimsEq
    exact experimentEq.trans experiment

#print axioms openQuery_ordinary
#print axioms observed_real
#print axioms observed_binding
#print axioms execution_boundRows
#print axioms verifySource_experiment
#print axioms verifySource_prepared_experiment

end Whir.AnchoredIdealPhysicalAcceptance
