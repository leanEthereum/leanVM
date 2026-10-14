import Whir.AnchoredPhysicalKnowledgeAcceptance
import Whir.AnchoredPhysicalAcceptance

/-! Literal anchored native replay with an arbitrary rectangular root getter.
The getter can be the first shape-address capture rather than the later
physical digest registry. Only actual queried-row agreement and array shapes
are required; no whole later/earlier oracle identity is introduced.
This module does not discharge those sampled-row hypotheses or prove FS soundness.
-/
set_option autoImplicit false
namespace Whir.PCSBCSNativeOracleReplay
open Concrete Protocol FiatShamirGame DuplexModeGame
open MerkleTransport WHIRPhysicalVerifier WHIRPhysicalReplay WHIRPhysicalSoundness
open PublicMerkleProgram AnchoredPhysicalDriver WHIRSourceChronology

variable {ctx : RawWHIRKeys.Context} {stack : ctx.mode = .stack} {Q cap : Nat}
  {packet : RawWHIRKeys.Packet ctx Q} {saved : AnchoredHeaderCodec.Record}

def original (a : Accepted ctx Q cap packet saved) (base : CausalGame.BaseOracle) :
    WHIRFiatShamir.StackInitial packet.val.profile cap where
  lanes := a.request.lanes
  root := base
  lane_bound := a.request.lane_bound
  familyCount := a.request.claims.count
  family := a.request.claims.family
  family_bound := a.request.claims.family_bound
  points := a.request.claims.points
  claim_bound := a.request.claims.claim_bound

noncomputable def input (a : Accepted ctx Q cap packet saved) (base : CausalGame.BaseOracle)
    (seed : RingPCSGame.Prefix) : CausalGame.Public where
  config := ParameterBounds.config packet.val.profile
  lanes := saved.shape.lanes
  root := base
  claims := AnchorPrefixRefinement.anchoredClaims (ParameterBounds.config packet.val.profile) saved
    a.request.claims.family a.request.claims.points seed

theorem decodeStack_rootShapes (p : ParameterBounds.Profile) (familyCap : Nat)
    (catalog : StackWHIRReplay.Catalog p familyCap) (roots : WHIRReplay.Roots)
    (rows : WHIRPhysicalHistory.Rows) (key : StackWHIRReplay.Key p)
    (out : StackWHIRReplay.Replay p familyCap)
    (parsed : WHIRPhysicalHistory.decodeStack p familyCap catalog roots rows key = some out)
    (rectangular : ∀ digest level, oracleValid (roots digest level)
      (ParameterBounds.length (ParameterBounds.config p) level)
      (2^(ParameterBounds.config p).folds[level]!) = true)
    (tape : CausalGame.Tape (ParameterBounds.config p)) (proof : Opening)
    (accepted : CausalGame.opening (ParameterBounds.config p)
      (CausalGame.challenges (ParameterBounds.config p) tape) out.whir.replies = .ok proof) :
    WHIRNativeArithmetic.RootShapes (ParameterBounds.config p) proof := by
  intro i bound hasNext next found
  obtain ⟨digest,_,value⟩ := decodeStack_opening_nextOracle p familyCap catalog roots rows key
    out parsed tape proof accepted ⟨i,bound⟩ hasNext
  have equal := Option.some.inj (found.symm.trans value)
  subst next
  have shape := rectangular digest (i+1)
  have dimensions := ((CausalBoundary.production_boundary_facts p ⟨i,bound⟩).2.2 hasNext).1
  change CausalGame.remaining (ParameterBounds.config p) (i+1) +
    (ParameterBounds.config p).folds[i+1]! = CausalGame.remaining (ParameterBounds.config p) i at dimensions
  have remaining : CausalGame.remaining (ParameterBounds.config p) (i+1) =
      CausalGame.remaining (ParameterBounds.config p) i - (ParameterBounds.config p).folds[i+1]! := by omega
  simpa only [ParameterBounds.length,remaining] using shape

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

theorem verifySource_experiment (boundary : AnchoredPhysicalDriver.Boundary)
    (model : WHIRCallerSupport.ProductionLayout) (proofs : Array PrunedMerklePaths)
    (observations : List Observation) (a : Accepted ctx Q cap packet saved)
    (run : Runs (erase (AnchoredPhysicalDriver.verifySource cap boundary model ctx stack Q packet saved proofs))
      observations (some a))
    (base : CausalGame.BaseOracle) (roots : WHIRReplay.Roots)
    (baseShape : oracleValid (CausalGame.liftRoot base)
      (2^((ParameterBounds.config packet.val.profile).logN-(ParameterBounds.config packet.val.profile).folds[0]!+
        (ParameterBounds.config packet.val.profile).rates[0]!)) saved.shape.lanes = true)
    (rectangular : ∀ digest level, oracleValid (roots digest level)
      (ParameterBounds.length (ParameterBounds.config packet.val.profile) level)
      (2^(ParameterBounds.config packet.val.profile).folds[level]!) = true)
    (boundRows : WHIRPhysicalRoots.BoundRows base roots a.wire) :
    ∃ replay : StackWHIRReplay.Replay packet.val.profile cap, ∃ proof,
      replay.original = original a base ∧
      a.wire.initial = some replay.initial ∧ a.wire.tape.1 = replay.initial.2 ∧
      replay.whir.replies.map WHIRPhysicalErasure.eraseReply = a.wire.replies ∧
      CausalGame.opening (ParameterBounds.config packet.val.profile)
        (CausalGame.challenges (ParameterBounds.config packet.val.profile) a.wire.tape)
        replay.whir.replies = .ok proof ∧
      WHIRPhysicalHistory.decodeStack packet.val.profile cap (fun _ => some (original a base)) roots
        (fun i => a.wire.rows[i]!)
        ⟨packet.val.statement,packet.val.messages,(localHistory ctx stack Q packet.val.profile a.history).tail⟩ =
        some replay ∧
      CausalGame.experiment (input a base replay.initial.1)
        (CausalStrategy.indexedStrategy replay.whir.replies) a.wire.tape = true := by
  obtain ⟨_,rootEq,lanesEq,trace,_⟩ := AnchoredPhysicalExecution.verifySource_execution
    cap boundary model ctx stack Q packet saved proofs observations a run
  have trace' : Trace ctx stack Q packet.val.profile a.request.lanes proofs
      (RawOracleCoupling.Concrete.completion ctx Q packet)
      (initialWireState packet.val.profile a.request.root) a.wire a.history := by
    simpa only [rootEq,lanesEq] using trace
  let catalog : StackWHIRReplay.Catalog packet.val.profile cap := fun _ => some (original a base)
  have found : catalog packet.val.statement = some (original a base) := rfl
  have chain := WHIRPhysicalReplay.completion_chain ctx Q packet
  have complete := trace_completed a.request.root chain trace'
  obtain ⟨_,past,sample,erased,history,decoded,originalEq,initialSeed,_,tape,replies⟩ :=
    Completed.decodeStack packet a.wire a.history catalog (original a base) found complete
      (AnchoredPhysicalKnowledgeAcceptance.replies_nonempty a)
  have tail : (localHistory ctx stack Q packet.val.profile a.history).tail = past := by rw [history]; rfl
  have full := decoded
  change WHIRPhysicalHistory.decodeStack packet.val.profile cap catalog WHIRPhysicalErasure.zeroRoots
    (fun i => a.wire.rows[i]!) ⟨packet.val.statement,packet.val.messages,past⟩ = some erased at full
  rw [WHIRPhysicalErasure.decodeStack_zero packet.val.profile cap catalog roots
    (fun i => a.wire.rows[i]!) ⟨packet.val.statement,packet.val.messages,past⟩] at full
  obtain ⟨replay,physical,erasedEq⟩ := Option.map_eq_some_iff.mp full
  subst erased
  change replay.original = original a base at originalEq
  change a.wire.initial = some replay.initial at initialSeed
  change (StackWHIRReplay.finish ⟨packet.val.statement,packet.val.messages,past⟩ replay sample).whir.tape = a.wire.tape at tape
  change replay.whir.replies.map WHIRPhysicalErasure.eraseReply = a.wire.replies at replies
  have agreement := WHIRPhysicalRoots.trace_stackRowsAgree packet a.request.root catalog (original a base)
    roots found chain trace' boundRows
  rw [tail] at agreement
  have ideal := WHIRPhysicalHistory.decodeStack_success packet.val.profile cap catalog roots
    (fun i => a.wire.rows[i]!) ⟨packet.val.statement,packet.val.messages,past⟩ replay agreement physical
  have lambda := StackWHIRReplay.decode_initial_lambda catalog roots
    ⟨packet.val.statement,packet.val.messages,past⟩ replay ideal sample
  rw [tape] at lambda
  change a.wire.tape.1 = replay.initial.2 at lambda
  obtain ⟨seed,nativeProof,seedFound,parsed,native⟩ := a.acceptance
  have sameSeed : seed = replay.initial := Option.some.inj (seedFound.symm.trans initialSeed)
  subst seed
  rw [← replies] at parsed
  obtain ⟨proof,parsedFull,erasedProof⟩ := opening_unerase _ _ replay.whir.replies nativeProof parsed
  have nativeFull : AnchoredPhysicalAnchor.sourceVerify saved a.request.claims.family a.request.claims.points
      replay.initial.1 replay.initial.2 (ParameterBounds.config packet.val.profile)
      (CausalGame.challenges (ParameterBounds.config packet.val.profile) a.wire.tape) proof = .ok () := by
    rw [← AnchoredPhysicalKnowledgeAcceptance.sourceVerify_erased,erasedProof]
    exact native
  have rootsShape := decodeStack_rootShapes packet.val.profile cap catalog roots
    (fun i => a.wire.rows[i]!) ⟨packet.val.statement,packet.val.messages,past⟩ replay physical rectangular
    a.wire.tape proof parsedFull
  have authenticated := trace_authenticatedRows packet a.request.root base roots chain trace' boundRows
    catalog replay (by rw [tail]; exact physical) proof parsedFull
  have nativeShapes := AnchoredPhysicalDriver.accepted_nativeShapes a
  have shapes := AnchoredPhysicalAcceptance.accepted_anchored_shapes a replay.initial.1 replay.initial.2
  have verified := AnchorPrefixRefinement.sourceVerify_refines saved a.request.claims.family a.request.claims.points
    replay.initial.1 replay.initial.2 (ParameterBounds.config packet.val.profile) _ proof
    (CausalGame.liftRoot base) a.configuration.1 a.configuration.2.1 a.configuration.2.2.1
    nativeShapes.1 (fun i => nativeShapes.2 _ (by simp)) shapes.2 baseShape rootsShape authenticated nativeFull
  refine ⟨replay,proof,originalEq,initialSeed,lambda,replies,parsedFull,
    (by simpa only [catalog,← tail] using physical),?_⟩
  apply WHIRPhysicalSoundness.experiment_indexed_accepts (input a base replay.initial.1)
    a.wire.tape replay.whir.replies proof parsedFull
  · exact shapes.1
  · change Protocol.verify (ParameterBounds.config packet.val.profile)
      (CausalGame.challenges (ParameterBounds.config packet.val.profile) a.wire.tape) saved.shape.lanes
      (CausalGame.liftRoot base)
      (CausalGame.batchClaims (2^(ParameterBounds.config packet.val.profile).logN)
        (input a base replay.initial.1).claims a.wire.tape.1).weight
      (CausalGame.batchClaims (2^(ParameterBounds.config packet.val.profile).logN)
        (input a base replay.initial.1).claims a.wire.tape.1).value proof = .ok ()
    rw [lambda]
    exact verified

#print axioms decodeStack_rootShapes
#print axioms verifySource_experiment
end Whir.PCSBCSNativeOracleReplay
