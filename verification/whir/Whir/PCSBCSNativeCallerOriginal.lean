import Whir.AnchoredPhysicalPreparation
import Whir.PCSBCSSourceCallerOriginal
import Whir.PCSBCSCallerCompletionCausality
import Whir.PCSBCSNativePacketBridge

/-! Exact original reconstruction for the fresh physical caller. Earlier
answers are obtained from the executed source, not a compatibility callback.
This module does not identify physical and atomic frozen Merkle captures. -/
namespace Whir.PCSBCSNativeCallerOriginal
open Concrete Protocol FiatShamirGame DuplexRefinement DuplexFraming DuplexModeGame
open WHIRCallerSupport WHIRSourceChronology WHIRPhysicalCaller AnchoredPhysicalDriver
open PCSBCSSourceCallerOriginal PCSBCSRestorationHazard PCSRoundByRoundTranscriptState
open PCSBCSCallerBinding
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000

 theorem real_observations {R : Type} (C : PrimitiveOracle) (iv : Digest32) (program : Program R) :
    ∀ o ∈ (runReal C iv program).view.observations, o.answer = realAnswer C iv o.query := by
  induction program with
  | done => simp [runReal]
  | ask query next ih =>
    intro o member
    rcases List.mem_cons.mp member with equal | member
    · subst o
      rfl
    · exact ih (realAnswer C iv query) o member

 theorem real_caller_prefix {R : Type} (C : PrimitiveOracle) (iv : Digest32)
    (program : Program R) (ctx : RawWHIRKeys.Context) (Q : Nat) (packet : RawWHIRKeys.Packet ctx Q)
    (before after : List Observation)
    (splitTrace : (runReal C iv program).view.observations = before ++ after)
    (queries : before.map Observation.query = (WHIRModeFinal.callerPositions ctx Q packet).map
      (fun q => Query.construction q.val (RawWHIRKeys.callerOutput_admissible ctx Q packet q.val q.property))) :
    ∀ wanted ∈ WHIRCallerOutputs.callerOutputs (RawWHIRKeys.entry ctx packet.val),
      latestAnswers before wanted = some (evalCoordinate (compressionOf C) iv wanted) := by
  intro wanted prior
  have queried : Query.construction wanted (RawWHIRKeys.callerOutput_admissible ctx Q packet wanted prior) ∈
      before.map Observation.query := by
    rw [queries]
    exact List.mem_map.mpr ⟨⟨wanted,prior⟩,List.mem_attach _ _,rfl⟩
  obtain ⟨o,member,equal⟩ := List.mem_map.mp queried
  apply latestAnswers_consistent before wanted
    (RawWHIRKeys.callerOutput_admissible ctx Q packet wanted prior) _ ⟨o,member,equal⟩
  intro observation member proof same
  have actual := real_observations C iv program observation (by
    rw [splitTrace]
    exact List.mem_append_left _ member)
  rw [same] at actual
  exact actual

 theorem request_original (cap : Nat) (p : ParameterBounds.Profile) (model : ProductionLayout)
    (saved : AnchoredHeaderCodec.Record) (configured : configuration p saved)
    (shape : saved.shape = AnchoredSourceCaller.shape model.layout)
    (entry : FramedHistory) (answers : Coordinate → Option Digest32)
    (request : CausalBindingState.ClaimRequest cap p)
    (familyCap : cap ≤ 2^64)
    (accepted : AnchoredPhysicalDriver.request .fresh cap p model.layout saved entry answers = some request) :
    ∃ input : CallerInput p,
      original p model.layout saved entry (fun q => (answers q).getD zeroDigest) = some input ∧
      input.m = request.claims.count ∧
      ∀ root seed, OriginalClaimsChecker.input input.prepared root seed =
        ⟨ParameterBounds.config p,saved.shape.lanes,root,
          AnchorPrefixRefinement.anchoredClaims (ParameterBounds.config p) saved
            request.claims.family request.claims.points seed⟩ := by
  have guards := AnchoredPhysicalPreparation.request_guards .fresh cap p model saved configured shape
    entry answers request accepted
  unfold AnchoredPhysicalDriver.request at accepted
  split at accepted
  next present =>
    cases decoded : AnchoredPhysicalDriver.decodeCaller .fresh model.layout saved entry
        (fun q => (answers q).getD zeroDigest) with
    | none => simp [decoded] at accepted
    | some claims =>
      simp only [decoded,bind,Option.bind] at accepted
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
              have familyBound : claims.caller.families.length ≤ 2^64 := families.trans familyCap
              change OriginalClaimsChecker.Guards (ParameterBounds.config p) saved.shape.lanes
                (indexedFamily claims) claims.caller.points saved.point.toArray at guards
              cases prepared : OriginalClaimsChecker.prepare (ParameterBounds.config p) saved.shape.lanes
                  (indexedFamily claims) claims.caller.points saved.point.toArray saved.value with
              | none =>
                simp only [OriginalClaimsChecker.prepare,dite_eq_left guards] at prepared
                cases prepared
              | some cached =>
                let input : CallerInput p := ⟨saved.shape.lanes,claims.caller.families.length,indexedFamily claims,
                  claims.caller.points,saved.point.toArray,saved.value,cached,familyBound,points⟩
                refine ⟨input,?_,rfl,?_⟩
                · have fresh : AnchoredSourceFreshCaller.decode model.layout saved entry
                      (fun q => (answers q).getD zeroDigest) = some claims := decoded
                  simp only [original,fresh]
                  dsimp only [Bind.bind,Option.bind]
                  rw [dite_eq_left familyBound,dite_eq_left points,prepared]
                  rfl
                · intro root seed
                  change CausalGame.Public.mk (ParameterBounds.config p) saved.shape.lanes root
                    (OriginalClaimsChecker.input cached root seed).claims = _
                  apply congrArg (CausalGame.Public.mk (ParameterBounds.config p) saved.shape.lanes root)
                  exact OriginalClaimsChecker.input_claims cached root seed
            next => contradiction
          next => contradiction
        next => contradiction
  next => contradiction

 theorem real_verifySource_original (cap : Nat) (model : ProductionLayout)
    (ctx : RawWHIRKeys.Context) (stack : ctx.mode = .stack) (Q : Nat)
    (packet : RawWHIRKeys.Packet ctx Q) (saved : AnchoredHeaderCodec.Record)
    (proofs : Array MerkleTransport.PrunedMerklePaths)
    (C : PrimitiveOracle) (iv : Digest32)
    (a : Accepted ctx Q cap packet saved) (familyCap : cap ≤ 2^64)
    (success : (runReal C iv (compile
      (AnchoredPhysicalDriver.verifySource cap .fresh model ctx stack Q packet saved proofs))).view.result.value = some a) :
    ∃ input : CallerInput packet.val.profile,
      original packet.val.profile model.layout saved (RawWHIRKeys.entry ctx packet.val)
        (evalCoordinate (compressionOf C) iv) = some input ∧
      input.m = a.request.claims.count ∧
      ∀ root seed, OriginalClaimsChecker.input input.prepared root seed =
        ⟨ParameterBounds.config packet.val.profile,saved.shape.lanes,root,
          AnchorPrefixRefinement.anchoredClaims (ParameterBounds.config packet.val.profile) saved
            a.request.claims.family a.request.claims.points seed⟩ := by
  let source := AnchoredPhysicalDriver.verifySource cap .fresh model ctx stack Q packet saved proofs
  have run := WHIRPhysicalCaller.real_source_runs C iv source
  change (runReal C iv (compile source)).view.result.value = some a at success
  rw [success] at run
  obtain ⟨caller,_,_,_,_⟩ := AnchoredPhysicalExecution.verifySource_execution
    cap .fresh model ctx stack Q packet saved proofs _ a run
  obtain ⟨before,after,splitTrace,_,queries,parsed⟩ := caller
  obtain ⟨_,shape,_,_,_,_,_,_,_,_⟩ := AnchoredPhysicalExecution.verifySource_success
    cap .fresh model ctx stack Q packet saved proofs _ a run
  have splitReal : (runReal C iv (compile source)).view.observations = before ++ after := by
    rw [← WHIRSourceChronology.real_source_trace]
    exact splitTrace
  have earlier := real_caller_prefix C iv (compile source) ctx Q packet before after splitReal queries
  obtain ⟨input,reconstructed,count,statement⟩ := request_original cap packet.val.profile model saved
    a.configuration shape (RawWHIRKeys.entry ctx packet.val) (latestAnswers before) a.request familyCap parsed
  refine ⟨input,?_,count,statement⟩
  rw [← reconstructed]
  apply original_prior_only
  intro q member
  rw [earlier q member]
  rfl

 theorem real_verifySource_constructed (cap : Nat) (model : ProductionLayout)
    (ctx : RawWHIRKeys.Context) (stack : ctx.mode = .stack) (Q : Nat)
    (packet : RawWHIRKeys.Packet ctx Q) (saved : AnchoredHeaderCodec.Record)
    (proofs : Array MerkleTransport.PrunedMerklePaths) (C : PrimitiveOracle) (iv : Digest32)
    (a : Accepted ctx Q cap packet saved) (familyCap : cap ≤ 2^64)
    {sourceQ boundary : Nat}
    (entered : PCSBCSChallengeOracle.EnteredPacket packet.val.profile sourceQ iv boundary)
    (entry : RawWHIRKeys.entry ctx packet.val = entered.1.val)
    (success : (runReal C iv (compile
      (AnchoredPhysicalDriver.verifySource cap .fresh model ctx stack Q packet saved proofs))).view.result.value = some a) :
    ∃ input : CallerInput packet.val.profile,
      original packet.val.profile model.layout saved entered.1.val
        (PCSBCSSourceCallerAnswers.answers
          (PCSBCSCallerCompletionCausality.realSourceTable (p := packet.val.profile)
            (Q := sourceQ) (iv := iv) (boundary := boundary) C)) = some input ∧
      input.m = a.request.claims.count ∧
      ∀ root seed, OriginalClaimsChecker.input input.prepared root seed =
        ⟨ParameterBounds.config packet.val.profile,saved.shape.lanes,root,
          AnchorPrefixRefinement.anchoredClaims (ParameterBounds.config packet.val.profile) saved
            a.request.claims.family a.request.claims.points seed⟩ := by
  obtain ⟨input,reconstructed,count,statement⟩ :=
    real_verifySource_original cap model ctx stack Q packet saved proofs C iv a familyCap success
  rw [entry] at reconstructed
  refine ⟨input,?_,count,statement⟩
  rw [← reconstructed]
  apply original_prior_only
  intro q member
  exact PCSBCSCallerCompletionCausality.realSource_answers C entered ⟨q,member⟩

 theorem real_verifySource_native_input (cap : Nat) (model : ProductionLayout)
    (ctx : RawWHIRKeys.Context) (stack : ctx.mode = .stack) (Q : Nat)
    (packet : RawWHIRKeys.Packet ctx Q) (saved : AnchoredHeaderCodec.Record)
    (proofs : Array MerkleTransport.PrunedMerklePaths) (C : PrimitiveOracle)
    (a : Accepted ctx Q cap packet saved) (familyCap : cap ≤ 2^64)
    (success : (runReal C ctx.iv (compile
      (AnchoredPhysicalDriver.verifySource cap .fresh model ctx stack Q packet saved proofs))).view.result.value = some a) :
    let entered := PCSBCSNativePacketBridge.enteredPacket ctx stack Q packet
    ∃ input : CallerInput packet.val.profile,
      original packet.val.profile model.layout saved entered.1.val
        (PCSBCSSourceCallerAnswers.answers
          (PCSBCSCallerCompletionCausality.realSourceTable (p := packet.val.profile)
            (Q := Q) (iv := ctx.iv) (boundary := entered.1.val.frames.length) C)) = some input ∧
      input.m = a.request.claims.count ∧
      ∀ root seed, OriginalClaimsChecker.input input.prepared root seed =
        ⟨ParameterBounds.config packet.val.profile,saved.shape.lanes,root,
          AnchorPrefixRefinement.anchoredClaims (ParameterBounds.config packet.val.profile) saved
            a.request.claims.family a.request.claims.points seed⟩ :=
  real_verifySource_constructed cap model ctx stack Q packet saved proofs C ctx.iv a familyCap
    (PCSBCSNativePacketBridge.enteredPacket ctx stack Q packet) rfl success

#print axioms real_caller_prefix
#print axioms request_original
#print axioms real_verifySource_original
#print axioms real_verifySource_constructed
#print axioms real_verifySource_native_input
end Whir.PCSBCSNativeCallerOriginal
