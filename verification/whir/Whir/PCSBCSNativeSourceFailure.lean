import Whir.PCSBCSNativeCapturedReplyTransport
import Whir.PCSBCSNativeCapturedLogs
import Whir.PCSBCSAdaptiveSourceKnowledgeProbability

/-! Actual fresh native success outside the retained primitive bad events
produces the existing adaptive source failure witness whenever the literal
original decoder's extractor fails. No observer refinement or accepted path is
assumed. The physical bad-event probability inclusion is a separate obligation. -/
set_option autoImplicit false
namespace Whir.PCSBCSNativeSourceFailure
open Concrete Protocol FiatShamirGame DuplexModeGame TypedOracleCompiler
open MerkleTransport MerkleTransport.Commitments PublicMerkleLog
open WHIRPhysicalVerifier WHIRPhysicalReplay AnchoredPhysicalDriver
open PCSBCSSourceRootReferences PCSBCSCapturedSourceAcceptance PCSBCSCallerBinding

section Driver
variable (cap : Nat) (model : WHIRCallerSupport.ProductionLayout)
    (ctx : RawWHIRKeys.Context) (stack : ctx.mode = .stack) (Q : Nat)
    (packet : RawWHIRKeys.Packet ctx Q) (saved : AnchoredHeaderCodec.Record)
    (proofs : Array PrunedMerklePaths) (B : Nat)
    (limit : sourceBudget ctx Q packet ≤ B)
    (seed : DuplexPublicSimulator.Seed) (ro : RawKey B → Digest32)

noncomputable def extractionFailed : Prop :=
  ∃ original : CallerInput packet.val.profile,
    PCSBCSSourceCallerOriginal.original packet.val.profile model.layout saved
      (RawWHIRKeys.entry ctx packet.val)
      (PCSBCSSourceCallerAnswers.answers (PCSBCSCapturedIdealNativeAcceptance.table ctx Q packet B seed ro)) = some original ∧
    ¬ ∃ witness,
      PCSRoundByRoundKnowledge.extract packet.val.profile original.lanes original.family original.points
        original.anchorPoint original.anchorValue
        (PCSBCSNativeSourceOriginal.sourceBase cap model ctx stack Q packet saved proofs B limit seed ro) = some witness ∧
      PCSRewindSource.ExplainsOriginal (ParameterBounds.config packet.val.profile) original.lanes
        (PCSBCSNativeSourceOriginal.sourceBase cap model ctx stack Q packet saved proofs B limit seed ro)
        original.family original.points original.anchorPoint original.anchorValue witness

theorem mixed_success_failed
    (a : Accepted ctx Q cap packet saved) (familyCap : cap ≤ 2^64)
    (success : (AnchoredMixedIdealSourceAcceptance.mixedView cap .fresh model ctx stack Q packet saved proofs
      ctx.iv B limit seed ro).result.value = some a)
    (quiet : ∀ opening ∈ a.wire.openings,
      ¬ PublicMerkleBinding.OpenPrimitiveBad seed
        (PCSBCSNativeCapturedRows.openingLog cap model ctx stack Q packet saved proofs B limit seed ro opening)
        opening.root opening.result.paths)
    (clean : ¬ OutputCollision (PCSBCSNativeCapturedLogs.wholeLog
      cap model ctx stack Q packet saved proofs B limit seed ro))
    (failed : extractionFailed cap model ctx stack Q packet saved proofs B limit seed ro) :
    PCSBCSAdaptiveSourceKnowledgeProbability.Failed model.layout
      (PCSBCSCapturedIdealNativeAcceptance.allocationProgram cap model ctx stack Q packet saved proofs B limit)
      (PCSBCSCapturedIdealNativeAcceptance.table ctx Q packet B seed ro) := by
  have cleanRefs := PCSBCSNativeCapturedLogs.referenceLog_clean
    cap model ctx stack Q packet saved proofs B limit seed ro clean
  obtain ⟨original,claims,replay,proof,bounded,reconstructed,caller,bound,terminal,initial,lambda,
    erased,parsed,canonical,accepted,nativeEq,raws,transport,assembly⟩ :=
    PCSBCSNativeCapturedReplyTransport.mixed_success_replyTransport
      cap model ctx stack Q packet saved proofs B limit seed ro a familyCap success quiet cleanRefs
  obtain ⟨failedOriginal,failedDecoded,failedExtract⟩ := failed
  have same : failedOriginal = original := Option.some.inj (failedDecoded.symm.trans reconstructed)
  subst failedOriginal
  obtain ⟨_,bounded',_,_,_,_,recorded,_⟩ := PCSBCSNativeCapturedTape.mixed_success_tape
    cap model ctx stack Q packet saved proofs B limit seed ro a success
  let final := PCSBCSNativePacketBridge.enteredPacket ctx stack B
    (PCSBCSNativePacketVisit.packetAtBound ctx Q B packet bounded)
  let native : PCSBCSCapturedSourceProbability.FailureWitness model.layout saved
      (PCSBCSSourceCallerAnswers.answers (PCSBCSCapturedIdealNativeAcceptance.table ctx Q packet B seed ro))
      (PCSBCSCapturedIdealNativeAcceptance.allocationProgram cap model ctx stack Q packet saved proofs B limit)
      original (PCSBCSCapturedIdealNativeAcceptance.table ctx Q packet B seed ro) := {
    primitive := seed
    final := final
    claims := claims
    valid := a.configuration.1
    profile := a.configuration.2
    caller := caller
    bound := bound
    terminal := terminal
    recorded := recorded
    authentic := PCSBCSNativeCapturedLogs.referenceLog_authentic
      cap model ctx stack Q packet saved proofs B limit seed ro ⟨saved.root,initialShape saved.shape⟩
    clean := cleanRefs ⟨saved.root,initialShape saved.shape⟩
    ring := replay.initial.1
    tape := a.wire.tape
    strategy := fun _ => CausalStrategy.indexedStrategy replay.whir.replies
    raws := raws
    transport := transport
    accepted := accepted
    failed := failedExtract }
  exact ⟨⟨saved,original,native,reconstructed⟩⟩

end Driver
#print axioms mixed_success_failed
end Whir.PCSBCSNativeSourceFailure
