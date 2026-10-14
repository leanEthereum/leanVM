import Whir.PCSBCSNativeCapturedOracles
import Whir.PCSBCSNativeIdealCallerOriginal

/-! Exact first-address Root0 and independently decoded original caller.
The accepted causal experiment is derived from the native source run with
captured getters; it does not assert current Rust or #607 correspondence. -/
set_option autoImplicit false
namespace Whir.PCSBCSNativeSourceOriginal
open Concrete Protocol FiatShamirGame DuplexModeGame TypedOracleCompiler
open MerkleTransport MerkleTransport.Commitments PublicMerkleLog
open WHIRPhysicalVerifier WHIRPhysicalReplay AnchoredPhysicalDriver
open PCSBCSSourceRootReferences PCSBCSCapturedSourceAcceptance PCSBCSCallerBinding

theorem nativeReplies_indexed {p : ParameterBounds.Profile}
    (original : CallerInput p) (root : CausalGame.BaseOracle) (ring : RingPCSGame.Prefix)
    (tape : CausalGame.Tape (ParameterBounds.config p)) (replies : Array CausalGame.Reply) (proof : Opening)
    (parsed : CausalGame.opening (ParameterBounds.config p)
      (CausalGame.challenges (ParameterBounds.config p) tape) replies = .ok proof) :
    nativeReplies original root (fun _ => CausalStrategy.indexedStrategy replies) ring tape = replies := by
  have equal := WHIRPhysicalSoundness.run_indexed_replies
    (ExecutionShapes.Input p original.lanes root (OriginalClaimsChecker.input original.prepared root ring).claims)
    tape replies proof parsed
  simpa only [nativeReplies,PCSRoundByRoundTranscriptState.replies,Array.toArray_toList] using
    congrArg List.toArray equal

section Driver
variable (cap : Nat) (model : WHIRCallerSupport.ProductionLayout)
    (ctx : RawWHIRKeys.Context) (stack : ctx.mode = .stack) (Q : Nat)
    (packet : RawWHIRKeys.Packet ctx Q) (saved : AnchoredHeaderCodec.Record)
    (proofs : Array PrunedMerklePaths) (B : Nat)
    (limit : sourceBudget ctx Q packet ≤ B)
    (seed : DuplexPublicSimulator.Seed) (ro : RawKey B → Digest32)

noncomputable abbrev addresses :=
  PCSBCSCapturedSourceTransport.address (p := packet.val.profile) (Q := B) (iv := ctx.iv)
    (boundary := (RawWHIRKeys.entry ctx packet.val).frames.length)

noncomputable abbrev sourceBase :=
  sourceRoot seed (addresses ctx Q packet B) ⟨saved.root,initialShape saved.shape⟩
    (PCSBCSCapturedIdealNativeAcceptance.allocationProgram cap model ctx stack Q packet saved proofs B limit)
    (PCSBCSCapturedIdealNativeAcceptance.table ctx Q packet B seed ro)

theorem base_eq_sourceRoot (profile : profileShape packet.val.profile saved.shape) :
    PCSBCSNativeCapturedOracles.base cap model ctx stack Q packet saved proofs B limit seed ro =
      sourceBase cap model ctx stack Q packet saved proofs B limit seed ro := by
  have shape := PCSBCSNativeRootRoles.nativeShape_opening packet.val.profile saved profile 0
  have length : 2^((ParameterBounds.length (ParameterBounds.config packet.val.profile) 0).log2) =
      ParameterBounds.length (ParameterBounds.config packet.val.profile) 0 := by
    simp [ParameterBounds.length]
  unfold PCSBCSNativeCapturedOracles.base sourceBase sourceRoot
  have ref : (⟨saved.root,PCSBCSNativeRootRoles.nativeShape packet.val.profile saved 0⟩ : Reference) =
      ⟨saved.root,initialShape saved.shape⟩ := rfl
  change WHIRPhysicalRows.compactBaseOracle (hash seed)
    ⟨recordDomain (records (PCSBCSNativeCapturedRows.referenceLog cap model ctx stack Q packet saved proofs B limit seed ro
      ⟨saved.root,PCSBCSNativeRootRoles.nativeShape packet.val.profile saved 0⟩)),[]⟩ saved.root
      (ParameterBounds.length (ParameterBounds.config packet.val.profile) 0).log2
      (ParameterBounds.length (ParameterBounds.config packet.val.profile) 0)
      (leafWords packet.val.profile 0) saved.shape.lanes = _
  rw [ref]
  have shape' : initialShape saved.shape =
      ⟨(ParameterBounds.length (ParameterBounds.config packet.val.profile) 0).log2,
        leafWords packet.val.profile 0,saved.shape.lanes⟩ := by
    simpa only [PCSBCSNativeRootRoles.nativeShape,ite_true] using shape
  simp only [shape',PCSBCSNativeCapturedRows.referenceLog,length]

theorem original_bound (input : CallerInput packet.val.profile)
    (reconstructed : PCSBCSSourceCallerOriginal.original packet.val.profile model.layout saved
      (RawWHIRKeys.entry ctx packet.val)
      (PCSBCSSourceCallerAnswers.answers (PCSBCSCapturedIdealNativeAcceptance.table ctx Q packet B seed ro)) = some input) :
    ∃ claims : AnchoredSourceCaller.Claims,
      AnchoredSourceFreshCaller.decode model.layout saved (RawWHIRKeys.entry ctx packet.val)
        (PCSBCSSourceCallerAnswers.answers (PCSBCSCapturedIdealNativeAcceptance.table ctx Q packet B seed ro)) = some claims ∧
      BoundOriginal input saved claims := by
  obtain ⟨claims,fc,cc,prepared,decoded,recordEq,rootEq,_,rfl⟩ :=
    PCSBCSSourceCallerOriginal.original_exact packet.val.profile model.layout saved
      (RawWHIRKeys.entry ctx packet.val)
      (PCSBCSSourceCallerAnswers.answers (PCSBCSCapturedIdealNativeAcceptance.table ctx Q packet B seed ro)) input reconstructed
  refine ⟨claims,decoded,recordEq,rootEq,rfl,?_,rfl,rfl,rfl⟩
  exact List.ofFn_getElem

theorem mixed_success_original_experiment
    (a : Accepted ctx Q cap packet saved) (familyCap : cap ≤ 2^64)
    (success : (AnchoredMixedIdealSourceAcceptance.mixedView cap .fresh model ctx stack Q packet saved proofs
      ctx.iv B limit seed ro).result.value = some a)
    (quiet : ∀ opening ∈ a.wire.openings,
      ¬ PublicMerkleBinding.OpenPrimitiveBad seed
        (PCSBCSNativeCapturedRows.openingLog cap model ctx stack Q packet saved proofs B limit seed ro opening)
        opening.root opening.result.paths) :
    ∃ (input : CallerInput packet.val.profile) (claims : AnchoredSourceCaller.Claims)
      (replay : StackWHIRReplay.Replay packet.val.profile cap) (proof : Opening),
      PCSBCSSourceCallerOriginal.original packet.val.profile model.layout saved
        (RawWHIRKeys.entry ctx packet.val)
        (PCSBCSSourceCallerAnswers.answers (PCSBCSCapturedIdealNativeAcceptance.table ctx Q packet B seed ro)) = some input ∧
      AnchoredSourceFreshCaller.decode model.layout saved (RawWHIRKeys.entry ctx packet.val)
        (PCSBCSSourceCallerAnswers.answers (PCSBCSCapturedIdealNativeAcceptance.table ctx Q packet B seed ro)) = some claims ∧
      BoundOriginal input saved claims ∧
      a.wire.initial = some replay.initial ∧ a.wire.tape.1 = replay.initial.2 ∧
      replay.whir.replies.map WHIRPhysicalErasure.eraseReply = a.wire.replies ∧
      CausalGame.opening (ParameterBounds.config packet.val.profile)
        (CausalGame.challenges (ParameterBounds.config packet.val.profile) a.wire.tape)
        replay.whir.replies = .ok proof ∧
      WHIRPhysicalHistory.decodeStack packet.val.profile cap
        (fun _ => some (PCSBCSNativeOracleReplay.original a
          (PCSBCSNativeCapturedOracles.base cap model ctx stack Q packet saved proofs B limit seed ro)))
        (PCSBCSNativeCapturedOracles.roots cap model ctx stack Q packet saved proofs B limit seed ro)
        (fun i => a.wire.rows[i]!)
        ⟨packet.val.statement,packet.val.messages,(localHistory ctx stack Q packet.val.profile a.history).tail⟩ =
        some replay ∧
      CausalGame.experiment
        (OriginalClaimsChecker.input input.prepared
          (sourceBase cap model ctx stack Q packet saved proofs B limit seed ro) replay.initial.1)
        (CausalStrategy.indexedStrategy replay.whir.replies) a.wire.tape = true := by
  obtain ⟨input,reconstructed,_,statement⟩ := PCSBCSNativeIdealCallerOriginal.fresh_original
    cap model ctx stack Q packet saved proofs B limit seed ro a familyCap success
  obtain ⟨claims,decoded,bound⟩ := original_bound model ctx Q packet saved B seed ro input reconstructed
  obtain ⟨replay,proof,_,initial,tape,replies,opening,canonical,accepted⟩ :=
    PCSBCSNativeCapturedOracles.mixed_success_experiment
      cap model ctx stack Q packet saved proofs B limit seed ro a familyCap success quiet
  have same := statement
    (PCSBCSNativeCapturedOracles.base cap model ctx stack Q packet saved proofs B limit seed ro) replay.initial.1
  change OriginalClaimsChecker.input input.prepared
    (PCSBCSNativeCapturedOracles.base cap model ctx stack Q packet saved proofs B limit seed ro) replay.initial.1 =
      PCSBCSNativeOracleReplay.input a
        (PCSBCSNativeCapturedOracles.base cap model ctx stack Q packet saved proofs B limit seed ro) replay.initial.1 at same
  have lanesEq : input.lanes = saved.shape.lanes := congrArg CausalGame.Public.lanes same
  have claimsEq := congrArg CausalGame.Public.claims same
  change (OriginalClaimsChecker.input input.prepared
    (PCSBCSNativeCapturedOracles.base cap model ctx stack Q packet saved proofs B limit seed ro) replay.initial.1).claims =
      AnchorPrefixRefinement.anchoredClaims (ParameterBounds.config packet.val.profile) saved
        a.request.claims.family a.request.claims.points replay.initial.1 at claimsEq
  have acceptedOriginal : CausalGame.experiment
      (OriginalClaimsChecker.input input.prepared
        (PCSBCSNativeCapturedOracles.base cap model ctx stack Q packet saved proofs B limit seed ro) replay.initial.1)
      (CausalStrategy.indexedStrategy replay.whir.replies) a.wire.tape = true := by
    change CausalGame.experiment
      ⟨ParameterBounds.config packet.val.profile,input.lanes,
        PCSBCSNativeCapturedOracles.base cap model ctx stack Q packet saved proofs B limit seed ro,
        (OriginalClaimsChecker.input input.prepared
          (PCSBCSNativeCapturedOracles.base cap model ctx stack Q packet saved proofs B limit seed ro) replay.initial.1).claims⟩
      (CausalStrategy.indexedStrategy replay.whir.replies) a.wire.tape = true
    rw [claimsEq,lanesEq]
    exact accepted
  rw [base_eq_sourceRoot cap model ctx stack Q packet saved proofs B limit seed ro a.configuration.2] at acceptedOriginal
  exact ⟨input,claims,replay,proof,reconstructed,decoded,bound,initial,tape,replies,opening,canonical,acceptedOriginal⟩

end Driver
#print axioms base_eq_sourceRoot
#print axioms original_bound
#print axioms mixed_success_original_experiment
#print axioms nativeReplies_indexed
end Whir.PCSBCSNativeSourceOriginal
