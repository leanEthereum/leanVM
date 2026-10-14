import Whir.PCSBCSNativeIdealCallerOriginal
import Whir.PCSBCSNativePacketCodec
import Whir.PCSBCSMerkleSeedProjection
import Whir.PCSBCSCapturedSourceAcceptance
import Whir.PCSBCSObservedPrimitiveExtension

/-! Historical pre-#607 native/captured join. The checked endpoint below transports
only the rows actually queried by an accepted native opening. It deliberately
retains the existing OpenPrimitiveBad alternative: first raw prequeries may
capture a root before its announcement, and later log growth is not a whole-table
identity. This is an intermediate, not ObserverRefines or an FS security theorem.

Endpoint hypotheses are: stack mode; aggregate source budget; actual mixed driver
success; caller family cap; membership of the selected opening in that result;
actual visit of an entered source packet in the raw allocation compiler; and
membership of the selected shape address in that packet's literal parsed roles.
No accepted original, compatible snapshot, capture/oracle equality, accepted
interactive experiment, source soundness, or observer refinement is assumed.
The final two hypotheses retain the source chronology/address join explicitly.
The conclusion uses the native frozenQueryOracle of the actual capture prefix;
it does not yet prove selectPhase equality or ReplyTransport for the native
same-tape interactive replies. Those require the scheduled phase-reference and
query-codec crosswalk, and transport of each nonterminal next-root reply without
equating a later physical registry with the earlier captured full oracle.
No FrozenExtractionBad probability charge or enclosing-adversary refinement is
derived here; the OpenPrimitiveBad alternative is left intact for that join.
-/
set_option autoImplicit false
namespace Whir.PCSBCSCapturedIdealNativeAcceptance
open Concrete Protocol FiatShamirGame DuplexFraming DuplexModeGame TypedOracleCompiler
open RawOracleCoupling PCSBCSChallengeOracle WHIRSourceChronology AnchoredPhysicalDriver
open PCSBCSSourceRootReferences PCSBCSMerkleRootCache PCSBCSCapturedNativeReplyBridge
open PCSBCSCapturedSourceAcceptance PublicMerkleLog MerkleTransport
open MerkleTransport.Commitments

section Driver
variable (cap : Nat) (model : WHIRCallerSupport.ProductionLayout)
    (ctx : RawWHIRKeys.Context) (stack : ctx.mode = .stack) (Q : Nat)
    (packet : RawWHIRKeys.Packet ctx Q) (saved : AnchoredHeaderCodec.Record)
    (proofs : Array PrunedMerklePaths) (B : Nat)
    (limit : WHIRPhysicalVerifier.sourceBudget ctx Q packet ≤ B)

private noncomputable abbrev part := EnteredPacket.partition (p := packet.val.profile) (Q := B)
  (iv := ctx.iv) (boundary := (RawWHIRKeys.entry ctx packet.val).frames.length)

/-- The literal grouped raw compiler, without a fabricated allocation trace. -/
noncomputable def allocationProgram :=
  Atomic.program (part ctx Q packet B)
    (PublicCompressionCouplingMixed.compile B ctx.iv []
      (WHIRSourceChronology.compile
        (AnchoredPhysicalDriver.verifySource cap .fresh model ctx stack Q packet saved proofs))
      (WHIRPhysicalVerifier.sourceBudget ctx Q packet) limit
      ((WHIRSourceChronology.compile_counted _ _).mpr
        (AnchoredPhysicalDriver.verifySource_counted cap .fresh model ctx stack Q packet saved proofs)))

noncomputable def table (seed : DuplexPublicSimulator.Seed) (ro : RawKey B → Digest32) :=
  (part ctx Q packet B).split (PublicCompressionCouplingMixed.oracle seed ro)

private abbrev view (seed : DuplexPublicSimulator.Seed) (ro : RawKey B → Digest32) :=
  AnchoredMixedIdealSourceAcceptance.mixedView cap .fresh model ctx stack Q packet saved proofs
    ctx.iv B limit seed ro

/-- The allocation compiler's result is the actual mixed driver view, not a
supplied tuple-copy equation. Its trace remains the actual grouped query trace. -/
theorem allocation_result (seed : DuplexPublicSimulator.Seed) (ro : RawKey B → Digest32) :
    Sampling.eval (table ctx Q packet B seed ro)
      (allocationProgram cap model ctx stack Q packet saved proofs B limit) =
      view cap model ctx stack Q packet saved proofs B limit seed ro := by
  unfold allocationProgram
  rw [Atomic.eval_program]
  simp only [table,Partition.join_split]
  rfl

/-- Actual complete primitive replay, including nonordinary simulator answers.
Its extension is not a uniform primitive and is not the independent source RO. -/
theorem observed_snapshot (seed : DuplexPublicSimulator.Seed) (ro : RawKey B → Digest32) :
    WHIRPhysicalSnapshots.Invariant
      (PCSBCSObservedPrimitiveExtension.extension seed
        (DuplexPublicSimulator.finalLog []
          (view cap model ctx stack Q packet saved proofs B limit seed ro).observations))
      (WHIRSourceObserver.replayTracked (CausalBindingState.empty cap)
        (view cap model ctx stack Q packet saved proofs B limit seed ro).result.events) := by
  simpa only [view,AnchoredMixedIdealSourceAcceptance.mixedView,
    PublicCompressionCouplingMixed.compile_actual,DuplexPublicSimulator.simulator] using
    PCSBCSObservedPrimitiveExtension.ideal_snapshot seed ro ctx.iv
      (AnchoredPhysicalDriver.verifySource cap .fresh model ctx stack Q packet saved proofs)
      (WHIRPhysicalVerifier.sourceBudget ctx Q packet) limit
      (AnchoredPhysicalDriver.verifySource_counted cap .fresh model ctx stack Q packet saved proofs)

/-- The source address for exactly this native opening's geometry. -/
def openingReference (opening : WHIRPhysicalVerifier.QueryOpening packet.val.profile)
    (lanes : Nat) : Reference :=
  ⟨opening.root,⟨(ParameterBounds.length (ParameterBounds.config packet.val.profile) opening.level.val).log2,
    WHIRPhysicalVerifier.leafWords packet.val.profile opening.level.val,
    if opening.level.val = 0 then lanes else WHIRPhysicalVerifier.leafWords packet.val.profile opening.level.val⟩⟩

/-- Strongest checked local join: exact caller original, actual raw-prefix
capture, and actual native queried rows (all phases, repetitions preserved), or
the existing captured-prefix bad event. No later physical registry is identified
with the earlier captured table. -/
theorem mixed_success_captured_rows
    (seed : DuplexPublicSimulator.Seed) (ro : RawKey B → Digest32)
    (a : Accepted ctx Q cap packet saved) (familyCap : cap ≤ 2^64)
    (success : (view cap model ctx stack Q packet saved proofs B limit seed ro).result.value = some a)
    (opening : WHIRPhysicalVerifier.QueryOpening packet.val.profile)
    (member : opening ∈ a.wire.openings)
    (current : EnteredPacket packet.val.profile B ctx.iv
      (RawWHIRKeys.entry ctx packet.val).frames.length)
    (visited : (.inl current : (part ctx Q packet B).Key) ∈
      ((Sampling.execute (table ctx Q packet B seed ro)
        (allocationProgram cap model ctx stack Q packet saved proofs B limit)).2.map Sigma.fst))
    (mentioned : openingReference ctx Q packet opening saved.shape.lanes ∈
      PCSBCSCapturedSourceTransport.address (.inl current)) :
    ∃ input : PCSBCSCallerBinding.CallerInput packet.val.profile,
      PCSBCSSourceCallerOriginal.original packet.val.profile model.layout saved
        (RawWHIRKeys.entry ctx packet.val)
        (PCSBCSSourceCallerAnswers.answers (table ctx Q packet B seed ro)) = some input ∧
      input.m = a.request.claims.count ∧
      (∀ root ring, OriginalClaimsChecker.input input.prepared root ring =
        ⟨ParameterBounds.config packet.val.profile,saved.shape.lanes,root,
          AnchorPrefixRefinement.anchoredClaims (ParameterBounds.config packet.val.profile) saved
            a.request.claims.family a.request.claims.points ring⟩) ∧
      ∃ f : Frozen,
        PCSBCSSourceRootCapture.capture
          PCSBCSCapturedSourceTransport.address
          (openingReference ctx Q packet opening saved.shape.lanes)
          (allocationProgram cap model ctx stack Q packet saved proofs B limit)
          (table ctx Q packet B seed ro) = some f ∧
        AuthenticLog seed f.queryPrefix ∧
        (¬ OutputCollision f.queryPrefix → f.raw = sourceRoot seed
          PCSBCSCapturedSourceTransport.address
          (openingReference ctx Q packet opening saved.shape.lanes)
          (allocationProgram cap model ctx stack Q packet saved proofs B limit)
          (table ctx Q packet B seed ro)) ∧
        (opening.result.rows = WHIRPhysicalVerifier.atQueries
          (WHIRPhysicalVerifier.frozenQueryOracle (hash seed)
            ⟨recordDomain (records f.queryPrefix),[]⟩ opening.root packet.val.profile
            opening.level.val saved.shape.lanes)
          (WHIRPhysicalVerifier.queryIndices packet.val.profile opening.level opening.sample) ∨
          PublicMerkleBinding.OpenPrimitiveBad seed f.queryPrefix opening.root opening.result.paths) := by
  obtain ⟨input,original,count,statement⟩ := PCSBCSNativeIdealCallerOriginal.fresh_original
    cap model ctx stack Q packet saved proofs B limit seed ro a familyCap success
  refine ⟨input,original,count,statement,?_⟩
  let addresses : (part ctx Q packet B).Key → List Reference :=
    PCSBCSCapturedSourceTransport.address
  let ref := openingReference ctx Q packet opening saved.shape.lanes
  let program := allocationProgram cap model ctx stack Q packet saved proofs B limit
  obtain ⟨f,captured⟩ := PCSBCSSourceRootCapture.capture_exists addresses ref
    (.inl current) mentioned program (table ctx Q packet B seed ro) visited
  obtain ⟨events,found,frozen,_⟩ := PCSBCSSourceRootCapture.capture_provenance addresses ref
    program (table ctx Q packet B seed ro) f captured
  have authentic : AuthenticLog seed f.queryPrefix := by
    rw [frozen]
    exact PCSBCSMerkleSeedProjection.firstMention_authentic seed ro addresses ref program events found
  have log : sourceLog addresses ref program (table ctx Q packet B seed ro) = f.queryPrefix := by
    rw [frozen]
    simp only [sourceLog,found,Option.getD_some,freeze_prefix]
  refine ⟨f,captured,authentic,?_,?_⟩
  · intro clean
    exact captured_sourceRoot seed addresses ref program (table ctx Q packet B seed ro) f
      captured (log.symm ▸ authentic) (log.symm ▸ clean)
  · obtain ⟨run,_,consistent⟩ := AnchoredMixedIdealSourceAcceptance.mixedView_runs
      cap .fresh model ctx stack Q packet saved proofs ctx.iv B limit seed ro
    rw [success] at run
    obtain ⟨_,_,_,_,observed⟩ := AnchoredPhysicalExecution.verifySource_execution
      cap .fresh model ctx stack Q packet saved proofs _ a run
    obtain ⟨proof,_,accepted,_⟩ := AnchoredIdealPhysicalAcceptance.observed_real
      (observed opening member) seed ctx.iv consistent
    exact WHIRPhysicalVerifier.openQuery_binding seed ctx.iv f.queryPrefix authentic
      ⟨recordDomain (records f.queryPrefix),[]⟩ rfl packet.val.profile opening.level
      saved.shape.lanes proof opening.root opening.sample opening.result accepted
end Driver

/-- Literal entered-packet full blocks, including the unused suffix of the last
block. The native answer is the inverse index cast of the actual source table
answer, not a supplied scalar-cache or compatible-answer certificate. -/
theorem entered_packet_codec (ctx : RawWHIRKeys.Context) (stack : ctx.mode = .stack)
    (Q : Nat) (packet : RawWHIRKeys.Packet ctx Q)
    (sourceTable : PCSStateRestoration.Latent.Table
      (PCSBCSSourceRootCapture.Key (p := packet.val.profile) (Q := Q) (iv := ctx.iv)
        (boundary := (RawWHIRKeys.entry ctx packet.val).frames.length))
      (PCSBCSSourceRootCapture.Answer)) :
    let current := PCSBCSNativePacketBridge.enteredPacket ctx stack Q packet
    let full := sourceTable (.inl current)
    let native := (PCSBCSNativePacketCodec.nativeFullBlocksEquiv ctx stack Q packet).symm full
    WHIRRawReplay.decodePacket ctx stack Q packet native = grouped current.2.coord full := by
  dsimp only
  rw [PCSBCSNativePacketCodec.decodePacket_eq_grouped]
  exact congrArg (grouped (PCSBCSNativePacketBridge.query ctx Q packet))
    ((PCSBCSNativePacketCodec.nativeFullBlocksEquiv ctx stack Q packet).apply_symm_apply
      (sourceTable (.inl (PCSBCSNativePacketBridge.enteredPacket ctx stack Q packet))))

#print axioms observed_snapshot
#print axioms mixed_success_captured_rows
#print axioms allocation_result
#print axioms entered_packet_codec
end Whir.PCSBCSCapturedIdealNativeAcceptance
