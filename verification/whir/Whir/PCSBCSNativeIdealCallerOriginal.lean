import Whir.PCSBCSNativeCallerOriginal
import Whir.AnchoredMixedIdealSourceAcceptance
import Whir.PCSBCSIdealConstructionAnswers

/-! Exact caller preparation from the actual ideal source execution. Earlier
caller outputs are the same bounded raw RO entries used by the grouped source
table, not deterministic compression answers or a supplied compatibility map. -/
set_option autoImplicit false
namespace Whir.PCSBCSNativeIdealCallerOriginal
open Concrete Protocol FiatShamirGame DuplexFraming DuplexModeGame TypedOracleCompiler
open WHIRCallerSupport WHIRSourceChronology WHIRPhysicalCaller AnchoredPhysicalDriver
open PCSBCSSourceCallerOriginal PCSBCSRestorationHazard PCSRoundByRoundTranscriptState
open PCSBCSCallerBinding RawOracleCoupling PCSBCSChallengeOracle

variable {p : ParameterBounds.Profile} {B : Nat} {iv : Digest32} {boundary : Nat}
local notation "part" => EnteredPacket.partition (p := p) (Q := B) (iv := iv) (boundary := boundary)

/-- The bounded source getter is exactly the same raw construction lookup. -/
theorem split_answers (seed : DuplexPublicSimulator.Seed) (ro : RawKey B → Digest32)
    (q : Coordinate) (bounded : pathCost q ≤ B) :
    PCSBCSSourceCallerAnswers.answers ((part).split (PublicCompressionCouplingMixed.oracle seed ro)) q =
      ro (constructionKey B iv q bounded) := by
  rw [PCSBCSSourceCallerAnswers.answers_bounded _ _ bounded,Partition.join_split]
  rfl

section Caller
variable (cap : Nat) (model : ProductionLayout) (ctx : RawWHIRKeys.Context)
    (stack : ctx.mode = .stack) (Q : Nat) (packet : RawWHIRKeys.Packet ctx Q)
    (saved : AnchoredHeaderCodec.Record) (proofs : Array MerkleTransport.PrunedMerklePaths)
    (B : Nat) (limit : WHIRPhysicalVerifier.sourceBudget ctx Q packet ≤ B)
    (seed : DuplexPublicSimulator.Seed) (ro : RawKey B → Digest32)

private abbrev view := AnchoredMixedIdealSourceAcceptance.mixedView cap .fresh model ctx stack Q
  packet saved proofs ctx.iv B limit seed ro

private noncomputable abbrev sourceTable :=
  (EnteredPacket.partition (p := packet.val.profile) (Q := B) (iv := ctx.iv)
    (boundary := (RawWHIRKeys.entry ctx packet.val).frames.length)).split
    (PublicCompressionCouplingMixed.oracle seed ro)

theorem fresh_original (a : Accepted ctx Q cap packet saved) (familyCap : cap ≤ 2^64)
    (success : (view cap model ctx stack Q packet saved proofs B limit seed ro).result.value = some a) :
    ∃ input : CallerInput packet.val.profile,
      original packet.val.profile model.layout saved (RawWHIRKeys.entry ctx packet.val)
        (PCSBCSSourceCallerAnswers.answers (sourceTable ctx Q packet B seed ro)) = some input ∧
      input.m = a.request.claims.count ∧
      ∀ root ring, OriginalClaimsChecker.input input.prepared root ring =
        ⟨ParameterBounds.config packet.val.profile,saved.shape.lanes,root,
          AnchorPrefixRefinement.anchoredClaims (ParameterBounds.config packet.val.profile) saved
            a.request.claims.family a.request.claims.points ring⟩ := by
  obtain ⟨run,_,_⟩ := AnchoredMixedIdealSourceAcceptance.mixedView_runs
    cap .fresh model ctx stack Q packet saved proofs ctx.iv B limit seed ro
  rw [success] at run
  obtain ⟨caller,_,_,_,_⟩ := AnchoredPhysicalExecution.verifySource_execution
    cap .fresh model ctx stack Q packet saved proofs _ a run
  obtain ⟨before,after,splitTrace,_,queries,parsed⟩ := caller
  obtain ⟨_,shape,_,_,_,_,_,_,_,_⟩ := AnchoredPhysicalExecution.verifySource_success
    cap .fresh model ctx stack Q packet saved proofs _ a run
  have splitView : (view cap model ctx stack Q packet saved proofs B limit seed ro).observations = before ++ after :=
    splitTrace
  have earlier : ∀ wanted ∈ WHIRCallerOutputs.callerOutputs (RawWHIRKeys.entry ctx packet.val),
      latestAnswers before wanted = some
        (PCSBCSSourceCallerAnswers.answers (sourceTable ctx Q packet B seed ro) wanted) := by
    intro wanted prior
    have queried : Query.construction wanted (RawWHIRKeys.callerOutput_admissible ctx Q packet wanted prior) ∈
        before.map Observation.query := by
      rw [queries]
      exact List.mem_map.mpr ⟨⟨wanted,prior⟩,List.mem_attach _ _,rfl⟩
    obtain ⟨o,member,equal⟩ := List.mem_map.mp queried
    apply latestAnswers_consistent before wanted
      (RawWHIRKeys.callerOutput_admissible ctx Q packet wanted prior) _ ⟨o,member,equal⟩
    intro observation member valid same
    have present : observation ∈
        (view cap model ctx stack Q packet saved proofs B limit seed ro).observations := by
      rw [splitView]
      exact List.mem_append_left _ member
    have actual : ∃ bounded : pathCost wanted ≤ B,
        observation.answer = ro (constructionKey B ctx.iv wanted bounded) := by
      have construction : (⟨.construction wanted valid,observation.answer⟩ : Observation) ∈
          (view cap model ctx stack Q packet saved proofs B limit seed ro).observations := by
        cases observation
        cases same
        exact present
      simp only [view,AnchoredMixedIdealSourceAcceptance.mixedView,
        PublicCompressionCouplingMixed.compile_actual] at construction
      exact PCSBCSIdealConstructionAnswers.construction_observations _ ro ctx.iv _ _ _ _ _
        wanted valid _ construction
    obtain ⟨bounded,actual⟩ := actual
    rw [split_answers seed ro wanted bounded]
    exact actual
  obtain ⟨input,reconstructed,count,statement⟩ := PCSBCSNativeCallerOriginal.request_original
    cap packet.val.profile model saved a.configuration shape (RawWHIRKeys.entry ctx packet.val)
    (latestAnswers before) a.request familyCap parsed
  refine ⟨input,?_,count,statement⟩
  rw [← reconstructed]
  apply original_prior_only
  intro q member
  rw [earlier q member]
  rfl
end Caller
#print axioms split_answers
#print axioms fresh_original
end Whir.PCSBCSNativeIdealCallerOriginal
