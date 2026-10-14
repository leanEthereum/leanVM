import Whir.AnchoredPhysicalDriver
import Whir.WHIRPhysicalSoundness

/-! Operational inversion of the anchored receiver. The caller model, boundary,
answers and packet/opening executions below are pinned by the executed program,
not selected from the result's existential `origin` field. -/
namespace Whir.AnchoredPhysicalExecution
open Concrete Protocol FiatShamirGame PublicMerkleProgram WHIRSourceChronology DuplexModeGame
open WHIRPhysicalVerifier WHIRPhysicalReplay WHIRPhysicalOpeningRuns
open WHIRPhysicalCaller AnchoredPhysicalDriver
open RawOracleCoupling.Concrete
open MerkleTransport MerkleTransport.Commitments

 theorem finish_success (ctx : RawWHIRKeys.Context) (Q cap : Nat)
    (packet : RawWHIRKeys.Packet ctx Q) (record : AnchoredHeaderCodec.Record)
    (configured : configuration packet.val.profile record)
    (request : CausalBindingState.ClaimRequest cap packet.val.profile)
    (state : WireState packet.val.profile) (history : List (Sigma (GroupAnswer ctx Q)))
    (origin : ∃ boundary : Boundary, ∃ model : WHIRCallerSupport.ProductionLayout,
      ∃ answers : Coordinate → Option Digest32,
      record.shape = AnchoredSourceCaller.shape model.layout ∧
      AnchoredPhysicalDriver.request boundary cap packet.val.profile model.layout record
        (RawWHIRKeys.entry ctx packet.val) answers = some request)
    (a : Accepted ctx Q cap packet record)
    (success : AnchoredPhysicalDriver.finish ctx Q cap packet record configured request state history origin = some a) :
    a.request = request ∧ a.wire = state ∧ a.history = history := by
  unfold AnchoredPhysicalDriver.finish at success
  split at success
  · cases success
  · dsimp only at success
    split at success
    · cases success
    · split at success
      · cases success
      · cases Option.some.inj success
        exact ⟨rfl,rfl,rfl⟩

 theorem verifySource_success (cap : Nat) (boundary : Boundary)
    (model : WHIRCallerSupport.ProductionLayout) (ctx : RawWHIRKeys.Context)
    (stack : ctx.mode = .stack) (Q : Nat) (packet : RawWHIRKeys.Packet ctx Q)
    (record : AnchoredHeaderCodec.Record) (proofs : Array PrunedMerklePaths)
    (observations : List Observation) (a : Accepted ctx Q cap packet record)
    (run : Runs (erase (AnchoredPhysicalDriver.verifySource cap boundary model ctx stack Q packet record proofs))
      observations (some a)) :
    ∃ (configured : configuration packet.val.profile record)
      (same : record.shape = AnchoredSourceCaller.shape model.layout) (before after : List Observation)
      (request : CausalBindingState.ClaimRequest cap packet.val.profile),
      observations = before ++ after ∧
      before.length = (WHIRModeFinal.callerPositions ctx Q packet).length ∧
      before.map Observation.query = (WHIRModeFinal.callerPositions ctx Q packet).map
        (fun q => Query.construction q.val (RawWHIRKeys.callerOutput_admissible ctx Q packet q.val q.property)) ∧
      ∃ parsed : AnchoredPhysicalDriver.request boundary cap packet.val.profile model.layout record
          (RawWHIRKeys.entry ctx packet.val) (latestAnswers before) = some request,
        Runs (erase (readPhysicalPackets (cap := cap) ctx stack Q packet.val.profile record.shape.lanes proofs none
          (completion ctx Q packet) (completion_profiles ctx Q packet)
          (initialWireState packet.val.profile record.root)
          (fun state history => .done (AnchoredPhysicalDriver.finish ctx Q cap packet record configured request state history
            ⟨boundary,model,latestAnswers before,same,parsed⟩)))) after (some a) := by
  unfold AnchoredPhysicalDriver.verifySource at run
  split at run
  · rename_i configured
    split at run
    · simp only [erase] at run
      cases run
    · rename_i same
      simp only [erase] at run
      obtain ⟨before,after,traceEq,count,queries,continued⟩ := readCallerInputs_run ctx Q packet
        (WHIRModeFinal.callerPositions ctx Q packet) (fun _ => none) _ observations (some a) run
      split at continued
      · cases continued
      · rename_i request parsed
        exact ⟨configured,not_ne_iff.mp same,before,after,request,traceEq,count,queries,parsed,continued⟩
  · simp only [erase] at run
    cases run

private theorem runs_done_eq {R : Type} {left right : R} {trace : List Observation}
    (run : Runs (.done left) trace right) : left = right := by
  cases run
  rfl

/-- Actual success exposes the actual caller-prefix equation as well as the
complete packet trace and every retained Merkle opener subrun. -/
 theorem verifySource_execution (cap : Nat) (boundary : Boundary)
    (model : WHIRCallerSupport.ProductionLayout) (ctx : RawWHIRKeys.Context)
    (stack : ctx.mode = .stack) (Q : Nat) (packet : RawWHIRKeys.Packet ctx Q)
    (record : AnchoredHeaderCodec.Record) (proofs : Array PrunedMerklePaths)
    (observations : List Observation) (a : Accepted ctx Q cap packet record)
    (run : Runs (erase (AnchoredPhysicalDriver.verifySource cap boundary model ctx stack Q packet record proofs))
      observations (some a)) :
    (∃ before after, observations = before ++ after ∧
      before.length = (WHIRModeFinal.callerPositions ctx Q packet).length ∧
      before.map Observation.query = (WHIRModeFinal.callerPositions ctx Q packet).map
        (fun q => Query.construction q.val (RawWHIRKeys.callerOutput_admissible ctx Q packet q.val q.property)) ∧
      AnchoredPhysicalDriver.request boundary cap packet.val.profile model.layout record
        (RawWHIRKeys.entry ctx packet.val) (latestAnswers before) = some a.request) ∧
    a.request.root = record.root ∧ a.request.lanes = record.shape.lanes ∧
    Trace ctx stack Q packet.val.profile record.shape.lanes proofs (completion ctx Q packet)
      (initialWireState packet.val.profile record.root) a.wire a.history ∧
    (∀ opening ∈ a.wire.openings, ObservedOpening record.shape.lanes proofs observations opening) := by
  obtain ⟨configured,same,before,after,request,traceEq,count,queries,parsed,physical⟩ :=
    verifySource_success cap boundary model ctx stack Q packet record proofs observations a run
  obtain ⟨final,history,suffix,trace,last⟩ := readPhysicalPackets_trace ctx stack Q packet.val.profile
    record.shape.lanes proofs _ _ _ _ after a physical
  obtain ⟨requestEq,wireEq,historyEq⟩ := finish_success ctx Q cap packet record configured request final history
    _ a (runs_done_eq last)
  obtain ⟨_,_,_,root,lanes⟩ := request_origin boundary cap packet.val.profile model.layout record
    (RawWHIRKeys.entry ctx packet.val) (latestAnswers before) request parsed
  refine ⟨⟨before,after,traceEq,count,queries,by simpa only [requestEq] using parsed⟩,
    (congrArg (fun r => r.root) requestEq).trans root,requestEq ▸ lanes,?_,?_⟩
  · simpa only [← wireEq,← historyEq] using trace
  · obtain ⟨state,log,remaining,last,_,opened⟩ := readPhysicalCompletion_openings ctx stack Q packet
      record.shape.lanes proofs record.root _ after a physical
    obtain ⟨_,wireEq',_⟩ := finish_success ctx Q cap packet record configured request state log
      _ a (runs_done_eq last)
    intro opening member
    rw [wireEq'] at member
    apply (opened opening member).mono
    intro event present
    rw [traceEq]
    exact List.mem_append_right _ present

#print axioms finish_success
#print axioms verifySource_success
#print axioms verifySource_execution
end Whir.AnchoredPhysicalExecution
