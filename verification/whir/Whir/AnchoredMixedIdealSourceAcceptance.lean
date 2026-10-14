import Whir.AnchoredIdealPhysicalAcceptance

/-! Actual mixed execution of the historical pre-#607 native source driver.
Source erasure and ordinary primitive consistency are derived from execution;
neither is an endpoint premise. Independent raw construction answers are left
untouched. The physical first-frozen registry invariant and preparedness are
explicit remaining causal hypotheses, not an identified PCS capture. -/
set_option autoImplicit false
namespace Whir.AnchoredMixedIdealSourceAcceptance
open Concrete Protocol FiatShamirGame DuplexFraming DuplexModeGame TypedOracleCompiler
open WHIRSourceChronology AnchoredPhysicalDriver PublicMerkleProgram WHIRPhysicalVerifier
open AnchoredPhysicalKnowledgeAcceptance (original)
open MerkleTransport

section Driver
variable (cap : Nat) (boundary : Boundary) (model : WHIRCallerSupport.ProductionLayout)
    (ctx : RawWHIRKeys.Context) (stack : ctx.mode = .stack) (Q : Nat)
    (packet : RawWHIRKeys.Packet ctx Q) (record : AnchoredHeaderCodec.Record)
    (proofs : Array PrunedMerklePaths) (iv : Digest32)
    (B : Nat) (limit : sourceBudget ctx Q packet ≤ B)

/-- The literal actual mixed compiler, at the driver's proved source budget.
B is the shared primitive/RO cap, not the historical packet ancestry cap Q. -/
def mixedView (seed : DuplexPublicSimulator.Seed) (ro : RawKey B → Digest32) :
    View (WHIRSourceChronology.Result cap (Option (Accepted ctx Q cap packet record))) :=
  Sampling.eval (PublicCompressionCouplingMixed.oracle seed ro)
    (PublicCompressionCouplingMixed.compile B iv []
      (WHIRSourceChronology.compile
        (AnchoredPhysicalDriver.verifySource cap boundary model ctx stack Q packet record proofs))
      (sourceBudget ctx Q packet) limit
      ((WHIRSourceChronology.compile_counted _ _).mpr
        (AnchoredPhysicalDriver.verifySource_counted cap boundary model ctx stack Q packet record proofs)))

/-- Both operational joins come from the actual execution. In particular, the
source event trace equals the observed trace even for rejecting continuations. -/
theorem mixedView_runs (seed : DuplexPublicSimulator.Seed) (ro : RawKey B → Digest32) :
    let view := mixedView cap boundary model ctx stack Q packet record proofs iv B limit seed ro
    Runs (WHIRSourceChronology.erase
      (AnchoredPhysicalDriver.verifySource cap boundary model ctx stack Q packet record proofs))
      view.observations view.result.value ∧
      WHIRSourceChronology.observations view.result.events = view.observations ∧
      AnchoredIdealPhysicalAcceptance.PrimitiveConsistent seed view.observations := by
  dsimp only
  let program := WHIRSourceChronology.compile
    (AnchoredPhysicalDriver.verifySource cap boundary model ctx stack Q packet record proofs)
  have counted : DuplexModeGame.Counts (sourceBudget ctx Q packet) program :=
    (WHIRSourceChronology.compile_counted _ _).mpr
      (AnchoredPhysicalDriver.verifySource_counted cap boundary model ctx stack Q packet record proofs)
  have compiledRun : Runs program
      (mixedView cap boundary model ctx stack Q packet record proofs iv B limit seed ro).observations
      (mixedView cap boundary model ctx stack Q packet record proofs iv B limit seed ro).result := by
    simp only [mixedView,PublicCompressionCouplingMixed.compile_actual]
    exact runIdeal_runs (DuplexPublicSimulator.simulator B) ro iv ⟨seed,[]⟩ program
      (sourceBudget ctx Q packet) limit counted
  obtain ⟨erased,observed⟩ := WHIRPhysicalCaller.compile_run
    (AnchoredPhysicalDriver.verifySource cap boundary model ctx stack Q packet record proofs) _ _ compiledRun
  refine ⟨erased,observed,?_⟩
  have authentic := PCSBCSMixedOrdinaryMerkle.runIdeal_initial_answers B seed ro iv program
    (sourceBudget ctx Q packet) limit counted
  simpa only [AnchoredIdealPhysicalAcceptance.PrimitiveConsistent,mixedView,
    PublicCompressionCouplingMixed.compile_actual,DuplexPublicSimulator.simulator,program] using authentic

/-- An actual successful mixed source run gives the native ideal acceptance
adapter its erased Runs and primitive-only answer facts. The only acceptance
premise is the actual driver's returned value, not native verification. -/
theorem mixed_success_prepared_experiment (seed : DuplexPublicSimulator.Seed)
    (ro : RawKey B → Digest32) (a : Accepted ctx Q cap packet record)
    (accepted : (mixedView cap boundary model ctx stack Q packet record proofs iv B limit seed ro).result.value = some a)
    (state : CausalBindingState.State cap) (invariant : WHIRPhysicalSnapshots.Invariant seed state)
    (initial : ∃ snap, MerkleTransport.Commitments.lookup record.root state.registry = some snap)
    (registered : CausalBindingState.Prepared state packet.val.profile
      ⟨packet.val.statement,packet.val.messages,[]⟩)
    (quiet : ∀ opening ∈ a.wire.openings, ∀ oldLog, state.frozenLog opening.root = some oldLog →
      ¬ PublicMerkleBinding.OpenPrimitiveBad seed oldLog opening.root opening.result.paths) :
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
  obtain ⟨run,_,answers⟩ := mixedView_runs cap boundary model ctx stack Q packet record proofs iv B limit seed ro
  rw [accepted] at run
  exact AnchoredIdealPhysicalAcceptance.verifySource_prepared_experiment
    cap boundary model ctx stack Q packet record proofs
    (mixedView cap boundary model ctx stack Q packet record proofs iv B limit seed ro).observations
    a run seed iv answers state invariant initial registered quiet

/-- The same join stated on actual runIdeal, rather than only its exactly equal
mixed lowering. All construction replies still come from the independent RO. -/
theorem runIdeal_success_prepared_experiment (seed : DuplexPublicSimulator.Seed)
    (ro : RawKey B → Digest32) (a : Accepted ctx Q cap packet record)
    (accepted : (runIdeal (DuplexPublicSimulator.simulator B) ro iv
      ((DuplexPublicSimulator.simulator B).initial seed)
      (WHIRSourceChronology.compile
        (AnchoredPhysicalDriver.verifySource cap boundary model ctx stack Q packet record proofs))
      (sourceBudget ctx Q packet) limit
      ((WHIRSourceChronology.compile_counted _ _).mpr
        (AnchoredPhysicalDriver.verifySource_counted cap boundary model ctx stack Q packet record proofs))).view.result.value = some a)
    (state : CausalBindingState.State cap) (invariant : WHIRPhysicalSnapshots.Invariant seed state)
    (initial : ∃ snap, MerkleTransport.Commitments.lookup record.root state.registry = some snap)
    (registered : CausalBindingState.Prepared state packet.val.profile
      ⟨packet.val.statement,packet.val.messages,[]⟩)
    (quiet : ∀ opening ∈ a.wire.openings, ∀ oldLog, state.frozenLog opening.root = some oldLog →
      ¬ PublicMerkleBinding.OpenPrimitiveBad seed oldLog opening.root opening.result.paths) :
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
  apply mixed_success_prepared_experiment cap boundary model ctx stack Q packet record proofs iv B limit
    seed ro a _ state invariant initial registered quiet
  simpa only [mixedView,PublicCompressionCouplingMixed.compile_actual,DuplexPublicSimulator.simulator] using accepted

end Driver
#print axioms mixedView_runs
#print axioms mixed_success_prepared_experiment
#print axioms runIdeal_success_prepared_experiment
end Whir.AnchoredMixedIdealSourceAcceptance
