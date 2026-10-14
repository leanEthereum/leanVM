import Whir.PCSBCSNativeCapturedRows
import Whir.PCSBCSNativeOracleReplay
import Whir.PCSBCSCapturedNativePhaseQuery

/-! First-address getters, not later physical registry getters. Native success
fixes the initial digest; every actual selected row comes from its own captured
prefix unless the retained primitive-opening bad event occurs. -/
set_option autoImplicit false
namespace Whir.PCSBCSNativeCapturedOracles
open Concrete Protocol FiatShamirGame DuplexModeGame TypedOracleCompiler
open MerkleTransport MerkleTransport.Commitments PublicMerkleLog
open WHIRPhysicalVerifier WHIRPhysicalReplay AnchoredPhysicalDriver
open PCSBCSSourceRootReferences

section Driver
variable (cap : Nat) (model : WHIRCallerSupport.ProductionLayout)
    (ctx : RawWHIRKeys.Context) (stack : ctx.mode = .stack) (Q : Nat)
    (packet : RawWHIRKeys.Packet ctx Q) (saved : AnchoredHeaderCodec.Record)
    (proofs : Array PrunedMerklePaths) (B : Nat)
    (limit : sourceBudget ctx Q packet ≤ B)
    (seed : DuplexPublicSimulator.Seed) (ro : RawKey B → Digest32)

noncomputable def logFor (root : Digest32) (level : Nat) : PublicLog :=
  PCSBCSNativeCapturedRows.referenceLog cap model ctx stack Q packet saved proofs B limit seed ro
    ⟨root,PCSBCSNativeRootRoles.nativeShape packet.val.profile saved level⟩

noncomputable def base : CausalGame.BaseOracle :=
  WHIRPhysicalRows.compactBaseOracle (hash seed)
    ⟨recordDomain (records (logFor cap model ctx stack Q packet saved proofs B limit seed ro saved.root 0)),[]⟩
    saved.root (ParameterBounds.length (ParameterBounds.config packet.val.profile) 0).log2
    (ParameterBounds.length (ParameterBounds.config packet.val.profile) 0)
    (leafWords packet.val.profile 0) saved.shape.lanes

noncomputable def roots : WHIRReplay.Roots := fun root level =>
  frozenQueryOracle (hash seed)
    ⟨recordDomain (records (logFor cap model ctx stack Q packet saved proofs B limit seed ro root level)),[]⟩
    root packet.val.profile level (2^(ParameterBounds.config packet.val.profile).folds[0]!)

theorem roots_rectangular (root : Digest32) (level : Nat) :
    oracleValid (roots cap model ctx stack Q packet saved proofs B limit seed ro root level)
      (ParameterBounds.length (ParameterBounds.config packet.val.profile) level)
      (2^(ParameterBounds.config packet.val.profile).folds[level]!) = true := by
  have shape := frozenQueryOracle_valid (hash seed)
    ⟨recordDomain (records (logFor cap model ctx stack Q packet saved proofs B limit seed ro root level)),[]⟩
    root packet.val.profile level (2^(ParameterBounds.config packet.val.profile).folds[0]!) (by rfl)
  by_cases zero : level = 0
  · simpa only [roots,zero,ite_true] using shape
  · simpa only [roots,ite_eq_right zero] using shape

theorem base_valid (fits : saved.shape.lanes ≤ 2^(ParameterBounds.config packet.val.profile).folds[0]!) :
    oracleValid (CausalGame.liftRoot (base cap model ctx stack Q packet saved proofs B limit seed ro))
      (2^((ParameterBounds.config packet.val.profile).logN-(ParameterBounds.config packet.val.profile).folds[0]!+
        (ParameterBounds.config packet.val.profile).rates[0]!)) saved.shape.lanes = true := by
  have shape := WHIRPhysicalVerifier.compactBaseOracle_valid (hash seed)
    ⟨recordDomain (records (logFor cap model ctx stack Q packet saved proofs B limit seed ro saved.root 0)),[]⟩
    saved.root (ParameterBounds.length (ParameterBounds.config packet.val.profile) 0).log2
    (ParameterBounds.length (ParameterBounds.config packet.val.profile) 0)
    (2^(ParameterBounds.config packet.val.profile).folds[0]!) saved.shape.lanes fits
  simpa only [base,leafWords,ite_true,ParameterBounds.length,
    PCSBCSNativeRootRoles.production_initial_remaining] using shape

theorem opening_log (profile : profileShape packet.val.profile saved.shape)
    (opening : QueryOpening packet.val.profile) :
    PCSBCSNativeCapturedRows.openingLog cap model ctx stack Q packet saved proofs B limit seed ro opening =
      logFor cap model ctx stack Q packet saved proofs B limit seed ro opening.root opening.level.val := by
  unfold PCSBCSNativeCapturedRows.openingLog logFor
  congr 1
  exact congrArg (fun shape => Reference.mk opening.root shape)
    (PCSBCSNativeRootRoles.nativeShape_opening packet.val.profile saved profile opening.level.val).symm

theorem verifySource_initial_root (a : Accepted ctx Q cap packet saved)
    (observations : List Observation)
    (run : PublicMerkleProgram.Runs (WHIRSourceChronology.erase
      (AnchoredPhysicalDriver.verifySource cap .fresh model ctx stack Q packet saved proofs)) observations (some a))
    (opening : QueryOpening packet.val.profile) (member : opening ∈ a.wire.openings)
    (zero : opening.level.val = 0) : opening.root = saved.root := by
  obtain ⟨_,_,_,trace,_⟩ := AnchoredPhysicalExecution.verifySource_execution
    cap .fresh model ctx stack Q packet saved proofs observations a run
  have rooted := WHIRPhysicalRoots.trace_rooted saved.root trace opening member
  have allRoots := WHIRPhysicalRoots.trace_roots saved.root
    (WHIRPhysicalReplay.completion_chain ctx Q packet) trace
  have label := rooted.1
  rw [allRoots,zero] at label
  have same : saved.root = opening.root := by simpa using label
  exact same.symm

theorem mixed_success_boundRows
    (a : Accepted ctx Q cap packet saved) (familyCap : cap ≤ 2^64)
    (success : (AnchoredMixedIdealSourceAcceptance.mixedView cap .fresh model ctx stack Q packet saved proofs
      ctx.iv B limit seed ro).result.value = some a)
    (quiet : ∀ opening ∈ a.wire.openings,
      ¬ PublicMerkleBinding.OpenPrimitiveBad seed
        (PCSBCSNativeCapturedRows.openingLog cap model ctx stack Q packet saved proofs B limit seed ro opening)
        opening.root opening.result.paths) :
    WHIRPhysicalRoots.BoundRows (base cap model ctx stack Q packet saved proofs B limit seed ro)
      (roots cap model ctx stack Q packet saved proofs B limit seed ro) a.wire := by
  obtain ⟨run,_,_⟩ := AnchoredMixedIdealSourceAcceptance.mixedView_runs cap .fresh model ctx stack Q packet
    saved proofs ctx.iv B limit seed ro
  rw [success] at run
  have row := PCSBCSNativeCapturedRows.mixed_success_captured_rows cap model ctx stack Q packet saved proofs
    B limit seed ro a familyCap success
  intro opening member
  have good := (row opening member).2.resolve_right (quiet opening member)
  rw [opening_log cap model ctx stack Q packet saved proofs B limit seed ro a.configuration.2 opening] at good
  by_cases zero : opening.level.val = 0
  · have rootEq := verifySource_initial_root cap model ctx stack Q packet saved proofs
      a _ run opening member zero
    simpa only [zero,rootEq,ite_true,base,frozenQueryOracle] using good
  · simpa only [roots,frozenQueryOracle,ite_eq_right zero] using good

theorem mixed_success_experiment
    (a : Accepted ctx Q cap packet saved) (familyCap : cap ≤ 2^64)
    (success : (AnchoredMixedIdealSourceAcceptance.mixedView cap .fresh model ctx stack Q packet saved proofs
      ctx.iv B limit seed ro).result.value = some a)
    (quiet : ∀ opening ∈ a.wire.openings,
      ¬ PublicMerkleBinding.OpenPrimitiveBad seed
        (PCSBCSNativeCapturedRows.openingLog cap model ctx stack Q packet saved proofs B limit seed ro opening)
        opening.root opening.result.paths) :
    ∃ replay : StackWHIRReplay.Replay packet.val.profile cap, ∃ proof,
      replay.original = PCSBCSNativeOracleReplay.original a
        (base cap model ctx stack Q packet saved proofs B limit seed ro) ∧
      a.wire.initial = some replay.initial ∧ a.wire.tape.1 = replay.initial.2 ∧
      replay.whir.replies.map WHIRPhysicalErasure.eraseReply = a.wire.replies ∧
      CausalGame.opening (ParameterBounds.config packet.val.profile)
        (CausalGame.challenges (ParameterBounds.config packet.val.profile) a.wire.tape)
        replay.whir.replies = .ok proof ∧
      WHIRPhysicalHistory.decodeStack packet.val.profile cap
        (fun _ => some (PCSBCSNativeOracleReplay.original a
          (base cap model ctx stack Q packet saved proofs B limit seed ro)))
        (roots cap model ctx stack Q packet saved proofs B limit seed ro) (fun i => a.wire.rows[i]!)
        ⟨packet.val.statement,packet.val.messages,(localHistory ctx stack Q packet.val.profile a.history).tail⟩ =
        some replay ∧
      CausalGame.experiment
        (PCSBCSNativeOracleReplay.input a
          (base cap model ctx stack Q packet saved proofs B limit seed ro) replay.initial.1)
        (CausalStrategy.indexedStrategy replay.whir.replies) a.wire.tape = true := by
  obtain ⟨run,_,_⟩ := AnchoredMixedIdealSourceAcceptance.mixedView_runs cap .fresh model ctx stack Q packet
    saved proofs ctx.iv B limit seed ro
  rw [success] at run
  obtain ⟨_,_,lanesEq,_,_⟩ := AnchoredPhysicalExecution.verifySource_execution
    cap .fresh model ctx stack Q packet saved proofs _ a run
  have fits : saved.shape.lanes ≤ 2^(ParameterBounds.config packet.val.profile).folds[0]! := by
    rw [← lanesEq]
    exact a.request.lane_bound
  exact PCSBCSNativeOracleReplay.verifySource_experiment .fresh model proofs _ a run
    (base cap model ctx stack Q packet saved proofs B limit seed ro)
    (roots cap model ctx stack Q packet saved proofs B limit seed ro)
    (base_valid cap model ctx stack Q packet saved proofs B limit seed ro fits)
    (roots_rectangular cap model ctx stack Q packet saved proofs B limit seed ro)
    (mixed_success_boundRows cap model ctx stack Q packet saved proofs B limit seed ro a familyCap success quiet)

end Driver
#print axioms roots_rectangular
#print axioms base_valid
#print axioms opening_log
#print axioms verifySource_initial_root
#print axioms mixed_success_boundRows
#print axioms mixed_success_experiment
end Whir.PCSBCSNativeCapturedOracles
