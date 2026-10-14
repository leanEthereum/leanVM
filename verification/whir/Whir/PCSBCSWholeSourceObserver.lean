import Whir.PCSBCSWholeNativeCaptureTransport
import Whir.PCSBCSNativePublicCapture
import Whir.PCSBCSNativeSourceTables
import Whir.PCSBCSSourceKnowledgeComposition
import Whir.PCSBCSPublicPrimitiveOpening
import Whir.PublicCompressionModeSecurity

/-! Historical pre607 PCS-only whole-source public knowledge observer. The
caller class is structural over every reachable attacker output, including
rejected inputs. It fixes public profile, entry boundary and caller grammar
before batch coins, but not the caller's adaptively decoded points or values.
This is not a current compiled verifier refinement or concrete BLAKE2s claim. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000
namespace Whir.PCSBCSWholeSourceObserver
open Concrete Protocol FiatShamirGame DuplexModeGame TypedOracleCompiler
open RawOracleCoupling PCSBCSChallengeOracle PCSBCSSourceRootReferences
open PCSBCSCapturedNativeReplyBridge PCSBCSCapturedSourceAcceptance
open PCSBCSWholeNativeCaptureTransport PCSBCSNativePublicCapture
open WHIRPhysicalVerifier PublicMerkleLog

variable (cap : Nat) (registry : WHIRPhysicalDriver.ProductionRegistry) (Q : Nat)

/-- Public geometry and grammar of a caller input, independently of whether
its subsequent verifier execution accepts. Caller points and values are still
computed by the genuine fresh caller preparation from earlier public answers. -/
def FixedMetadata (p : ParameterBounds.Profile)
    (layout : WHIRCallerClaims.CallerLayout) (boundary : Nat)
    (input : AnchoredPhysicalAfter.Input registry.context Q) : Prop :=
  input.packet.val.profile = p ∧
  (RawWHIRKeys.entry registry.context input.packet.val).frames.length = boundary ∧
  (registry.packetModel Q input.packet).layout = layout

/-- Every answer continuation of the source attacker is in this public caller
class. There is no restriction to accepted outputs or a favorable hidden table. -/
def SourceClass (p : ParameterBounds.Profile)
    (layout : WHIRCallerClaims.CallerLayout) (boundary : Nat)
    (attacker : WHIRSourceChronology.Source cap (AnchoredPhysicalAfter.Input registry.context Q)) : Prop :=
  WHIRSourceBackfill.AllResults (FixedMetadata registry Q p layout boundary)
    (WHIRSourceChronology.erase attacker)

private theorem allResults_runs {R : Type} (program : Program R) (post : R → Prop)
    (all : WHIRSourceBackfill.AllResults post program)
    (trace : List Observation) (result : R) (run : PublicMerkleProgram.Runs program trace result) :
    post result := by
  induction run with
  | done => exact all
  | ask answer run ih => exact ih (all answer)

section Mixed
variable (attacker : WHIRSourceChronology.Source cap (AnchoredPhysicalAfter.Input registry.context Q))
    (A B : Nat) (limit : A ≤ B)
    (counted : Counts A (PCSBCSNativePhysicalFreeze.wholeProgram cap registry Q attacker))
    (seed : PrimitiveOracle) (ro : RawKey B → Digest32)
local notation "view" => PCSBCSWholeNativePacketCoverage.mixedView cap registry Q attacker A B limit counted seed ro

/-- Structural class membership follows from the actual attacker subrun. -/
theorem mixed_success_metadata (p : ParameterBounds.Profile)
    (layout : WHIRCallerClaims.CallerLayout) (boundary : Nat)
    (sourceClass : SourceClass cap registry Q p layout boundary attacker)
    (a : AnchoredPhysicalAfter.Accepted registry.context Q cap)
    (success : (view).result.value = some a) : FixedMetadata registry Q p layout boundary a.input := by
  obtain ⟨before,_,_,run,_,_⟩ := PCSBCSWholeNativePacketCoverage.mixed_success_native_segment
    cap registry Q attacker A B limit counted seed ro a success
  exact allResults_runs _ _ sourceClass before a.input run

/-- Caller-output coverage is derived from the fresh caller's actual queried
prefix, which is retained in the whole public view. -/
theorem mixed_success_publicOriginal (a : AnchoredPhysicalAfter.Accepted registry.context Q cap)
    (success : (view).result.value = some a) :
    publicOriginal a.input.packet.val.profile (registry.packetModel Q a.input.packet).layout
      a.input.record (RawWHIRKeys.entry registry.context a.input.packet.val) view =
      PCSBCSSourceCallerOriginal.original a.input.packet.val.profile
        (registry.packetModel Q a.input.packet).layout a.input.record
        (RawWHIRKeys.entry registry.context a.input.packet.val)
        (PCSBCSSourceCallerAnswers.answers (table (boundary :=
          (RawWHIRKeys.entry registry.context a.input.packet.val).frames.length)
          a.input.packet seed ro)) := by
  apply publicOriginal_recorded seed ro _ A limit counted
  obtain ⟨before,after,split,_,run,_⟩ := PCSBCSWholeNativePacketCoverage.mixed_success_native_segment
    cap registry Q attacker A B limit counted seed ro a success
  obtain ⟨⟨caller,physical,nativeSplit,_,queries,_⟩,_,_,_,_⟩ :=
    AnchoredPhysicalExecution.verifySource_execution cap .fresh (registry.packetModel Q a.input.packet)
      registry.context rfl Q a.input.packet a.input.record a.input.proofs after a.native run
  intro wanted prior
  have queried : Query.construction wanted
      (RawWHIRKeys.callerOutput_admissible registry.context Q a.input.packet wanted prior) ∈
      caller.map Observation.query := by
    rw [queries]
    exact List.mem_map.mpr ⟨⟨wanted,prior⟩,List.mem_attach _ _,rfl⟩
  obtain ⟨o,member,equal⟩ := List.mem_map.mp queried
  refine ⟨RawWHIRKeys.callerOutput_admissible registry.context Q a.input.packet wanted prior,o.answer,?_⟩
  have present : o ∈ (view).observations := by
    rw [split,nativeSplit]
    exact List.mem_append_right _ (List.mem_append_left _ member)
  cases o
  cases equal
  exact present

/-- A full native capture supplies every accepting source witness field. The
only failure input is the genuine public extractor predicate on that view. -/
theorem capture_failure (a : AnchoredPhysicalAfter.Accepted registry.context Q cap)
    (success : (view).result.value = some a)
    (capture : CaptureResult (stack := rfl) a.input.packet a.input.record
      (wholeAllocation cap registry Q attacker A B limit counted a) seed ro
      (registry.packetModel Q a.input.packet) a.native)
    (clean : ∀ ref, ¬ OutputCollision
      (wholeReferenceLog cap registry Q attacker A B limit counted seed ro a ref))
    (failed : publicExtractionFailed (p := a.input.packet.val.profile) (B := B)
      (iv := registry.context.iv)
      (boundary := (RawWHIRKeys.entry registry.context a.input.packet.val).frames.length)
      (registry.packetModel Q a.input.packet).layout a.input.record
      (RawWHIRKeys.entry registry.context a.input.packet.val)
      ⟨a.input.record.root,initialShape a.input.record.shape⟩ view) :
    PCSBCSAdaptiveSourceKnowledgeProbability.Failed (registry.packetModel Q a.input.packet).layout
      (wholeAllocation cap registry Q attacker A B limit counted a) (table
        (boundary := (RawWHIRKeys.entry registry.context a.input.packet.val).frames.length)
        a.input.packet seed ro) := by
  obtain ⟨original,decoded,failed⟩ := failed
  rw [mixed_success_publicOriginal cap registry Q attacker A B limit counted seed ro a success,
    capture.original_decoded] at decoded
  have originalEq := Option.some.inj decoded
  subst original
  have publicClean : ¬ OutputCollision (publicLog
      (PCSBCSCapturedSourceTransport.address (p := a.input.packet.val.profile) (Q := B)
        (iv := registry.context.iv)
        (boundary := (RawWHIRKeys.entry registry.context a.input.packet.val).frames.length))
      ⟨a.input.record.root,initialShape a.input.record.shape⟩ view) := by
    have eqLog := publicLog_actual seed ro
      (PCSBCSNativePhysicalFreeze.wholeProgram cap registry Q attacker) A limit counted
      (PCSBCSCapturedSourceTransport.address (p := a.input.packet.val.profile) (Q := B)
        (iv := registry.context.iv)
        (boundary := (RawWHIRKeys.entry registry.context a.input.packet.val).frames.length))
      ⟨a.input.record.root,initialShape a.input.record.shape⟩
    dsimp only at eqLog
    simp only [Atomic.eval_program,Partition.join_split] at eqLog
    rw [← eqLog]
    exact clean _
  have publicClean' := publicClean
  rw [← PCSBCSWholeNativePacketCoverage.allocationView_mixed cap registry Q attacker
    A B limit counted seed ro a.input.packet.val.profile
    (RawWHIRKeys.entry registry.context a.input.packet.val).frames.length] at publicClean'
  have root := publicRoot_actual seed ro
    (PCSBCSNativePhysicalFreeze.wholeProgram cap registry Q attacker) A limit counted
    (PCSBCSCapturedSourceTransport.address (p := a.input.packet.val.profile) (Q := B)
      (iv := registry.context.iv)
      (boundary := (RawWHIRKeys.entry registry.context a.input.packet.val).frames.length))
    ⟨a.input.record.root,initialShape a.input.record.shape⟩ publicClean'
  dsimp only at root
  simp only [Atomic.eval_program,Partition.join_split] at root
  rw [root] at failed
  refine ⟨{
    saved := a.input.record
    original := capture.original
    constructed := ?_
    native := {
      primitive := seed
      final := capture.final
      claims := capture.claims
      valid := a.native.configuration.1
      profile := a.native.configuration.2
      caller := ?_
      bound := capture.bound_original
      terminal := capture.terminal
      recorded := capture.recorded
      authentic := ?_
      clean := clean _
      ring := capture.replay.initial.1
      tape := a.native.wire.tape
      strategy := fun _ => CausalStrategy.indexedStrategy capture.replay.whir.replies
      raws := capture.raws
      transport := ?_
      accepted := capture.experiment
      failed := failed } }⟩
  · rw [capture.entry]
    exact capture.caller_decoded
  · exact referenceLog_authentic a.input.packet _ seed ro _
  · intro current member
    rw [capture.native_replies]
    exact capture.transport current member
  · rw [capture.entry]
    exact capture.original_decoded
end Mixed

/-- The literal whole source result and observations, not a projected verifier
suffix or a seed-indexed observer. -/
abbrev WholeSourceView := View (WHIRSourceChronology.Result cap
  (Option (AnchoredPhysicalAfter.Accepted registry.context Q cap)))

/-- Actual native acceptance followed by failure of the public, computable
round-by-round extractor. Public reconstruction supplies the original. -/
def PublicFailure (B : Nat) (view : WholeSourceView cap registry Q) : Prop :=
  ∃ a, view.result.value = some a ∧
    publicExtractionFailed (p := a.input.packet.val.profile) (B := B)
      (iv := registry.context.iv)
      (boundary := (RawWHIRKeys.entry registry.context a.input.packet.val).frames.length)
      (registry.packetModel Q a.input.packet).layout a.input.record
      (RawWHIRKeys.entry registry.context a.input.packet.val)
      ⟨a.input.record.root,initialShape a.input.record.shape⟩ view

/-- All exclusions are finite public checks on the same whole view. There is
no quantification over hidden tables or an assumed soundness certificate. -/
def Good (B : Nat) (view : WholeSourceView cap registry Q) : Prop :=
  PublicFailure cap registry Q B view ∧
  ¬ OutputCollision (PCSBCSPublicPrimitiveOpening.publicOrdinaryLog B registry.context.iv view) ∧
  ∀ a, view.result.value = some a → ∀ opening ∈ a.native.wire.openings,
    ¬ PCSBCSPublicPrimitiveOpening.publicBadOpening B registry.context.iv
      (boundary := (RawWHIRKeys.entry registry.context a.input.packet.val).frames.length)
      (PCSBCSNativeRootRoles.openingRole a.input.record opening) view opening

open Classical in
noncomputable def failureObserver (B : Nat) (view : WholeSourceView cap registry Q) : Bool :=
  decide (PublicFailure cap registry Q B view)

open Classical in
noncomputable def goodObserver (B : Nat) (view : WholeSourceView cap registry Q) : Bool :=
  decide (Good cap registry Q B view)

section Observer
variable (attacker : WHIRSourceChronology.Source cap (AnchoredPhysicalAfter.Input registry.context Q))
    (B : Nat) (counted : Counts B (PCSBCSNativePhysicalFreeze.wholeProgram cap registry Q attacker))
    (p : ParameterBounds.Profile) (layout : WHIRCallerClaims.CallerLayout) (boundary : Nat)
    (familyCap : cap ≤ 2^64)
    (sourceClass : SourceClass cap registry Q p layout boundary attacker)
local notation "whole" => PCSBCSNativePhysicalFreeze.wholeProgram cap registry Q attacker

include familyCap sourceClass in
/-- ALL typed tables are realized by the existing inverse partition. Native
caller/reply acceptance evidence is derived by actual mixed whole success. -/
theorem observerRefines :
    PCSBCSSourceKnowledgeGame.ObserverRefines (p := p) (iv := registry.context.iv)
      (boundary := boundary) layout whole counted (goodObserver cap registry Q B) := by
  classical
  intro typed observed
  obtain ⟨seed,ro,equal⟩ := PCSBCSNativeSourceTables.every_table typed
  rw [← equal] at observed ⊢
  simp only [PCSBCSSourceKnowledgeGame.source,Atomic.eval_program,Partition.join_split] at observed
  have good : Good cap registry Q B
      (PCSBCSWholeNativePacketCoverage.mixedView cap registry Q attacker B B (by rfl) counted seed ro) :=
    of_decide_eq_true observed
  obtain ⟨⟨a,success,failed⟩,clean,quiet⟩ := good
  have logs := PCSBCSPublicPrimitiveOpening.wholeReferenceLog_clean cap registry Q attacker
    B B (by rfl) counted seed ro a clean
  have exclusions : ∀ opening ∈ a.native.wire.openings,
      ¬ PublicMerkleBinding.OpenPrimitiveBad seed
        (wholeOpeningLog cap registry Q attacker B B (by rfl) counted seed ro a opening)
        opening.root opening.result.paths := by
    intro opening member bad
    exact quiet a success opening member
      ((PCSBCSPublicPrimitiveOpening.mixed_success_publicBadOpening_iff cap registry Q attacker
        B B (by rfl) counted seed ro a success opening member).mpr bad)
  obtain ⟨capture⟩ := mixed_success_capture_replyTransport cap registry Q attacker
    B B (by rfl) counted seed ro a familyCap success exclusions logs
  obtain ⟨profile,entry,grammar⟩ := mixed_success_metadata cap registry Q attacker
    B B (by rfl) counted seed ro p layout boundary sourceClass a success
  subst p boundary layout
  exact capture_failure cap registry Q attacker B B (by rfl) counted seed ro
    a success capture logs failed
end Observer

section Real
variable (nativeRegistry : {r : WHIRPhysicalDriver.ProductionRegistry //
      r.context.iv = PCSBCSSourceCoordinateDecoder.seedIV})
    (attacker : WHIRSourceChronology.Source cap (AnchoredPhysicalAfter.Input nativeRegistry.val.context Q))
    (B : Nat) (counted : Counts B (PCSBCSNativePhysicalFreeze.wholeProgram cap nativeRegistry.val Q attacker))
local notation "whole" => PCSBCSNativePhysicalFreeze.wholeProgram cap nativeRegistry.val Q attacker

/-- The SAME complete physical alarm excludes every accepted native opening
bad event, without a separate physical-freeze or scanner-admission premise. -/
theorem actual_opening_quiet (rootRegistry : AnchoredHeaderRoots.Public) (C : PrimitiveOracle)
    (a : AnchoredPhysicalAfter.Accepted nativeRegistry.val.context Q cap)
    (success : (runReal C nativeRegistry.val.context.iv whole).view.result.value = some a)
    (quiet : PublicMerkleProbability.traceAlarm
      (PCSBCSSourcePrimitiveRootBudget.targets a.input.packet.val.profile B
        (RawWHIRKeys.entry nativeRegistry.val.context a.input.packet.val).frames.length rootRegistry) []
      (PublicCompressionProgram.primitiveLog C nativeRegistry.val.context.iv whole B counted) = false) :
    ∀ opening ∈ a.native.wire.openings,
      ¬ PublicMerkleBinding.OpenPrimitiveBad C
        (wholeOpeningLog cap nativeRegistry.val Q attacker B B (by rfl) counted C
          (WHIRRealSimulator.rawTable B C) a opening) opening.root opening.result.paths := by
  intro opening member
  have mentioned := PCSBCSWholeNativePacketCoverage.actual_success_opening_firstMention
    cap nativeRegistry.val Q attacker B B (by rfl) counted C a success opening member
  rw [openingReference_eq_role a.input.packet a.input.record a.native.configuration.2 opening,
    nativeRegistry.property] at mentioned
  obtain ⟨events,mentioned⟩ := mentioned
  have evaluated := PCSBCSNativePhysicalFreeze.whole_success_evaluated
    cap nativeRegistry.val Q attacker C B counted a success opening member
  have quiet' := quiet
  rw [nativeRegistry.property] at quiet'
  have excluded := PCSBCSNativeCompleteAlarm.firstMention_opening_quiet
    a.input.packet.val.profile B (RawWHIRKeys.entry nativeRegistry.val.context a.input.packet.val).frames.length
    rootRegistry C whole B (by rfl) counted (PCSBCSNativeRootRoles.openingRole a.input.record opening)
    events mentioned quiet' opening.result.paths
    (by intro path present bytes input; exact (evaluated path present bytes input).1)
    (by
      intro path present bytes input event found
      simpa only [nativeRegistry.property] using (evaluated path present bytes input).2 event found)
  change ¬ PublicMerkleBinding.OpenPrimitiveBad C
    (PCSBCSNativePhysicalFreeze.actualSourceLog (p := a.input.packet.val.profile)
      (iv := nativeRegistry.val.context.iv)
      (boundary := (RawWHIRKeys.entry nativeRegistry.val.context a.input.packet.val).frames.length)
      C whole B (by rfl) counted (PCSBCSNativeRootRoles.openingRole a.input.record opening))
    opening.root opening.result.paths
  simpa only [PCSBCSNativeRootRoles.openingRole,nativeRegistry.property] using excluded

/-- Pointwise real reduction to exactly the modeled complete trace alarm. -/
theorem real_failure_good_or_alarm (p : ParameterBounds.Profile)
    (layout : WHIRCallerClaims.CallerLayout) (boundary : Nat)
    (sourceClass : SourceClass cap nativeRegistry.val Q p layout boundary attacker)
    (rootRegistry : AnchoredHeaderRoots.Public) (C : PrimitiveOracle)
    (failed : failureObserver cap nativeRegistry.val Q B
      (runReal C nativeRegistry.val.context.iv whole).view = true) :
    goodObserver cap nativeRegistry.val Q B (runReal C nativeRegistry.val.context.iv whole).view = true ∨
    PublicMerkleProbability.traceAlarm
      (PCSBCSSourcePrimitiveRootBudget.targets p B boundary rootRegistry) []
      (PublicCompressionProgram.primitiveLog C nativeRegistry.val.context.iv whole B counted) = true := by
  classical
  by_cases alarm : PublicMerkleProbability.traceAlarm
      (PCSBCSSourcePrimitiveRootBudget.targets p B boundary rootRegistry) []
      (PublicCompressionProgram.primitiveLog C nativeRegistry.val.context.iv whole B counted) = true
  · exact Or.inr alarm
  have quiet := Bool.eq_false_iff.mpr alarm
  have failure : PublicFailure cap nativeRegistry.val Q B
      (runReal C nativeRegistry.val.context.iv whole).view := of_decide_eq_true failed
  obtain ⟨a,success,extractionFailed⟩ := failure
  have mixedSuccess := success
  rw [← PCSBCSWholeNativePacketCoverage.actual_mixedView cap nativeRegistry.val Q attacker
    B B (by rfl) counted C] at mixedSuccess
  obtain ⟨profile,entry,_⟩ := mixed_success_metadata cap nativeRegistry.val Q attacker
    B B (by rfl) counted C (WHIRRealSimulator.rawTable B C)
    p layout boundary sourceClass a mixedSuccess
  have ordinary := PCSBCSPublicPrimitiveOpening.publicOrdinaryLog_actual
    (p := p) (iv := nativeRegistry.val.context.iv) (boundary := boundary)
    C (WHIRRealSimulator.rawTable B C) whole B (by rfl) counted
  simp only [Atomic.eval_program,Partition.join_split] at ordinary
  change PCSBCSPublicPrimitiveOpening.publicOrdinaryLog B nativeRegistry.val.context.iv
    (PCSBCSWholeNativePacketCoverage.mixedView cap nativeRegistry.val Q attacker
      B B (by rfl) counted C (WHIRRealSimulator.rawTable B C)) = _ at ordinary
  rw [PCSBCSWholeNativePacketCoverage.actual_mixedView cap nativeRegistry.val Q attacker
    B B (by rfl) counted C] at ordinary
  apply Or.inl
  apply decide_eq_true
  refine ⟨⟨a,success,extractionFailed⟩,?_,?_⟩
  · rw [ordinary]
    intro collision
    have loud := PCSBCSNativePhysicalMerkleBad.mixed_atomic_collision_alarm
      (p := p) (boundary := boundary) C nativeRegistry.val.context.iv whole B (by rfl) counted
      (PCSBCSSourcePrimitiveRootBudget.targets p B boundary rootRegistry) collision
    exact alarm loud
  · intro accepted acceptedSuccess opening member bad
    have same := Option.some.inj (success.symm.trans acceptedSuccess)
    subst accepted
    have quiet' := quiet
    rw [← profile,← entry] at quiet'
    have excluded := actual_opening_quiet cap Q nativeRegistry attacker B counted rootRegistry C a success quiet'
    apply excluded opening member
    apply (PCSBCSPublicPrimitiveOpening.mixed_success_publicBadOpening_iff cap nativeRegistry.val Q
      attacker B B (by rfl) counted C (WHIRRealSimulator.rawTable B C) a mixedSuccess opening member).mp
    rw [PCSBCSWholeNativePacketCoverage.actual_mixedView]
    exact bad
end Real

section Composition
variable {Coins : Type} [Fintype Coins] [Nonempty Coins]
    (nativeRegistry : {r : WHIRPhysicalDriver.ProductionRegistry //
      r.context.iv = PCSBCSSourceCoordinateDecoder.seedIV})
    (attacker : Coins → WHIRSourceChronology.Source cap (AnchoredPhysicalAfter.Input nativeRegistry.val.context Q))
    (B : Nat) (counted : ∀ coins, Counts B (PCSBCSNativePhysicalFreeze.wholeProgram cap nativeRegistry.val Q (attacker coins)))
    (p : ParameterBounds.Profile) (layout : WHIRCallerClaims.CallerLayout) (boundary : Nat)
    (sourceClass : ∀ coins, SourceClass cap nativeRegistry.val Q p layout boundary (attacker coins))
    (rootRegistry : AnchoredHeaderRoots.Public)
local notation "adversary" => fun coins => PCSBCSNativePhysicalFreeze.wholeProgram cap nativeRegistry.val Q (attacker coins)

omit [Fintype Coins] [Nonempty Coins] in
include sourceClass in
theorem realReduction :
    PCSBCSSourceKnowledgeComposition.Reduction (p := p) (iv := nativeRegistry.val.context.iv)
      (boundary := boundary) rootRegistry adversary counted
      (failureObserver cap nativeRegistry.val Q B) (goodObserver cap nativeRegistry.val Q B) := by
  intro C coins failed
  exact real_failure_good_or_alarm cap Q nativeRegistry (attacker coins) B (counted coins)
    p layout boundary (sourceClass coins) rootRegistry C failed

include counted sourceClass rootRegistry in
/-- Full historical PCS-only random-compression endpoint, using the genuine
public observer and the derived ALL-table and SAME-alarm obligations. B counts
all ordinary calls plus full construction-path work, not distinct native calls. -/
theorem random_compression_failure_probability (familyCap : cap ≤ 2^64) :
    realProbability nativeRegistry.val.context.iv adversary (failureObserver cap nativeRegistry.val Q B) ≤
      (B : ℚ)*PCSRoundByRoundKnowledge.rbrError + duplexModeLoss B +
      ((B : ℚ)^3+3*(B : ℚ)^2-2*(B : ℚ))/2^256 := by
  apply PCSBCSSourceKnowledgeComposition.random_compression_failure_probability
    (p := p) (boundary := boundary) rootRegistry layout adversary counted
    (failureObserver cap nativeRegistry.val Q B) (goodObserver cap nativeRegistry.val Q B)
  · intro coins
    exact observerRefines cap nativeRegistry.val Q (attacker coins) B (counted coins)
      p layout boundary familyCap (sourceClass coins)
  · exact realReduction cap Q nativeRegistry attacker B counted p layout boundary sourceClass rootRegistry

include counted sourceClass rootRegistry in
/-- The q56 RBR, 256-bit coupling, and complete Merkle terms are kept separate.
The variable B is the aggregate public source primitive-work budget. -/
theorem explicit_failure_probability (familyCap : cap ≤ 2^64) :
    realProbability nativeRegistry.val.context.iv adversary (failureObserver cap nativeRegistry.val Q B) ≤
      (B : ℚ)*((17/32 : ℚ)^56 + 1/2^78) +
      min 1 ((2*(B : ℚ)^2-(B : ℚ))/2^256) +
      ((B : ℚ)^3+3*(B : ℚ)^2-2*(B : ℚ))/2^256 := by
  simpa only [PCSRoundByRoundKnowledge.rbrError,SupportedCandidateExtraction.radiusEnvelope,
    duplexModeLoss_eq] using random_compression_failure_probability
      cap Q nativeRegistry attacker B counted p layout boundary sourceClass rootRegistry familyCap
end Composition

#print axioms observerRefines
#print axioms realReduction
#print axioms random_compression_failure_probability

#print axioms explicit_failure_probability
end Whir.PCSBCSWholeSourceObserver
