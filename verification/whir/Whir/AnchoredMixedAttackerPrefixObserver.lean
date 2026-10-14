import Whir.AnchoredMixedAttackerPrefixSource
import Whir.PCSBCSNativePhysicalMerkleBad

/-! Historical pre-#607 anchored source prefixes use the SAME complete physical
Merkle alarm as the public source observer. This join derives the ordinary
collision guard, rather than charging a second event or assuming clean caches.
It does not claim a current Rust-to-Lean or #607 transcript correspondence. -/
set_option autoImplicit false
namespace Whir.AnchoredMixedAttackerPrefixObserver
open Concrete FiatShamirGame DuplexModeGame TypedOracleCompiler
open PublicCompressionProgram PublicMerkleLog
open AnchoredHeaderRoots AnchoredMixedAttackerPrefix AnchoredMixedAttackerPrefixSource

/-- Every literal ordinary observation, including cache hits, belongs to the
actual complete primitive trace under the real construction table. -/
theorem ordinary_subset {Q : Nat} {R : Type} (C : PrimitiveOracle) (iv : Digest32)
    (program : Program R) (remaining : Nat) (cap : remaining ≤ Q)
    (counted : Counts remaining program) :
    let view := Sampling.eval
      (PublicCompressionCouplingMixed.oracle C (WHIRRealSimulator.rawTable Q C))
      (PublicCompressionCouplingMixed.compile Q iv [] program remaining cap counted)
    ∀ record ∈ PCSBCSMerkleSeedProjection.ordinaryObservations view.observations,
      record ∈ primitiveLog C iv program remaining counted := by
  intro view record member
  obtain ⟨observation,present,parsed⟩ := List.mem_filterMap.mp member
  rcases observation with ⟨query,answer⟩
  cases query with
  | construction coordinate valid => simp at parsed
  | primitive purpose input =>
    by_cases ordinary : DuplexFraming.tag input = 0
    · simp only [ordinary,↓reduceIte,Option.some.injEq] at parsed
      subst record
      have actual : view = (runReal C iv program).view := by
        dsimp only [view]
        rw [PublicCompressionCouplingMixed.compile_actual]
        exact WHIRRealSimulator.runIdeal_view C iv _ ⟨rfl,by simp⟩ _ _ cap _
      rw [actual] at present
      have included := PCSBCSConstructionReplayTrace.observation_trace_membership
        C iv program remaining counted _ present
      have authentic := PCSBCSConstructionReplayTrace.observation_answer C iv program _ present
      change answer = C input at authentic
      apply included (input,answer)
      exact List.mem_singleton.mpr (Prod.ext rfl authentic)
    · simp [ordinary] at parsed

/-- The anchored cache guard is already paid by the complete physical alarm. -/
theorem ordinary_quiet_of_alarm {Q : Nat} {R : Type} (C : PrimitiveOracle)
    (iv : Digest32) (program : Program R) (remaining : Nat) (cap : remaining ≤ Q)
    (counted : Counts remaining program) (roots : PublicMerkleProbability.RootPolicy)
    (quiet : PublicMerkleProbability.traceAlarm roots []
      (primitiveLog C iv program remaining counted) = false) :
    ¬ OutputCollision (PCSBCSMerkleSeedProjection.ordinaryObservations
      (Sampling.eval (PublicCompressionCouplingMixed.oracle C (WHIRRealSimulator.rawTable Q C))
        (PublicCompressionCouplingMixed.compile Q iv [] program remaining cap counted)).observations) := by
  intro bad
  have collision := PublicMerkleProbability.collision_mono
    (ordinary_subset C iv program remaining cap counted) bad
  have clean := PublicMerkleProbability.traceAlarm_clean C roots [] _
    (by intro n d h; cases h) (primitiveLog_authentic C iv program remaining counted)
    (by rintro ⟨a,b,d,h,_⟩; cases h) quiet
  apply clean
  apply PublicMerkleProbability.collision_mono _ collision
  exact fun _ member => List.mem_append_left _ (List.mem_reverse.mpr member)

/-- All attacker and verifier source prefixes, not just the final prefix, have
actual frozen root tables outside that SAME complete physical event. -/
theorem source_prefixes_of_alarm {Q : Nat} {R : Type} (registry : Public)
    (C : PrimitiveOracle) (program : Program R) (remaining : Nat)
    (cap : remaining ≤ Q) (counted : Counts remaining program)
    (roots : PublicMerkleProbability.RootPolicy)
    (quiet : PublicMerkleProbability.traceAlarm roots []
      (primitiveLog C registry.iv program remaining counted) = false) :
    let full := PCSBCSMerkleSeedProjection.ordinaryObservations
      (Sampling.eval (PublicCompressionCouplingMixed.oracle C (WHIRRealSimulator.rawTable Q C))
        (PublicCompressionCouplingMixed.compile Q registry.iv [] program remaining cap counted)).observations
    SourcePrefixes registry C (WHIRRealSimulator.rawTable Q C) full [] []
      program remaining cap counted := by
  exact initial_source_prefixes registry C (WHIRRealSimulator.rawTable Q C) program remaining
    cap counted (ordinary_quiet_of_alarm C registry.iv program remaining cap counted roots quiet)

#print axioms ordinary_subset
#print axioms ordinary_quiet_of_alarm
#print axioms source_prefixes_of_alarm
end Whir.AnchoredMixedAttackerPrefixObserver
