import Whir.DuplexPublicSimulator
import Whir.AnchoredPrimitivePhysicalSnapshots
import Whir.WHIRSourceResolver

/-! The observed primitive table extends the actual fallback seed on unobserved
inputs. This construction makes no uniformity claim for the extension and does
not identify independent construction answers with compression evaluations. -/
set_option autoImplicit false
namespace Whir.PCSBCSObservedPrimitiveExtension
open Concrete FiatShamirGame DuplexFraming DuplexModeGame DuplexPublicSimulator

def extension (seed : Seed) (log : PublicLog) : Node → Digest32 :=
  fun input => match lookup log input with
    | some answer => answer
    | none => seed input

theorem extension_of_mem (seed : Seed) {log : PublicLog}
    (functional : Functional log) {input : Node} {answer : Digest32}
    (member : (input,answer) ∈ log) : extension seed log input = answer := by
  obtain ⟨value,found⟩ := lookup_exists member
  have same := functional input value answer (lookup_mem found) member
  simp [extension,found,same]

theorem primitive_in_finalLog (log : PublicLog) (observations : List Observation)
    (purpose : Purpose) (input : Node) (answer : Digest32)
    (member : (⟨.primitive purpose input,answer⟩ : Observation) ∈ observations) :
    (input,answer) ∈ finalLog log observations := by
  induction observations generalizing log with
  | nil => simp at member
  | cons observation rest ih =>
    rcases observation with ⟨query,value⟩
    rcases List.mem_cons.mp member with same | later
    · cases same
      exact finalLog_contains _ rest _ (List.mem_cons_self)
    · cases query with
      | primitive purpose node => exact ih _ later
      | construction coordinate valid => exact ih _ later

theorem finalLog_consistent (seed : Seed) (observations : List Observation)
    (functional : Functional (finalLog [] observations)) :
    ∀ observation ∈ observations,
      match observation.query with
      | .primitive _ input =>
        observation.answer = extension seed (finalLog [] observations) input
      | _ => True := by
  intro observation member
  rcases observation with ⟨query,answer⟩
  cases query with
  | primitive purpose input =>
    exact (extension_of_mem seed functional
      (primitive_in_finalLog [] observations purpose input answer member)).symm
  | construction coordinate valid => trivial

theorem answer_in_observations {cap : Nat} (events : List (WHIRSourceChronology.Event cap))
    (query : Query) (answer : Digest32)
    (member : WHIRSourceChronology.Event.answer query answer ∈ events) :
    (⟨query,answer⟩ : Observation) ∈ WHIRSourceChronology.observations events := by
  induction events with
  | nil => simp at member
  | cons event rest ih =>
    rcases List.mem_cons.mp member with same | later
    · cases same
      exact List.mem_cons_self
    · cases event with
      | answer query value => exact List.mem_cons_of_mem _ (ih later)
      | commit root => exact ih later
      | claims profile entry request => exact ih later

/-- Every actual ideal source execution has its historical physical registry
invariant for the observed primitive extension. No consistency certificate for
the adversary's nonordinary primitive queries or construction replies is assumed.
The extension need not be uniform; this is not a Merkle security bound. -/
theorem ideal_snapshot {Q cap : Nat} {R : Type} (seed : Seed)
    (ro : RawKey Q → Digest32) (iv : Digest32)
    (source : WHIRSourceChronology.Source cap R) (remaining : Nat)
    (limit : remaining ≤ Q) (counted : WHIRSourceChronology.Counts remaining source) :
    let execution := runIdeal (simulator Q) ro iv ((simulator Q).initial seed)
      (WHIRSourceChronology.compile source) remaining limit
      ((WHIRSourceChronology.compile_counted source remaining).mpr counted)
    WHIRPhysicalSnapshots.Invariant
      (extension seed (finalLog [] execution.view.observations))
      (WHIRSourceObserver.replayTracked (CausalBindingState.empty cap)
        execution.view.result.events) := by
  let execution := runIdeal (simulator Q) ro iv ((simulator Q).initial seed)
    (WHIRSourceChronology.compile source) remaining limit
    ((WHIRSourceChronology.compile_counted source remaining).mpr counted)
  change WHIRPhysicalSnapshots.Invariant
    (extension seed (finalLog [] execution.view.observations))
    (WHIRSourceObserver.replayTracked (CausalBindingState.empty cap) execution.view.result.events)
  apply AnchoredPrimitivePhysicalSnapshots.replayTracked_empty_invariant
  intro event member
  cases event with
  | answer query answer =>
    cases query with
    | primitive purpose input =>
      have observed : (⟨.primitive purpose input,answer⟩ : Observation) ∈
          execution.view.observations := by
        rw [← WHIRSourceResolver.ideal_source_trace (simulator Q) ro iv
          ((simulator Q).initial seed) source remaining limit counted]
        exact answer_in_observations _ _ _ member
      exact finalLog_consistent seed _ (finalLog_functional ro iv
        ((simulator Q).initial seed) _ remaining limit _
        (by simp [simulator,Functional])) _ observed
    | construction coordinate valid => trivial
  | commit root => trivial
  | claims profile entry request => trivial

#print axioms extension_of_mem
#print axioms primitive_in_finalLog
#print axioms finalLog_consistent
#print axioms answer_in_observations
#print axioms ideal_snapshot
end Whir.PCSBCSObservedPrimitiveExtension
