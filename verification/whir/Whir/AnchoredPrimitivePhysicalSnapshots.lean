import Whir.WHIRPhysicalSnapshots

/-! The tracked physical registry only observes primitive replies and root
announcements. Construction challenges do not update it, so its invariant does
not require independently sampled ideal challenges to equal a deterministic
compression evaluation. This does not yet identify PCS first-root captures. -/
set_option autoImplicit false
namespace Whir.AnchoredPrimitivePhysicalSnapshots
open FiatShamirGame DuplexModeGame WHIRSourceChronology WHIRSourceObserver
open WHIRPhysicalSnapshots CausalBindingState

variable {cap : Nat}

def PrimitiveEvent (C : PrimitiveOracle) : Event cap → Prop
  | .answer (.primitive _ node) answer => answer = C node
  | _ => True

theorem step_invariant (C : PrimitiveOracle)
    (state next : CausalBindingState.State cap) (event : Event cap)
    (old : Invariant C state) (correct : PrimitiveEvent C event)
    (stepped : step state event = .ok next) : Invariant C next := by
  cases event with
  | answer query value =>
    cases query with
    | primitive purpose node =>
      change value = C node at correct
      subst value
      cases stepped
      exact observePublic_invariant C state node old
    | construction coordinate valid => cases stepped; exact old
  | commit root => cases stepped; exact registerRoot_invariant C state root old
  | claims profile entry request =>
    unfold step at stepped
    cases known : MerkleTransport.Commitments.lookup request.root state.registry <;>
      simp only [known] at stepped
    · cases stepped
    · cases stepped; exact old

/-- Actual tracked execution, including bookkeeping errors, preserves frozen
snapshot authentication when its primitive replies are consistent. -/
theorem replayTracked_invariant (C : PrimitiveOracle)
    (state : CausalBindingState.State cap) (events : List (Event cap))
    (old : Invariant C state) (correct : ∀ e ∈ events, PrimitiveEvent C e) :
    Invariant C (replayTracked state events) := by
  induction events generalizing state with
  | nil => exact old
  | cons event rest ih =>
    unfold replayTracked
    cases progress : step state event with
    | error root =>
      exact ih _ (error_invariant C state (state.sourceError.or (some root)) old)
        (fun e member => correct e (List.mem_cons_of_mem _ member))
    | ok next =>
      exact ih next (step_invariant C state next event old (correct event (by simp)) progress)
        (fun e member => correct e (List.mem_cons_of_mem _ member))

theorem replayTracked_empty_invariant (C : PrimitiveOracle)
    (events : List (Event cap)) (correct : ∀ e ∈ events, PrimitiveEvent C e) :
    Invariant C (replayTracked (empty cap) events) :=
  replayTracked_invariant C _ events (empty_invariant C cap) correct

#print axioms step_invariant
#print axioms replayTracked_invariant
#print axioms replayTracked_empty_invariant
end Whir.AnchoredPrimitivePhysicalSnapshots
