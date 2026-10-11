import Whir.WHIRSourceChronology
import Whir.DuplexPublicSimulator

namespace Whir.WHIRSourceObserver
open FiatShamirGame DuplexModeGame
open WHIRSourceChronology

/-- Only the returned source trace and public observations are inspected. The current missing raw reply, and metadata derived after it, are excluded. -/
def publicEvents (Q : Nat) (iv : Digest32) (cache : RawKey Q → Option Digest32)
    (view : View (Result cap R)) : List (Event cap) :=
  beforeAnswers (DuplexPublicSimulator.publicCut Q iv cache [] view.observations).length
    view.result.events

/-- The causal experiment can rerun its fixed source from its fixed simulator coins, but stops at the first unavailable raw answer. This definition has no total-oracle argument. -/
def privateEvents (Q : Nat) (iv : Digest32) (cache : RawKey Q → Option Digest32)
    (seed : DuplexPublicSimulator.Seed) (source : Source cap R) (counted : Counts Q source) :
    List (Event cap) :=
  (recover source (DuplexPublicSimulator.runPartial cache iv
    ((DuplexPublicSimulator.simulator Q).initial seed) (compile source) Q (by omega)
      ((compile_counted source Q).mpr counted)).observations).events

theorem publicEvents_actual (Q : Nat) (iv : Digest32) (cache : RawKey Q → Option Digest32)
    (ro : RawKey Q → Digest32) (agrees : DuplexPublicSimulator.CacheAgrees cache ro)
    (seed : DuplexPublicSimulator.Seed) (source : Source cap R) (counted : Counts Q source) :
    publicEvents Q iv cache (runIdeal (DuplexPublicSimulator.simulator Q) ro iv
      ((DuplexPublicSimulator.simulator Q).initial seed) (compile source) Q (by omega)
        ((compile_counted source Q).mpr counted)).view =
      privateEvents Q iv cache seed source counted := by
  unfold publicEvents privateEvents
  have cut := DuplexPublicSimulator.publicCut_runPartial cache ro agrees iv
    ((DuplexPublicSimulator.simulator Q).initial seed) (compile source) Q (by omega)
    ((compile_counted source Q).mpr counted)
  change DuplexPublicSimulator.publicCut Q iv cache [] _ = _ at cut
  rw [cut]
  apply beforeAnswers_ideal_prefix (DuplexPublicSimulator.simulator Q) ro iv
    ((DuplexPublicSimulator.simulator Q).initial seed) source Q (by omega) counted
  obtain ⟨suffix,eq⟩ := DuplexPublicSimulator.runPartial_prefix cache ro agrees iv
    ((DuplexPublicSimulator.simulator Q).initial seed) (compile source) Q (by omega)
    ((compile_counted source Q).mpr counted)
  exact ⟨suffix,eq.symm⟩

/-- A failed commitment-order check records the first error, but does not stop observing later public compression calls. Otherwise a later root could capture a stale log even though the underlying source execution continued. Claims never install their purported family or point metadata. -/
def replayTracked (state : CausalBindingState.State cap) :
    List (Event cap) → CausalBindingState.State cap
  | [] => state
  | event :: rest =>
      match step state event with
      | .error root => replayTracked {state with sourceError := state.sourceError.or (some root)} rest
      | .ok next => replayTracked next rest

theorem replayTracked_extends (state : CausalBindingState.State cap) (events : List (Event cap)) :
    CausalBindingState.Extends state (replayTracked state events) := by
  induction events generalizing state with
  | nil => exact .refl _
  | cons event rest ih =>
      unfold replayTracked
      cases progress : step state event with
      | error root =>
          exact (show CausalBindingState.Extends state
            {state with sourceError := state.sourceError.or (some root)} from
            ⟨fun _ _ h => h,fun _ _ h => h,fun _ _ _ => rfl,
              fun _ _ _ h => h,fun _ _ _ => rfl⟩).trans (ih _)
      | ok next => exact (step_extends state next event progress).trans (ih next)

@[simp] theorem observeRecords_sourceError (state : CausalBindingState.State cap)
    (records : MerkleTransport.Commitments.Records) :
    (observeRecords state records).sourceError = state.sourceError := by
  induction records generalizing state with
  | nil => rfl
  | cons record rest ih =>
      change (observeRecords (CausalBindingState.observe state record.1 record.2) rest).sourceError = _
      rw [ih]
      unfold CausalBindingState.observe
      split <;> rfl

@[simp] theorem observePublic_sourceError (state : CausalBindingState.State cap)
    (input : DuplexFraming.Node) (answer : Digest32) :
    (observePublic state input answer).sourceError = state.sourceError := by
  simp [observePublic]

@[simp] theorem registerRoot_sourceError (state : CausalBindingState.State cap) (root : Digest32) :
    (CausalBindingState.registerRoot state root).sourceError = state.sourceError := by
  unfold CausalBindingState.registerRoot
  split <;> rfl

theorem step_sourceError (state next : CausalBindingState.State cap) (event : Event cap)
    (success : step state event = .ok next) : next.sourceError = state.sourceError := by
  cases event with
  | answer query value =>
      cases query with
      | primitive purpose input => cases success; exact observePublic_sourceError _ _ _
      | construction coordinate valid => cases success; rfl
  | commit root => cases success; exact registerRoot_sourceError _ _
  | claims profile entry request =>
      unfold step at success
      cases found : MerkleTransport.Commitments.lookup request.root state.registry with
      | none => simp [found] at success
      | some snapshot =>
          simp only [found] at success
          cases success
          rfl

/-- Observing subsequent events cannot repair or replace the first chronology error. -/
theorem replayTracked_error_sticky (state : CausalBindingState.State cap) (events : List (Event cap))
    (root : Digest32) (failed : state.sourceError = some root) :
    (replayTracked state events).sourceError = some root := by
  induction events generalizing state with
  | nil => exact failed
  | cons event rest ih =>
      unfold replayTracked
      cases progress : step state event with
      | error later => exact ih _ (by simp [failed])
      | ok next => exact ih next ((step_sourceError state next event progress).trans failed)

def publicReplay (Q : Nat) (iv : Digest32) (cache : RawKey Q → Option Digest32)
    (view : View (Result cap R)) (state : CausalBindingState.State cap) :
    CausalBindingState.State cap :=
  replayTracked state (publicEvents Q iv cache view)

def privateReplay (Q : Nat) (iv : Digest32) (cache : RawKey Q → Option Digest32)
    (seed : DuplexPublicSimulator.Seed) (source : Source cap R) (counted : Counts Q source)
    (state : CausalBindingState.State cap) : CausalBindingState.State cap :=
  replayTracked state (privateEvents Q iv cache seed source counted)

theorem publicReplay_actual (Q : Nat) (iv : Digest32) (cache : RawKey Q → Option Digest32)
    (ro : RawKey Q → Digest32) (agrees : DuplexPublicSimulator.CacheAgrees cache ro)
    (seed : DuplexPublicSimulator.Seed) (source : Source cap R) (counted : Counts Q source)
    (state : CausalBindingState.State cap) :
    publicReplay Q iv cache (runIdeal (DuplexPublicSimulator.simulator Q) ro iv
      ((DuplexPublicSimulator.simulator Q).initial seed) (compile source) Q (by omega)
        ((compile_counted source Q).mpr counted)).view state =
      privateReplay Q iv cache seed source counted state := by
  unfold publicReplay privateReplay
  rw [publicEvents_actual Q iv cache ro agrees seed source counted]

theorem publicReplay_extends (Q : Nat) (iv : Digest32) (cache : RawKey Q → Option Digest32)
    (view : View (Result cap R)) (state : CausalBindingState.State cap) :
    CausalBindingState.Extends state (publicReplay Q iv cache view state) :=
  replayTracked_extends _ _

theorem privateReplay_extends (Q : Nat) (iv : Digest32) (cache : RawKey Q → Option Digest32)
    (seed : DuplexPublicSimulator.Seed) (source : Source cap R) (counted : Counts Q source)
    (state : CausalBindingState.State cap) :
    CausalBindingState.Extends state (privateReplay Q iv cache seed source counted state) :=
  replayTracked_extends _ _

end Whir.WHIRSourceObserver
