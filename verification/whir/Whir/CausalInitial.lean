import Whir.InitialSoundness
import Whir.CausalProbability
import Whir.CausalExecution

/-! Initial batching draws its fresh scalar after the commitment-fixed base-field
list and all public claims. Later messages do not enter this event. -/
namespace Whir.CausalInitial
open Concrete Protocol CausalGame CausalProbability ParameterBounds GroupedChallenges

/-- The bad set is fixed by the commitment and public claims, before the initial scalar. -/
def Event (input : Public) (tape : Tape input.config) : Prop :=
  tape.1 ∈ InitialBatching.candidateEscape
    (InitialCandidates.extensionCandidates input.config input.lanes input.root) input.claims

open Classical in
theorem event_bound (p : Profile) (lanes : Nat) (root : BaseOracle) (claims : Array Claim)
    (lane_bound : lanes ≤ 2 ^ (config p).folds[0]!)
    (shape : ∀ j : Fin claims.size, claims[j].weight.size = 2 ^ (config p).logN) :
    Soundness.uniformProb (Finset.univ.filter (Event ⟨config p, lanes, root, claims⟩)) ≤
      initialBatch (config p) (estimates (config p)) claims.size := by
  classical
  apply fiber_event_bound Coordinate.initial
  intro rest
  have coordinate (x : E) : (set Coordinate.initial rest.val x).1 = x :=
    get_set Coordinate.initial rest.val x
  have event : (Finset.univ.filter fun x : E =>
      Event ⟨config p, lanes, root, claims⟩ (set Coordinate.initial rest.val x)) =
      InitialBatching.candidateEscape (InitialCandidates.extensionCandidates (config p) lanes root) claims := by
    have same : (Finset.univ.filter fun x : E =>
        Event ⟨config p, lanes, root, claims⟩ (set Coordinate.initial rest.val x)) =
        (Finset.univ.filter fun x : E => x ∈ InitialBatching.candidateEscape
          (InitialCandidates.extensionCandidates (config p) lanes root) claims) := by
      apply Finset.filter_congr
      intro x _
      simp only [Event, coordinate]
    rw [same, Finset.filter_mem_eq_inter, Finset.univ_inter]
  rw [event]
  have bounded := InitialSoundness.initial_escape_probability p lanes root lane_bound claims shape
  have envelope : ((claims.size - 1 : Nat) : ℚ) / 2 ^ 160 =
      initialBatch (config p) (estimates (config p)) claims.size := by
    unfold initialBatch
    rw [dite_eq_left (production_config_valid p).2.1]
    simp only [estimates, fieldSize, Nat.cast_pow, Nat.cast_ofNat]
    ring
  exact bounded.trans_eq envelope

/-- Any replacement of a later coordinate preserves the initial event exactly. -/
theorem event_set (input : Public) (tape : Tape input.config) (q : Coordinate input.config)
    (x : Sample q) (later : q ≠ .initial) : Event input (set q tape x) ↔ Event input tape := by
  have same : (set q tape x).1 = tape.1 := get_set_ne q .initial tape x (Ne.symm later)
  simp only [Event, same]

end Whir.CausalInitial
