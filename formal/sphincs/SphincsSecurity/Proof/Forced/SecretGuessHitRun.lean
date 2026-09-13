import SphincsSecurity.Proof.Forced.SecretGuessForceBound
namespace SphincsSecurity.Concrete.SecretGuessObservation

open _root_.OracleComp OracleSpec ENNReal
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

variable {Coordinate Value Memory AuxIndex : Type} {auxSpec : OracleSpec AuxIndex}
  [Fintype Coordinate] [DecidableEq Coordinate] [DecidableEq Value]

theorem lazyRun_probes_mono {Result : Type} (environment : Environment auxSpec Coordinate Value Memory)
    (computation : OracleComp (World auxSpec Coordinate Value) Result) (state : State Coordinate Value Memory)
    (result : Result × State Coordinate Value Memory) (hr : lazyRun environment computation state result ≠ 0) :
    state.probes ≤ result.2.probes := by
  apply lazyRun_preserves environment (fun next => state.probes ≤ next.probes) _ computation state le_rfl result hr
  intro middle hm input next hn
  rw [lazyImpl_probes environment middle input next hn]
  exact hm.trans (Nat.le_add_right _ _)

theorem hitImpl_eq_lazy (environment : Environment auxSpec Coordinate Value Memory) (slot : Nat)
    (state : State Coordinate Value Memory) (hne : state.probes ≠ slot) (input : (World auxSpec Coordinate Value).Domain) :
    (hitImpl environment slot input).run state = (lazyImpl environment input).run state := by
  cases input with
  | inl input => rfl
  | inr input =>
      cases input with
      | inl probe =>
          rcases probe with ⟨coordinate, candidate⟩
          simp only [hitImpl, lazyImpl, StateT.run_mk, hitTrial, if_neg hne]
      | inr coordinate => rfl

theorem hitImplRun_after {Result : Type} (environment : Environment auxSpec Coordinate Value Memory) (slot : Nat)
    (computation : OracleComp (World auxSpec Coordinate Value) Result) (state : State Coordinate Value Memory)
    (hslot : slot < state.probes) : runWith (hitImpl environment slot) computation state = lazyRun environment computation state := by
  induction computation using OracleComp.inductionOn generalizing state with
  | pure value => simp only [lazyRun, runWith_pure]
  | query_bind input next ih =>
      rw [runWith_query_bind, lazyRun, runWith_query_bind, hitImpl_eq_lazy environment slot state (Nat.ne_of_gt hslot)]
      apply RetainedObservation.bind_congr
      intro middle hm
      have hp := lazyImpl_probes environment state input middle hm
      apply ih middle.1 middle.2
      rw [hp]
      exact hslot.trans_le (Nat.le_add_right _ _)

theorem hitRun_apply {Result : Type} (environment : Environment auxSpec Coordinate Value Memory) (slot : Nat)
    (computation : OracleComp (World auxSpec Coordinate Value) Result) (state : State Coordinate Value Memory)
    (result : Result × State Coordinate Value Memory) : hitRun environment slot computation state result =
      if slot < result.2.probes then runWith (hitImpl environment slot) computation state result else 0 := by
  rw [hitRun, SPMF.bind_apply_eq_tsum, tsum_eq_single result]
  · split <;> simp only [SPMF.pure_apply_self, SPMF.failure_apply, mul_one, mul_zero]
  · intro other hother
    split <;> simp only [SPMF.pure_apply, if_neg (Ne.symm hother), SPMF.failure_apply, mul_zero]

theorem hitRun_after {Result : Type} (environment : Environment auxSpec Coordinate Value Memory) (slot : Nat)
    (computation : OracleComp (World auxSpec Coordinate Value) Result) (state : State Coordinate Value Memory)
    (hslot : slot < state.probes) : hitRun environment slot computation state = lazyRun environment computation state := by
  apply SPMF.ext
  intro result
  rw [hitRun_apply, hitImplRun_after environment slot computation state hslot]
  by_cases hp : slot < result.2.probes
  · exact if_pos hp
  · rw [if_neg hp]
    symm
    by_contra hr
    exact hp (hslot.trans_le (lazyRun_probes_mono environment computation state result hr))

theorem hitRun_query_bind {Result : Type} (environment : Environment auxSpec Coordinate Value Memory) (slot : Nat)
    (input : (World auxSpec Coordinate Value).Domain)
    (next : (World auxSpec Coordinate Value).Range input → OracleComp (World auxSpec Coordinate Value) Result)
    (state : State Coordinate Value Memory) :
    hitRun environment slot (liftM ((World auxSpec Coordinate Value).query input) >>= next) state =
      ((hitImpl environment slot input).run state >>= fun middle => hitRun environment slot (next middle.1) middle.2) := by
  simp only [hitRun, runWith_query_bind, bind_assoc]

theorem hitRun_probe_at {Result : Type} (environment : Environment auxSpec Coordinate Value Memory)
    (coordinate : Coordinate) (candidate : Value)
    (next : Bool → OracleComp (World auxSpec Coordinate Value) Result) (state : State Coordinate Value Memory) :
    hitRun environment state.probes
      (liftM ((World auxSpec Coordinate Value).query (.inr (.inl (coordinate, candidate)))) >>= next) state =
      (trial state.allowed coordinate candidate >>= fun hit =>
        if hit = true ∧ coordinate ∉ state.retired then lazyRun environment (next hit) (afterTrial environment state coordinate candidate hit)
        else failure) := by
  rw [hitRun_query_bind]
  simp only [hitImpl, StateT.run_mk, bind_map_left, hitTrial, ite_true, bind_assoc]
  apply congrArg (trial state.allowed coordinate candidate >>= ·)
  funext hit
  by_cases hh : hit = true ∧ coordinate ∉ state.retired
  · rw [if_pos hh, pure_bind, hitRun_after environment state.probes _ _ (Nat.lt_succ_self _)]
    rw [if_pos hh]
  · simp only [if_neg hh, failure_bind]

theorem hitRun_probe_other {Result : Type} (environment : Environment auxSpec Coordinate Value Memory) (slot : Nat)
    (coordinate : Coordinate) (candidate : Value)
    (next : Bool → OracleComp (World auxSpec Coordinate Value) Result) (state : State Coordinate Value Memory)
    (hne : state.probes ≠ slot) :
    hitRun environment slot
      (liftM ((World auxSpec Coordinate Value).query (.inr (.inl (coordinate, candidate)))) >>= next) state =
      (trial state.allowed coordinate candidate >>= fun hit => hitRun environment slot (next hit) (afterTrial environment state coordinate candidate hit)) := by
  rw [hitRun_query_bind, hitImpl_eq_lazy environment slot state hne]
  simp only [lazyImpl, StateT.run_mk, bind_map_left]
  rfl

end SphincsSecurity.Concrete.SecretGuessObservation
