import SphincsSecurity.Proof.Forced.SecretGuessObservation
namespace SphincsSecurity.Concrete.SecretGuessObservation

open _root_.OracleComp OracleSpec ENNReal
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

variable {Coordinate Value Memory AuxIndex : Type} {auxSpec : OracleSpec AuxIndex}
  [Fintype Coordinate] [DecidableEq Coordinate] [DecidableEq Value]

def EligibleAt (slot : Nat) (state : State Coordinate Value Memory) (coordinate : Coordinate) (candidate : Value) : Prop :=
  state.probes = slot ∧ coordinate ∉ state.retired ∧ trial state.allowed coordinate candidate true ≠ 0

noncomputable def forcedTrial (slot : Nat) (state : State Coordinate Value Memory)
    (coordinate : Coordinate) (candidate : Value) : SPMF Bool :=
  if EligibleAt slot state coordinate candidate then pure true else trial state.allowed coordinate candidate

theorem forcedTrial_nonzero (slot : Nat) (state : State Coordinate Value Memory)
    (coordinate : Coordinate) (candidate : Value) (hit : Bool)
    (hhit : forcedTrial slot state coordinate candidate hit ≠ 0) : trial state.allowed coordinate candidate hit ≠ 0 := by
  by_cases he : EligibleAt slot state coordinate candidate
  · simp only [forcedTrial, if_pos he, ne_eq, SPMF.pure_apply_eq_zero_iff, not_not] at hhit
    subst hit
    exact he.2.2
  · simpa only [forcedTrial, if_neg he] using hhit

noncomputable def forcedImpl (environment : Environment auxSpec Coordinate Value Memory) (slot : Nat) :
    QueryImpl (World auxSpec Coordinate Value) (StateT (State Coordinate Value Memory) SPMF)
  | .inl input => lazyImpl environment (.inl input)
  | .inr (.inl (coordinate, candidate)) => StateT.mk fun state =>
      (fun hit => (hit, afterTrial environment state coordinate candidate hit)) <$> forcedTrial slot state coordinate candidate
  | .inr (.inr coordinate) => lazyImpl environment (.inr (.inr coordinate))

noncomputable def forcedRun {Result : Type} (environment : Environment auxSpec Coordinate Value Memory) (slot : Nat)
    (computation : OracleComp (World auxSpec Coordinate Value) Result) (state : State Coordinate Value Memory) :=
  runWith (forcedImpl environment slot) computation state

theorem forcedImpl_nonzero (environment : Environment auxSpec Coordinate Value Memory) (slot : Nat)
    (state : State Coordinate Value Memory) (input : (World auxSpec Coordinate Value).Domain)
    (result : (World auxSpec Coordinate Value).Range input × State Coordinate Value Memory)
    (hr : (forcedImpl environment slot input).run state result ≠ 0) :
    (lazyImpl environment input).run state result ≠ 0 := by
  cases input with
  | inl input => exact hr
  | inr input =>
      cases input with
      | inl probe =>
          rcases probe with ⟨coordinate, candidate⟩
          simp only [forcedImpl, lazyImpl, StateT.run_mk, map_eq_bind_pure_comp,
            RetainedObservation.bind_nonzero] at hr ⊢
          obtain ⟨hit, hh, hr⟩ := hr
          exact ⟨hit, forcedTrial_nonzero slot state coordinate candidate hit hh, hr⟩
      | inr coordinate => exact hr

theorem forcedRun_nonzero {Result : Type} (environment : Environment auxSpec Coordinate Value Memory) (slot : Nat)
    (computation : OracleComp (World auxSpec Coordinate Value) Result) (state : State Coordinate Value Memory)
    (result : Result × State Coordinate Value Memory) (hr : forcedRun environment slot computation state result ≠ 0) :
    lazyRun environment computation state result ≠ 0 := by
  induction computation using OracleComp.inductionOn generalizing state result with
  | pure value => exact hr
  | query_bind input next ih =>
      simp only [forcedRun, lazyRun, runWith_query_bind, RetainedObservation.bind_nonzero] at hr ⊢
      obtain ⟨middle, hm, hr⟩ := hr
      exact ⟨middle, forcedImpl_nonzero environment slot state input middle hm, ih middle.1 middle.2 result hr⟩

theorem forcedImpl_probes (environment : Environment auxSpec Coordinate Value Memory) (slot : Nat)
    (state : State Coordinate Value Memory) (input : (World auxSpec Coordinate Value).Domain)
    (result : (World auxSpec Coordinate Value).Range input × State Coordinate Value Memory)
    (hr : (forcedImpl environment slot input).run state result ≠ 0) :
    result.2.probes = state.probes + probeStep input :=
  lazyImpl_probes environment state input result (forcedImpl_nonzero environment slot state input result hr)

theorem forcedRun_nonempty {Result : Type} (environment : Environment auxSpec Coordinate Value Memory) (slot : Nat)
    (computation : OracleComp (World auxSpec Coordinate Value) Result) (state : State Coordinate Value Memory)
    (ha : ∀ coordinate, (state.allowed coordinate).Nonempty) (result : Result × State Coordinate Value Memory)
    (hr : forcedRun environment slot computation state result ≠ 0) : ∀ coordinate, (result.2.allowed coordinate).Nonempty :=
  lazyRun_nonempty environment computation state ha result (forcedRun_nonzero environment slot computation state result hr)

end SphincsSecurity.Concrete.SecretGuessObservation
