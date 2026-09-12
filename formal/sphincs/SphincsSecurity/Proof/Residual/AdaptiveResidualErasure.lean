import SphincsSecurity.Proof.Base.Prelude
import SphincsSecurity.Proof.Residual.AdaptiveResidualLabels
namespace SphincsSecurity.Concrete.AdaptiveResidualLabels

open _root_.OracleComp OracleSpec HiddenLabelObservation UniformTableCompletion RetainedObservation ResidualTableCompletion
set_option backward.isDefEq.respectTransparency false

variable {Coordinate Cell Memory AuxIndex : Type} {auxSpec : OracleSpec AuxIndex}
  [Fintype Coordinate] [DecidableEq Coordinate] [Fintype Cell] [DecidableEq Cell]

omit [Fintype Cell] in
theorem lazyRun_nonempty {Result : Type} (environment : Environment auxSpec Coordinate Cell Memory)
    (computation : OracleComp (World auxSpec Coordinate Cell) Result) (state : State Coordinate Cell Memory)
    (ha : ∀ coordinate, (state.candidates coordinate).Nonempty)
    (result : Option Result × State Coordinate Cell Memory) (h : lazyRun environment computation state result ≠ 0) :
    ∀ coordinate, (result.2.candidates coordinate).Nonempty := by
  induction computation using OracleComp.inductionOn generalizing state result with
  | pure value =>
      simp only [lazyRun, runWith_pure, ne_eq, SPMF.pure_apply_eq_zero_iff, not_not] at h
      subst result
      exact ha
  | query_bind input next ih =>
      cases input with
      | inl input =>
          simp only [lazyRun, runWith_query_bind, lazyImpl, OptionT.run_mk, StateT.run_mk,
            bind_assoc, pure_bind] at h
          obtain ⟨⟨answer, memory⟩, _, hnext⟩ := (bind_nonzero _ _ _).mp h
          cases answer with
          | none =>
              simp only [Option.elim_none, ne_eq, SPMF.pure_apply_eq_zero_iff, not_not] at hnext
              subst result
              exact ha
          | some answer => exact ih answer { state with memory := memory } ha result hnext
      | inr input =>
          cases input with
          | read input =>
              simp only [lazyRun, runWith_query_bind, lazyImpl, OptionT.run_mk, StateT.run_mk,
                bind_assoc, pure_bind, Option.elim_some] at h
              obtain ⟨answer, _, hnext⟩ := (bind_nonzero _ _ _).mp h
              exact ih answer (readState environment state input answer) ha result hnext
          | probe input test =>
              cases hcache : state.rows input with
              | some answer =>
                  simp only [lazyRun, runWith_query_bind, lazyImpl, OptionT.run_mk, StateT.run_mk,
                    hcache, pure_bind, Option.elim_some] at h
                  exact ih answer (readState environment state input answer) ha result h
              | none =>
                  simp only [lazyRun, runWith_query_bind, lazyImpl, OptionT.run_mk, StateT.run_mk,
                    hcache, observe_bind, pure_bind, Option.elim_none, Option.elim_some] at h
                  rcases (observe_nonzero _ _ _ _).mp h with ⟨_, hstop⟩ | ⟨answer, hanswer, hnext⟩
                  · simp only [ne_eq, SPMF.pure_apply_eq_zero_iff, not_not] at hstop
                    subst result
                    exact ha
                  · exact ih answer (probeState environment state input test answer)
                      (lazyResponse_nonempty state.candidates test answer hanswer) result hnext
          | disclose coordinate =>
              simp only [lazyRun, runWith_query_bind, lazyImpl, OptionT.run_mk, StateT.run_mk,
                bind_assoc, pure_bind, Option.elim_some] at h
              obtain ⟨value, _, hnext⟩ := (bind_nonzero _ _ _).mp h
              exact ih value (disclosedState environment state coordinate value)
                (discloseTableValue_nonempty state.candidates ha coordinate value) result hnext

def erase {Result : Type}
    (result : Option ((Coordinate → Digest) × (Cell → HashOutput) × Result) × State Coordinate Cell Memory) :
    Option Result × State Coordinate Cell Memory := (result.1.map (fun data => data.2.2), result.2)

omit [Fintype Coordinate] [DecidableEq Coordinate] [Fintype Cell] [DecidableEq Cell] in
theorem erase_retain {Result : Type} (labels : Coordinate → Digest) (table : Cell → HashOutput)
    (result : Option Result × State Coordinate Cell Memory) : erase (retain labels table result) = result := by
  rcases result with ⟨value, state⟩
  cases value <;> rfl

theorem erase_finish {Result : Type} (result : Option Result × State Coordinate Cell Memory)
    (ha : ∀ coordinate, (result.2.candidates coordinate).Nonempty) : erase <$> finish result = pure result := by
  rcases result with ⟨value, state⟩
  cases value with
  | none => simp only [finish, map_pure, erase, Option.map_none]
  | some value =>
      simp only [finish, map_bind, map_pure, erase, Option.map_some, completeRows_bind_const]
      rw [complete_of_nonempty state.candidates ha, lift_bind_const]

theorem run_erasure {Result : Type} (environment : Environment auxSpec Coordinate Cell Memory)
    (computation : OracleComp (World auxSpec Coordinate Cell) Result) (state : State Coordinate Cell Memory)
    (ha : ∀ coordinate, (state.candidates coordinate).Nonempty) :
    (complete state.candidates >>= fun labels => completeRows state.rows >>= fun table =>
      observedRun environment labels table computation state) = lazyRun environment computation state := by
  have h := congrArg (fun law => erase <$> law) (run_posterior environment computation state ha)
  simp only [map_bind, ← comp_map, Function.comp_def, erase_retain, id_map'] at h
  calc
    _ = lazyRun environment computation state >>= fun result => erase <$> finish result := h
    _ = lazyRun environment computation state >>= pure := by
      apply RetainedObservation.bind_congr
      intro result hresult
      exact erase_finish result (lazyRun_nonempty environment computation state ha result hresult)
    _ = _ := bind_pure _

omit [Fintype Coordinate] [Fintype Cell] in
theorem observedRun_bind_const {Result Other : Type} (environment : Environment auxSpec Coordinate Cell Memory)
    (labels : Coordinate → Digest) (table : Cell → HashOutput)
    (computation : OracleComp (World auxSpec Coordinate Cell) Result) (state : State Coordinate Cell Memory)
    (after : SPMF Other) : (observedRun environment labels table computation state >>= fun _ => after) = after := by
  induction computation using OracleComp.inductionOn generalizing state with
  | pure result => simp only [observedRun, runWith_pure, pure_bind]
  | query_bind input next ih =>
      cases input with
      | inl input =>
          simp only [observedRun, runWith_query_bind, observedImpl, OptionT.run_mk, StateT.run_mk,
            bind_assoc, pure_bind]
          dsimp only [OracleSpec.Range, World, OracleSpec.add_apply_inl]
          have hnext (result : Option (auxSpec.Range input) × Memory) :
              (result.1.elim (pure (none, { state with memory := result.2 }))
                (fun answer => runWith (observedImpl environment labels table) (next answer)
                  { state with memory := result.2 }) >>= fun _ => after) = after := by
            rcases result with ⟨answer, memory⟩
            cases answer with
            | none => exact pure_bind _ _
            | some answer => exact ih answer { state with memory := memory }
          simp_rw [hnext]
          exact lift_bind_const _ _
      | inr input =>
          cases input with
          | read input =>
              simp only [observedRun, runWith_query_bind, observedImpl, OptionT.run_mk, StateT.run_mk, pure_bind, Option.elim_some]
              exact ih (table input) (readState environment state input (table input))
          | probe input test =>
              cases hcache : state.rows input with
              | some answer =>
                  simp only [observedRun, runWith_query_bind, observedImpl, OptionT.run_mk, StateT.run_mk, hcache, pure_bind, Option.elim_some]
                  exact ih answer (readState environment state input answer)
              | none =>
                  simp only [observedRun, runWith_query_bind, observedImpl, OptionT.run_mk, StateT.run_mk, hcache]
                  split
                  · simp only [pure_bind, Option.elim_some]
                    exact ih (table input) (probeState environment state input test (table input))
                  · simp only [pure_bind, Option.elim_none]
          | disclose coordinate =>
              simp only [observedRun, runWith_query_bind, observedImpl, OptionT.run_mk, StateT.run_mk, pure_bind, Option.elim_some]
              exact ih (labels coordinate) (disclosedState environment state coordinate (labels coordinate))

theorem lazyRun_bind_const {Result Other : Type} (environment : Environment auxSpec Coordinate Cell Memory)
    (computation : OracleComp (World auxSpec Coordinate Cell) Result) (state : State Coordinate Cell Memory)
    (ha : ∀ coordinate, (state.candidates coordinate).Nonempty) (after : SPMF Other) :
    (lazyRun environment computation state >>= fun _ => after) = after := by
  rw [← run_erasure environment computation state ha]
  simp only [bind_assoc, observedRun_bind_const, completeRows_bind_const]
  rw [complete_of_nonempty state.candidates ha, lift_bind_const]

end SphincsSecurity.Concrete.AdaptiveResidualLabels
