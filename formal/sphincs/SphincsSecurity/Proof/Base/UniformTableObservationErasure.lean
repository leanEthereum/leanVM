import SphincsSecurity.Proof.Base.UniformTableObservation
namespace SphincsSecurity.Concrete.UniformTableObservation

open _root_.OracleComp OracleSpec UniformTableCompletion RetainedObservation
set_option backward.isDefEq.respectTransparency false

variable {Coordinate Value AuxIndex : Type} [Fintype Coordinate] [DecidableEq Coordinate] [DecidableEq Value]
  {auxSpec : OracleSpec AuxIndex}

noncomputable def fixedImpl (auxiliary : QueryImpl auxSpec SPMF) (table : Coordinate → Value) :
    QueryImpl (auxSpec + TableSpec Coordinate Value) SPMF
  | .inl input => auxiliary input
  | .inr coordinate => pure (table coordinate)

omit [Fintype Coordinate] [DecidableEq Value] in
theorem observedRun_forget {Result : Type} (auxiliary : QueryImpl auxSpec SPMF) (table : Coordinate → Value)
    (computation : OracleComp (auxSpec + TableSpec Coordinate Value) Result) (allowed : Coordinate → Finset Value) :
    Prod.fst <$> observedRun auxiliary table computation allowed = simulateQ (fixedImpl auxiliary table) computation := by
  induction computation using OracleComp.inductionOn generalizing allowed with
  | pure value => simp only [observedRun_pure, map_pure, simulateQ_pure]
  | query_bind input next ih =>
      cases input <;> simp only [observedRun_query_bind, observedImpl, fixedImpl, StateT.run_mk,
        bind_map_left, pure_bind, map_bind, ih, simulateQ_bind, simulateQ_spec_query]

omit [Fintype Coordinate] [DecidableEq Value] in
theorem lazyRun_nonempty {Result : Type} (auxiliary : QueryImpl auxSpec SPMF)
    (computation : OracleComp (auxSpec + TableSpec Coordinate Value) Result) (allowed : Coordinate → Finset Value)
    (ha : ∀ coordinate, (allowed coordinate).Nonempty)
    (result : Result × (Coordinate → Finset Value)) (hr : lazyRun auxiliary computation allowed result ≠ 0) :
    ∀ coordinate, (result.2 coordinate).Nonempty := by
  induction computation using OracleComp.inductionOn generalizing allowed result with
  | pure value =>
      simp only [lazyRun_pure, ne_eq, SPMF.pure_apply_eq_zero_iff, not_not] at hr
      subst result
      exact ha
  | query_bind input next ih =>
      cases input with
      | inl input =>
          simp only [lazyRun_query_bind, lazyImpl, StateT.run_mk, bind_map_left] at hr
          obtain ⟨answer, _, hnext⟩ := (bind_nonzero _ _ _).mp hr
          exact ih answer allowed ha result hnext
      | inr coordinate =>
          simp only [lazyRun_query_bind, lazyImpl, StateT.run_mk, bind_map_left] at hr
          obtain ⟨answer, _, hnext⟩ := (bind_nonzero _ _ _).mp hr
          exact ih answer _ (discloseTableValue_nonempty allowed ha coordinate answer) result hnext

theorem run_erasure {Result : Type} (auxiliary : QueryImpl auxSpec SPMF)
    (computation : OracleComp (auxSpec + TableSpec Coordinate Value) Result) (allowed : Coordinate → Finset Value)
    (ha : ∀ coordinate, (allowed coordinate).Nonempty) :
    (complete allowed >>= fun table => observedRun auxiliary table computation allowed) = lazyRun auxiliary computation allowed := by
  have h := congrArg (fun law : SPMF ((Coordinate → Value) × (Result × (Coordinate → Finset Value))) => Prod.snd <$> law)
    (run_posterior auxiliary computation allowed)
  simp only [← bind_pure_comp, bind_assoc, pure_bind, bind_pure] at h
  rw [h]
  have hfinish : (lazyRun auxiliary computation allowed >>= fun result =>
      (fun _ : Coordinate → Value => result) <$> complete result.2) =
        (lazyRun auxiliary computation allowed >>= fun result => pure result) := by
    apply RetainedObservation.bind_congr
    intro result hr
    rw [complete_of_nonempty _ (lazyRun_nonempty auxiliary computation allowed ha result hr), ← bind_pure_comp]
    exact lift_bind_const _ _
  simpa only [← bind_pure_comp, bind_pure] using hfinish

theorem run_marginal {Result : Type} (auxiliary : QueryImpl auxSpec SPMF)
    (computation : OracleComp (auxSpec + TableSpec Coordinate Value) Result) (allowed : Coordinate → Finset Value)
    (ha : ∀ coordinate, (allowed coordinate).Nonempty) :
    (complete allowed >>= fun table => simulateQ (fixedImpl auxiliary table) computation) =
      Prod.fst <$> lazyRun auxiliary computation allowed := by
  rw [← run_erasure auxiliary computation allowed ha, map_bind]
  simp only [observedRun_forget]

end SphincsSecurity.Concrete.UniformTableObservation
