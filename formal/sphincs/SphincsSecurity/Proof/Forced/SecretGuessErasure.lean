import SphincsSecurity.Proof.Forced.SecretGuessObservation
namespace SphincsSecurity.Concrete.SecretGuessObservation

open _root_.OracleComp OracleSpec UniformTableCompletion
set_option backward.isDefEq.respectTransparency false

variable {Coordinate Value AuxIndex : Type} {auxSpec : OracleSpec AuxIndex}
  [Fintype Coordinate] [DecidableEq Coordinate] [DecidableEq Value]

noncomputable def fixedAnswers (auxiliary : QueryImpl auxSpec ProbComp) (labels : Coordinate → Value) :
    QueryImpl (World auxSpec Coordinate Value) ProbComp
  | .inl input => auxiliary input
  | .inr (.inl (coordinate, candidate)) => pure (decide (labels coordinate = candidate))
  | .inr (.inr coordinate) => pure (labels coordinate)

noncomputable def environment (auxiliary : QueryImpl auxSpec ProbComp) : Environment auxSpec Coordinate Value PUnit where
  auxiliary _ input := (fun answer => (answer, PUnit.unit)) <$> (liftM (auxiliary input) : PMF _)
  trial _ _ _ _ := PUnit.unit
  disclosure _ _ _ := PUnit.unit

omit [Fintype Coordinate] [DecidableEq Coordinate] in
theorem fixedAnswers_disclosureSequence (auxiliary : QueryImpl auxSpec ProbComp) (labels : Coordinate → Value)
    {n : Nat} (coordinates : Fin n → Coordinate) :
    simulateQ (fixedAnswers auxiliary labels) (sequenceFin fun position => disclosure (coordinates position)) =
      pure (fun position => labels (coordinates position)) := by
  induction n with
  | zero =>
      simp only [sequenceFin, simulateQ_pure]
      congr 1
      funext position
      exact Fin.elim0 position
  | succ n ih =>
      rw [sequenceFin, simulateQ_bind]
      change (pure (labels (coordinates 0)) >>= _) = _
      rw [pure_bind, simulateQ_bind, ih]
      simp only [pure_bind, simulateQ_pure]
      congr 1
      funext position
      exact Fin.cases rfl (fun _ => rfl) position

omit [Fintype Coordinate] in
theorem fixedImpl_projection (auxiliary : QueryImpl auxSpec ProbComp) (labels : Coordinate → Value)
    (input : (World auxSpec Coordinate Value).Domain) (state : State Coordinate Value PUnit) :
    Prod.fst <$> ((fixedImpl (environment auxiliary) labels input).run state) = 𝒟[fixedAnswers auxiliary labels input] := by
  cases input with
  | inl input =>
      change Prod.fst <$> ((fun result => (result.1, { state with memory := result.2 })) <$>
        𝒟[(fun answer => (answer, PUnit.unit)) <$> (liftM (auxiliary input) : PMF _)]) = 𝒟[auxiliary input]
      simp only [evalDist_map, Functor.map_map, id_map']
      rfl
  | inr input =>
      cases input <;> simp only [fixedImpl, fixedAnswers, StateT.run_mk, map_pure, evalDist_pure]

omit [Fintype Coordinate] in
theorem fixedRun_projection {Result : Type} (auxiliary : QueryImpl auxSpec ProbComp) (labels : Coordinate → Value)
    (computation : OracleComp (World auxSpec Coordinate Value) Result) (state : State Coordinate Value PUnit) :
    Prod.fst <$> fixedRun (environment auxiliary) labels computation state =
      𝒟[simulateQ (fixedAnswers auxiliary labels) computation] := by
  induction computation using OracleComp.inductionOn generalizing state with
  | pure result => simp only [fixedRun, runWith_pure, map_pure, simulateQ_pure, evalDist_pure]
  | query_bind input next ih =>
      simp only [fixedRun, runWith_query_bind, map_bind, simulateQ_bind, simulateQ_spec_query, evalDist_bind]
      change ((fixedImpl (environment auxiliary) labels input).run state >>= fun middle =>
        Prod.fst <$> fixedRun (environment auxiliary) labels (next middle.1) middle.2) = _
      simp only [ih]
      have h := congrArg (· >>= fun answer => 𝒟[simulateQ (fixedAnswers auxiliary labels) (next answer)])
        (fixedImpl_projection auxiliary labels input state)
      rw [bind_map_left] at h
      exact h

end SphincsSecurity.Concrete.SecretGuessObservation
