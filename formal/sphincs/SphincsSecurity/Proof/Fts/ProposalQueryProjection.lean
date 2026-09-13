import SphincsSecurity.Proof.Base.Prelude
import SphincsSecurity.Proof.Fts.ProposalLengthProjection
namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal

noncomputable def pmfSumImpl {ι κ σ : Type} {leftSpec : OracleSpec ι} {rightSpec : OracleSpec κ}
    (left : QueryImpl leftSpec (StateT σ ProbComp)) (right : QueryImpl rightSpec (StateT σ ProbComp)) :
    QueryImpl (leftSpec + rightSpec) (StateT σ PMF)
  | .inl input => StateT.mk fun state => liftM ((left input).run state)
  | .inr input => StateT.mk fun state => liftM ((right input).run state)

theorem pmfSumImpl_inl {ι κ σ : Type} {leftSpec : OracleSpec ι} {rightSpec : OracleSpec κ}
    (left : QueryImpl leftSpec (StateT σ ProbComp)) (right : QueryImpl rightSpec (StateT σ ProbComp))
    (input : leftSpec.Domain) (state : σ) :
    (pmfSumImpl left right (.inl input)).run state = (liftM ((left input).run state) : PMF _) := rfl

theorem pmfSumImpl_inr {ι κ σ : Type} {leftSpec : OracleSpec ι} {rightSpec : OracleSpec κ}
    (left : QueryImpl leftSpec (StateT σ ProbComp)) (right : QueryImpl rightSpec (StateT σ ProbComp))
    (input : rightSpec.Domain) (state : σ) :
    (pmfSumImpl left right (.inr input)).run state = (liftM ((right input).run state) : PMF _) := rfl

theorem pmfSumImpl_eq_lift_add {ι κ σ : Type} {leftSpec : OracleSpec ι} {rightSpec : OracleSpec κ}
    (left : QueryImpl leftSpec (StateT σ ProbComp)) (right : QueryImpl rightSpec (StateT σ ProbComp)) :
    pmfSumImpl left right = fun input => StateT.mk fun state =>
      (liftM (((left + right) input).run state) : PMF _) := by
  funext input
  cases input <;> rfl

theorem simulateQ_liftProbCompImpl_run {ι σ α : Type} {spec : OracleSpec ι}
    (impl : QueryImpl spec (StateT σ ProbComp)) (computation : OracleComp spec α) (state : σ) :
    (simulateQ (fun input => StateT.mk fun current => (liftM ((impl input).run current) : PMF _))
      computation).run state = (liftM ((simulateQ impl computation).run state) : PMF _) := by
  induction computation using OracleComp.inductionOn generalizing state with
  | pure value =>
      simp only [simulateQ_pure, StateT.run_pure]
      exact (liftM_pure (m := ProbComp) (n := PMF) _).symm
  | query_bind input next ih =>
      simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query,
        id_map, StateT.run_bind, StateT.run_mk]
      rw [liftM_bind (m := ProbComp) (n := PMF)]
      exact congrArg (fun continuation => (liftM ((impl input).run state) : PMF _).bind continuation)
        (funext fun result => ih result.1 result.2)

noncomputable def proposalRecordImpl {ι α σ : Type} {spec : OracleSpec ι}
    {Ω : spec.Domain → Type}
    (record : (input : spec.Domain) → σ → PMF (Ω input))
    (response : (input : spec.Domain) → Ω input → spec.Range input)
    (advance : (input : spec.Domain) → σ → Nat → Ω input → σ)
    (label : (input : spec.Domain) → Ω input → α)
    (rejected : (input : spec.Domain) → σ → PMF α)
    (active : spec.Domain → σ → Bool)
    (accept : ENNReal) (hpos : accept ≠ 0) (hle : accept ≤ 1) :
    QueryImpl spec (StateT (List α × σ) PMF) :=
  fun input => StateT.mk fun state =>
    if active input state.2 then
      (recordProposalBridge (record input state.2) (rejected input state.2) accept hpos hle).map
        (fun result => (response input result.2,
          (state.1 ++ result.1 ++ [label input result.2],
            advance input state.2 (result.1.length + 1) result.2)))
    else
      (record input state.2).map fun outcome =>
        (response input outcome, (state.1, advance input state.2 0 outcome))

noncomputable def lengthRecordImpl {ι σ : Type} {spec : OracleSpec ι}
    {Ω : spec.Domain → Type}
    (record : (input : spec.Domain) → σ → PMF (Ω input))
    (response : (input : spec.Domain) → Ω input → spec.Range input)
    (advance : (input : spec.Domain) → σ → Nat → Ω input → σ)
    (active : spec.Domain → σ → Bool)
    (accept : ENNReal) (hpos : accept ≠ 0) (hle : accept ≤ 1) :
    QueryImpl spec (StateT σ PMF) :=
  fun input => StateT.mk fun state =>
    if active input state then
      (recordLengthBridge (record input state) accept hpos hle).map
        (fun result => (response input result.2, advance input state result.1 result.2))
    else
      (record input state).map fun outcome => (response input outcome, advance input state 0 outcome)

theorem proposalRecordImpl_project {ι α σ : Type} {spec : OracleSpec ι}
    {Ω : spec.Domain → Type}
    (record : (input : spec.Domain) → σ → PMF (Ω input))
    (response : (input : spec.Domain) → Ω input → spec.Range input)
    (advance : (input : spec.Domain) → σ → Nat → Ω input → σ)
    (label : (input : spec.Domain) → Ω input → α)
    (rejected : (input : spec.Domain) → σ → PMF α)
    (active : spec.Domain → σ → Bool)
    (accept : ENNReal) (hpos : accept ≠ 0) (hle : accept ≤ 1)
    (input : spec.Domain) (state : List α × σ) :
    Prod.map id Prod.snd <$>
      ((proposalRecordImpl record response advance label rejected active accept hpos hle) input).run state =
    ((lengthRecordImpl record response advance active accept hpos hle) input).run state.2 := by
  change PMF.map (Prod.map id Prod.snd) _ = _
  simp only [proposalRecordImpl, lengthRecordImpl, StateT.run_mk]
  by_cases hactive : active input state.2 = true
  · simp only [hactive, if_true]
    calc
      _ = ((recordProposalBridge (record input state.2) (rejected input state.2) accept hpos hle).map
          (fun result => (result.1.length + 1, result.2))).map
            (fun result => (response input result.2, advance input state.2 result.1 result.2)) := by
        rw [PMF.map_comp, PMF.map_comp]
        rfl
      _ = _ := by rw [recordProposalBridge_length_record]
  · simp only [hactive, Bool.false_eq_true, if_false, PMF.map_comp]
    rfl

theorem simulateQ_proposalRecordImpl_project {ι α σ β : Type} {spec : OracleSpec ι}
    {Ω : spec.Domain → Type}
    (record : (input : spec.Domain) → σ → PMF (Ω input))
    (response : (input : spec.Domain) → Ω input → spec.Range input)
    (advance : (input : spec.Domain) → σ → Nat → Ω input → σ)
    (label : (input : spec.Domain) → Ω input → α)
    (rejected : (input : spec.Domain) → σ → PMF α)
    (active : spec.Domain → σ → Bool)
    (accept : ENNReal) (hpos : accept ≠ 0) (hle : accept ≤ 1)
    (computation : OracleComp spec β) (state : List α × σ) :
    Prod.map id Prod.snd <$>
      (simulateQ (proposalRecordImpl record response advance label rejected active accept hpos hle)
        computation).run state =
    (simulateQ (lengthRecordImpl record response advance active accept hpos hle)
      computation).run state.2 :=
  map_run_simulateQ_eq_of_query_map_eq _ _ Prod.snd
    (proposalRecordImpl_project record response advance label rejected active accept hpos hle)
    computation state

theorem lengthRecordImpl_project {ι σ τ : Type} {spec : OracleSpec ι}
    {Ω : spec.Domain → Type}
    (record : (input : spec.Domain) → σ → PMF (Ω input))
    (response : (input : spec.Domain) → Ω input → spec.Range input)
    (advance : (input : spec.Domain) → σ → Nat → Ω input → σ)
    (active : spec.Domain → σ → Bool)
    (accept : ENNReal) (hpos : accept ≠ 0) (hle : accept ≤ 1)
    (base : QueryImpl spec (StateT τ PMF)) (project : σ → τ)
    (next : (input : spec.Domain) → σ → Ω input → τ)
    (hnext : ∀ input state length outcome, project (advance input state length outcome) = next input state outcome)
    (hrecord : ∀ input state, (record input state).map
      (fun outcome => (response input outcome, next input state outcome)) = (base input).run (project state))
    (input : spec.Domain) (state : σ) :
    Prod.map id project <$> ((lengthRecordImpl record response advance active accept hpos hle) input).run state =
      (base input).run (project state) := by
  change PMF.map (Prod.map id project) _ = _
  simp only [lengthRecordImpl, StateT.run_mk]
  by_cases hactive : active input state = true
  · simp only [hactive, if_true, PMF.map_comp, Function.comp_def, Prod.map, id_eq, hnext]
    calc
      _ = ((recordLengthBridge (record input state) accept hpos hle).map Prod.snd).map
          (fun outcome => (response input outcome, next input state outcome)) := by
        rw [PMF.map_comp]
        rfl
      _ = _ := by rw [recordLengthBridge_record, hrecord]
  · simpa only [hactive, Bool.false_eq_true, if_false, PMF.map_comp, Function.comp_def, Prod.map, id_eq, hnext]
      using hrecord input state

theorem simulateQ_lengthRecordImpl_project {ι σ τ β : Type} {spec : OracleSpec ι}
    {Ω : spec.Domain → Type}
    (record : (input : spec.Domain) → σ → PMF (Ω input))
    (response : (input : spec.Domain) → Ω input → spec.Range input)
    (advance : (input : spec.Domain) → σ → Nat → Ω input → σ)
    (active : spec.Domain → σ → Bool)
    (accept : ENNReal) (hpos : accept ≠ 0) (hle : accept ≤ 1)
    (base : QueryImpl spec (StateT τ PMF)) (project : σ → τ)
    (next : (input : spec.Domain) → σ → Ω input → τ)
    (hnext : ∀ input state length outcome, project (advance input state length outcome) = next input state outcome)
    (hrecord : ∀ input state, (record input state).map
      (fun outcome => (response input outcome, next input state outcome)) = (base input).run (project state))
    (computation : OracleComp spec β) (state : σ) :
    Prod.map id project <$>
      (simulateQ (lengthRecordImpl record response advance active accept hpos hle) computation).run state =
      (simulateQ base computation).run (project state) :=
  map_run_simulateQ_eq_of_query_map_eq _ _ project
    (lengthRecordImpl_project record response advance active accept hpos hle base project next hnext hrecord)
    computation state

end SphincsSecurity.Concrete
