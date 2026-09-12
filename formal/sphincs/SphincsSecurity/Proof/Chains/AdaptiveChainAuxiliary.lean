import SphincsSecurity.Proof.Chains.AdaptiveChainEndpoint
import SphincsSecurity.Proof.Base.QueryCap
namespace SphincsSecurity.Concrete.PartialChainEndpoint

open _root_.OracleComp OracleSpec
set_option backward.isDefEq.respectTransparency false

variable {State AuxIndex ExtraIndex : Type} {auxSpec : OracleSpec AuxIndex} {extraSpec : OracleSpec ExtraIndex} {n : Nat} {Result : Type}

noncomputable def extendAux (auxiliary : QueryImpl auxSpec PMF) (extra : QueryImpl extraSpec Id) : QueryImpl (auxSpec + extraSpec) PMF
  | .inl input => auxiliary input
  | .inr input => PMF.pure (extra input)

noncomputable def eraseAux (extra : QueryImpl extraSpec Id) :
    QueryImpl ((auxSpec + extraSpec) + PrefixSpec n State) (OracleComp (auxSpec + PrefixSpec n State))
  | .inl (.inl input) => liftM ((auxSpec + PrefixSpec n State).query (.inl input))
  | .inl (.inr input) => pure (extra input)
  | .inr query => liftM ((auxSpec + PrefixSpec n State).query (.inr query))

variable [Fintype State] [DecidableEq State] [Nonempty State]

omit [Fintype State] [Nonempty State] in
theorem observedRun_eraseAux (auxiliary : QueryImpl auxSpec PMF) (extra : QueryImpl extraSpec Id)
    (tables : Fin n → State → State) (computation : OracleComp ((auxSpec + extraSpec) + PrefixSpec n State) Result)
    (observed : Fin n → State → Option State) :
    observedRun auxiliary tables (simulateQ (eraseAux extra) computation) observed = observedRun (extendAux auxiliary extra) tables computation observed := by
  have himpl : (observedImpl auxiliary tables).compose (eraseAux extra) = observedImpl (extendAux auxiliary extra) tables := by
    funext input
    cases input with
    | inl input =>
        cases input with
        | inl input => simp only [QueryImpl.apply_compose, eraseAux, simulateQ_spec_query]; rfl
        | inr input =>
            simp only [QueryImpl.apply_compose, eraseAux, simulateQ_pure, observedImpl, extendAux]
            ext observed
            simp only [StateT.run_pure, StateT.run_mk, PMF.map, PMF.pure_bind, Function.comp_def, PMF.monad_pure_eq_pure]
    | inr query => simp only [QueryImpl.apply_compose, eraseAux, simulateQ_spec_query]; rfl
  simp only [observedRun, ← QueryImpl.simulateQ_compose, himpl]

theorem realRun_eraseAux (auxiliary : State → QueryImpl auxSpec PMF) (extra : State → QueryImpl extraSpec Id)
    (computation : State → OracleComp ((auxSpec + extraSpec) + PrefixSpec n State) Result)
    (observed : Fin n → State → Option State) :
    realRun auxiliary (fun endpoint => simulateQ (eraseAux (extra endpoint)) (computation endpoint)) observed =
      realRun (fun endpoint => extendAux (auxiliary endpoint) (extra endpoint)) computation observed := by
  simp only [realRun, observedRun_eraseAux]

end SphincsSecurity.Concrete.PartialChainEndpoint
