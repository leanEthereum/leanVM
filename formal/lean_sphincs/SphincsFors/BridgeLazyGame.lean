import SphincsFors.BridgeShortCost

/-! For a computation that queries only short inputs, the stopped hidden-row experiment over a
uniformly sampled outside table on the short inputs has the law of the stopped experiment with an
actual lazy outside random oracle started from the structural cache. -/

open OracleComp OracleSpec ENNReal

namespace SphincsFors.Security.HiddenBridge

open Completeness SeedModel Graph Assembly Reduce HiddenGraph Eager Internalize

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
attribute [local instance] Classical.propDecidable

theorem evalDist_stoppedExperiment_lazy {A α : Type}
    (model : HiddenRows.Model HashInput HashOutput A HiddenGraph.Coordinate)
    (cache : QueryCache HashSpec)
    (computation : OracleComp (HiddenRows.SourceSpec HashInput HashOutput HiddenGraph.Coordinate) α)
    (hshort : OnlyShort computation) (known : HiddenReveal.Knowledge HiddenGraph.Coordinate) :
    (($ᵗ Eager.Table) >>= fun outside =>
        HiddenRows.stoppedExperiment model (extend cache outside) computation known) =ᵈ (Option.map Prod.fst <$> HiddenOutside.stoppedExperiment model computation known cache) := by
  unfold HiddenRows.stoppedExperiment HiddenOutside.stoppedExperiment
  refine (OracleComp.EvalDistEq.bind_bind_swap _ _ _).trans ?_
  rw [map_bind]
  exact EvalDistEq.bind_right _ fun table => evalDist_stopped_lazy model table computation hshort known cache

theorem probEvent_bind_congr₂ {α β γ : Type} (p : ProbComp α) (k₁ : α → ProbComp β)
    (k₂ : α → ProbComp γ) (event₁ : β → Prop) (event₂ : γ → Prop)
    (h : ∀ a, Pr{let x ← k₁ a}[event₁ x] = Pr{let x ← k₂ a}[event₂ x]) :
    Pr{let x ← p >>= k₁}[event₁ x] = Pr{let x ← p >>= k₂}[event₂ x] := by
  simp only [OracleComp.prEvent_bind_eq_tsum, h]

end SphincsFors.Security.HiddenBridge
