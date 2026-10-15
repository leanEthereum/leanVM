import SphincsFors.BridgeAssembly

/-! Probabilistic semantics of the graph-view game with an explicit cost trace, and the exact
"identical until the seed is named" comparison for two fixed answer functions. -/

open OracleComp OracleSpec ENNReal

namespace SphincsFors.Security.Stop

open Completeness HiddenCost GraphView

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
attribute [local instance] Classical.propDecidable

/-- Private draws are real; ordinary queries read a fixed function; reveals read a fixed table;
honest-work ticks are free here (their cost is kept in the trace). -/
noncomputable def fixedCostP (f : HashInput → HashOutput) (table : HiddenGraph.Table) :
    QueryImpl CostSpec ProbComp
  | .inl (.inl draw) => liftM (unifSpec.query draw)
  | .inl (.inr (.inl input)) => pure (f input)
  | .inl (.inr (.inr coordinate)) => pure (table coordinate)
  | .inr _ => pure ()

noncomputable def costRun {α : Type} (f : HashInput → HashOutput) (table : HiddenGraph.Table)
    (computation : OracleComp CostSpec α) : ProbComp (α × List (Entry HashInput)) :=
  simulateQ (fixedCostP f table) (trace computation)

theorem costRun_pure {α : Type} (f : HashInput → HashOutput) (table : HiddenGraph.Table) (value : α) :
    costRun f table (pure value) = pure (value, []) := by
  simp [costRun, trace_pure]

theorem costRun_query_bind {α : Type} (f : HashInput → HashOutput) (table : HiddenGraph.Table)
    (input : CostSpec.Domain) (next : CostSpec.Range input → OracleComp CostSpec α) :
    costRun f table (liftM (CostSpec.query input) >>= next) =
      fixedCostP f table input >>= fun answer =>
        (fun result => (result.1, recorded input ++ result.2)) <$> costRun f table (next answer) := by
  rw [costRun, trace_query_bind, simulateQ_bind, simulateQ_spec_query]
  simp only [simulateQ_map, costRun]

/-- The PMF handler underneath the cost writer. -/
noncomputable def fixedCostPMF (f : QueryImpl HashSpec Id) (table : HiddenGraph.Table) :
    QueryImpl CostSpec PMF :=
  fun | .inl request => GraphView.fixedSource f table request | .inr _ => PMF.pure ()

/-- Writer cost is the cost of the recorded trace. -/
theorem run_withAddCost_trace {m : Type → Type} [Monad m] [LawfulMonad m] {α : Type}
    (impl : QueryImpl CostSpec m) (computation : OracleComp CostSpec α) :
    (simulateQ (impl.withAddCost sourceCost) computation).run =
      (fun result => (result.1, Multiplicative.ofAdd (traceCost result.2))) <$>
        simulateQ impl (trace computation) := by
  induction computation using OracleComp.inductionOn with
  | pure value => simp [trace_pure, traceCost]
  | query_bind input next ih =>
      rw [trace_query_bind, simulateQ_bind, simulateQ_bind, simulateQ_spec_query, simulateQ_spec_query,
        WriterT.run_bind, QueryImpl.withAddCost_apply]
      simp only [WriterT.run_bind, map_bind, simulateQ_map, ih]
      simp [map_eq_bind_pure_comp, bind_assoc, traceCost_append,
        recorded_cost, ← ofAdd_add]

theorem liftM_id_pmf {α : Type} (x : α) : (liftM (show Id α from x) : PMF α) = PMF.pure x := rfl

theorem evalDist_liftM_id {α : Type} (x : α) :
    𝒟[(liftM (show Id α from x) : PMF α)] = 𝒟[(pure x : ProbComp α)] := by
  rw [liftM_id_pmf]
  simp

theorem evalDist_fixedCostSource {α : Type} (f : QueryImpl HashSpec Id) (table : HiddenGraph.Table)
    (computation : OracleComp CostSpec α) :
    𝒟[(simulateQ (fixedCostSource f table) computation).run] =
      𝒟[(fun result => (result.1, Multiplicative.ofAdd (traceCost result.2))) <$>
        costRun f table computation] := by
  rw [show fixedCostSource f table = (fixedCostPMF f table).withAddCost sourceCost from rfl,
    run_withAddCost_trace, evalDist_map, evalDist_map, costRun]
  congr 1
  refine Assembly.evalDist_simulateQ_congr _ _ (fun input => ?_) _
  rcases input with (draw | (bytes | coordinate)) | amount
  · change 𝒟[PMF.uniformOfFintype (Fin (draw + 1))] = 𝒟[(liftM (unifSpec.query draw) : ProbComp _)]
    rw [evalDist_query]
  · exact evalDist_liftM_id (f bytes)
  · exact evalDist_liftM_id (table coordinate)
  · change 𝒟[PMF.pure ()] = 𝒟[(pure () : ProbComp _)]
    simp

/-! ### Identical until a marked ordinary input -/

/-- Some ordinary input of the trace satisfies the marker. -/
def Hits (marked : HashInput → Prop) (entries : List (Entry HashInput)) : Prop :=
  ∃ input, Sum.inl input ∈ entries ∧ marked input

theorem hits_append_recorded (marked : HashInput → Prop) (input : CostSpec.Domain)
    (entries : List (Entry HashInput))
    (hinput : ∀ bytes, input = .inl (.inr (.inl bytes)) → ¬marked bytes) :
    Hits marked (recorded input ++ entries) ↔ Hits marked entries := by
  constructor
  · rintro ⟨bytes, hmem, hmarked⟩
    rw [List.mem_append] at hmem
    rcases hmem with hrec | htail
    · rcases input with (draw | (other | coordinate)) | amount <;> simp [recorded] at hrec
      subst other
      exact absurd hmarked (hinput bytes rfl)
    · exact ⟨bytes, htail, hmarked⟩
  · rintro ⟨bytes, hmem, hmarked⟩
    exact ⟨bytes, List.mem_append_right _ hmem, hmarked⟩

/-- Changing the answer function on marked inputs costs at most the marked-input probability,
both measured on the run with the unchanged function. -/
theorem probEvent_costRun_le {α : Type} (f f₀ : HashInput → HashOutput) (table : HiddenGraph.Table)
    (marked : HashInput → Prop) (hagree : ∀ input, ¬marked input → f input = f₀ input)
    (computation : OracleComp CostSpec α) (event : α × List (Entry HashInput) → Prop) :
    Pr[event | costRun f table computation] ≤
      Pr[event | costRun f₀ table computation] +
        Pr[fun result => Hits marked result.2 | costRun f₀ table computation] := by
  induction computation using OracleComp.inductionOn generalizing event with
  | pure value => simp [costRun_pure]
  | query_bind input next ih =>
      by_cases hmarked : ∃ bytes, input = .inl (.inr (.inl bytes)) ∧ marked bytes
      · obtain ⟨bytes, rfl, hbytes⟩ := hmarked
        have hone : Pr[fun result => Hits marked result.2 |
            costRun f₀ table (liftM (CostSpec.query (.inl (.inr (.inl bytes)))) >>= next)] = 1 := by
          rw [probEvent_eq_one_iff]
          refine ⟨by simp, fun result hresult => ?_⟩
          rw [costRun_query_bind, mem_support_bind_iff] at hresult
          obtain ⟨answer, _, hmap⟩ := hresult
          rw [support_map] at hmap
          obtain ⟨tail, _, rfl⟩ := hmap
          exact ⟨bytes, by simp [recorded], hbytes⟩
        rw [hone]
        exact probEvent_le_one.trans (le_add_self)
      · have hsame : fixedCostP f table input = fixedCostP f₀ table input := by
          rcases input with (draw | (bytes | coordinate)) | amount
          · rfl
          · simp only [fixedCostP]
            rw [hagree bytes (fun h => hmarked ⟨bytes, rfl, h⟩)]
          · rfl
          · rfl
        have hnot : ∀ bytes, input = .inl (.inr (.inl bytes)) → ¬marked bytes :=
          fun bytes heq h => hmarked ⟨bytes, heq, h⟩
        rw [costRun_query_bind, costRun_query_bind, hsame]
        simp only [probEvent_bind_eq_tsum, probEvent_map]
        rw [← ENNReal.tsum_add]
        refine ENNReal.tsum_le_tsum (fun answer => ?_)
        rw [← mul_add]
        refine mul_le_mul' le_rfl ?_
        have h := ih answer (event ∘ fun result : α × List (Entry HashInput) =>
          (result.1, recorded input ++ result.2))
        have hhit : (fun result : α × List (Entry HashInput) => Hits marked result.2) ∘
            (fun result : α × List (Entry HashInput) => (result.1, recorded input ++ result.2)) =
            fun result => Hits marked result.2 := by
          funext result
          exact propext (hits_append_recorded marked input result.2 hnot)
        rw [hhit]
        exact h

/-! ### Capping the original budget -/

theorem cap_pure' {α : Type} (value : α) (budget : Nat) :
    cap (pure value : OracleComp CostSpec α) budget = pure (some value) := rfl

theorem cap_query_bind' {α : Type} (input : CostSpec.Domain)
    (next : CostSpec.Range input → OracleComp CostSpec α) (budget : Nat) :
    cap (liftM (CostSpec.query input) >>= next) budget =
      if sourceCost input ≤ budget then
        liftM (CostSpec.query input) >>= fun value => cap (next value) (budget - sourceCost input)
      else pure none := rfl

/-- Runs within the budget are runs of the capped program. -/
theorem probEvent_costRun_le_cap {α : Type} (f : HashInput → HashOutput) (table : HiddenGraph.Table)
    (computation : OracleComp CostSpec α) (budget : Nat) (event : α → Prop) :
    Pr[fun result => event result.1 ∧ traceCost result.2 ≤ budget | costRun f table computation] ≤
      Pr[fun result => ∃ value, result.1 = some value ∧ event value |
        costRun f table (cap computation budget)] := by
  induction computation using OracleComp.inductionOn generalizing budget with
  | pure value =>
      rw [cap_pure', costRun_pure, costRun_pure]
      simp [traceCost]
  | query_bind input next ih =>
      rw [cap_query_bind']
      split
      · rename_i hcost
        rw [costRun_query_bind, costRun_query_bind]
        simp only [probEvent_bind_eq_tsum, probEvent_map]
        refine ENNReal.tsum_le_tsum (fun answer => mul_le_mul' le_rfl ?_)
        refine le_trans (probEvent_mono ?_) (ih answer (budget - sourceCost input))
        intro result _ hresult
        refine ⟨hresult.1, ?_⟩
        have h : traceCost (recorded input ++ result.2) ≤ budget := hresult.2
        rw [traceCost_append, recorded_cost] at h
        omega
      · rename_i hcost
        rw [costRun_query_bind]
        simp only [probEvent_bind_eq_tsum, probEvent_map]
        refine le_trans (le_of_eq ?_) bot_le
        refine ENNReal.tsum_eq_zero.2 (fun answer => ?_)
        rw [mul_eq_zero]
        right
        rw [probEvent_eq_zero_iff]
        intro result _ hresult
        have h : traceCost (recorded input ++ result.2) ≤ budget := hresult.2
        rw [traceCost_append, recorded_cost] at h
        omega

end SphincsFors.Security.Stop
