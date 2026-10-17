import Sphincs.BridgeReduce
import Sphincs.SecurityHiddenStopping

/-! The fixed-function cost run of a hidden-row oracle agrees with the existing stopped
execution until the first ordinary query names a still-hidden canonical input. -/

open OracleComp OracleSpec ENNReal

namespace Sphincs.Security.HiddenBridge

open HiddenCost Stop GraphView HiddenGraph

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
attribute [local instance] Classical.propDecidable

section Generic

variable {D R A ι : Type} [Fintype ι]

omit [Fintype ι] in
theorem stopped_map {α β : Type} (model : HiddenRows.Model D R A ι) (table : ι → Digest)
    (outside : D → R) (g : α → β) (computation : OracleComp (HiddenRows.SourceSpec D R ι) α)
    (known : HiddenReveal.Knowledge ι) :
    HiddenRows.stopped model table outside (g <$> computation) known =
      Option.map g <$> HiddenRows.stopped model table outside computation known := by
  induction computation using OracleComp.inductionOn generalizing known with
  | pure value => rfl
  | query_bind input next ih =>
      rw [map_bind]
      cases input with
      | inl draw =>
          rw [HiddenRows.stopped_private, HiddenRows.stopped_private, map_bind]
          exact congrArg (fun k => liftM (unifSpec.query draw) >>= k) (funext fun value => ih value known)
      | inr input => cases input with
        | inr coordinate =>
            rw [HiddenRows.stopped_reveal, HiddenRows.stopped_reveal]
            exact ih _ _
        | inl bytes =>
            rw [HiddenRows.stopped_hash, HiddenRows.stopped_hash]
            cases model.parse bytes with
            | none => exact ih _ known
            | some query =>
                dsimp only
                split_ifs
                · simp
                · exact ih _ _
                · exact ih _ _

theorem probEvent_stopOr_map {α β : Type} (g : α → β) (bad : β → Prop)
    (program : ProbComp (Option α)) :
    Pr[HiddenReveal.StopOr bad | Option.map g <$> program] =
      Pr[HiddenReveal.StopOr (bad ∘ g) | program] := by
  rw [probEvent_map]
  congr 1
  funext result
  cases result <;> rfl

end Generic

variable {A : Type}

theorem erase_trace_query_bind {α : Type} (input : CostSpec.Domain)
    (next : CostSpec.Range input → OracleComp CostSpec α) :
    erase (trace (liftM (CostSpec.query input) >>= next)) =
      eraseQuery input >>= fun value =>
        (fun result => (result.1, recorded input ++ result.2)) <$>
          erase (trace (next value)) := by
  rw [trace_query_bind, erase, simulateQ_bind, simulateQ_spec_query]
  simp only [simulateQ_map]
  rfl

/-- Identical until a hidden guess: every event of the fixed-function run is an event of the
stopped execution unless that execution has stopped. -/
theorem costRun_le_stopped {α : Type} (model : HiddenRows.Model HashInput HashOutput A Coordinate)
    (table : HiddenGraph.Table) (outside : HashInput → HashOutput)
    (computation : OracleComp CostSpec α) (known : HiddenReveal.Knowledge Coordinate)
    (hknown : HiddenRows.KnownAgrees table known) (event : α × List (Entry HashInput) → Prop) :
    Pr[event | costRun (HiddenRows.answer model table outside) table computation] ≤
      Pr[HiddenReveal.StopOr event |
        HiddenRows.stopped model table outside (erase (trace computation)) known] := by
  induction computation using OracleComp.inductionOn generalizing known event with
  | pure value =>
      rw [costRun_pure]
      change _ ≤ Pr[HiddenReveal.StopOr event | (pure (some (value, [])) : ProbComp _)]
      simp [HiddenReveal.StopOr]
  | query_bind input next ih =>
      rw [costRun_query_bind, erase_trace_query_bind]
      rcases input with (draw | (bytes | coordinate)) | amount
      · change _ ≤ Pr[_ | HiddenRows.stopped model table outside
          (liftM ((HiddenRows.SourceSpec HashInput HashOutput Coordinate).query (.inl draw)) >>= _) known]
        rw [HiddenRows.stopped_private]
        simp only [probEvent_bind_eq_tsum]
        refine ENNReal.tsum_le_tsum fun value => mul_le_mul' le_rfl ?_
        rw [stopped_map, probEvent_stopOr_map, probEvent_map]
        exact ih value known hknown _
      · change _ ≤ Pr[_ | HiddenRows.stopped model table outside
          (liftM ((HiddenRows.SourceSpec HashInput HashOutput Coordinate).query (.inr (.inl bytes))) >>= _) known]
        rw [HiddenRows.stopped_hash]
        change Pr[_ | pure (HiddenRows.answer model table outside bytes) >>= _] ≤ _
        rw [pure_bind]
        cases hp : model.parse bytes with
        | none =>
            dsimp only
            rw [stopped_map, probEvent_stopOr_map, probEvent_map]
            exact ih _ known hknown _
        | some query =>
            dsimp only
            split_ifs with hstop hcanonical
            · simp [HiddenReveal.StopOr]
            · rw [stopped_map, probEvent_stopOr_map, probEvent_map]
              exact ih _ _ (hknown.reveal _) _
            · rw [stopped_map, probEvent_stopOr_map, probEvent_map]
              exact ih _ known hknown _
      · change _ ≤ Pr[_ | HiddenRows.stopped model table outside
          (liftM ((HiddenRows.SourceSpec HashInput HashOutput Coordinate).query (.inr (.inr coordinate))) >>= _) known]
        rw [HiddenRows.stopped_reveal]
        change Pr[_ | pure (table coordinate) >>= _] ≤ _
        rw [pure_bind, stopped_map, probEvent_stopOr_map, probEvent_map]
        exact ih _ _ (hknown.reveal coordinate) _
      · change Pr[_ | pure () >>= _] ≤ Pr[_ | HiddenRows.stopped model table outside (pure () >>= _) known]
        rw [pure_bind, pure_bind, stopped_map, probEvent_stopOr_map, probEvent_map]
        exact ih () known hknown _

end Sphincs.Security.HiddenBridge
