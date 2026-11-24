module

public import FORS.Reduction.SeedFreeGame
public import FORS.LazyRun.Outside

@[expose] public section

/-! The fixed-function cost run of a hidden-row oracle agrees with the existing stopped
execution until the first ordinary query names a still-hidden canonical input. -/

open OracleComp OracleSpec ENNReal

namespace FORS.Security.HiddenBridge

variable [Params]

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
    Pr{let x ← Option.map g <$> program}[(HiddenReveal.StopOr bad) x] =
      Pr{let x ← program}[(HiddenReveal.StopOr (bad ∘ g)) x] := by
  rw [prEvent_map]
  congr 1
  refine congrArg (· <$> program) (funext fun result => ?_)
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

end FORS.Security.HiddenBridge
