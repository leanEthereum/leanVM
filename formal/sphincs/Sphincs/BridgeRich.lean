import Sphincs.BridgeLazyGame

/-! A richer graph-view program returning the forgery, the signing log, the verifier's
answer and every revealed coordinate. The original win event is a function of its result. -/

open OracleComp OracleSpec ENNReal

namespace Sphincs.Security.HiddenBridge

open HiddenCost GraphView Concrete

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
attribute [local instance] Classical.propDecidable

section Generic

variable {D R ι : Type}

def revealed : (SourceCostSpec D R ι).Domain → List ι
  | .inl (.inr (.inr coordinate)) => [coordinate]
  | _ => []

/-- Record the coordinates of every privileged reveal, in order. -/
def withReveals {α : Type} (computation : OracleComp (SourceCostSpec D R ι) α) :
    OracleComp (SourceCostSpec D R ι) (α × List ι) :=
  OracleComp.construct (fun value => pure (value, []))
    (fun input _ next => do
      let value ← liftM ((SourceCostSpec D R ι).query input)
      let result ← next value
      return (result.1, revealed input ++ result.2)) computation

theorem withReveals_pure {α : Type} (value : α) :
    withReveals (pure value : OracleComp (SourceCostSpec D R ι) α) = pure (value, []) := rfl

theorem withReveals_query_bind {α : Type} (input : (SourceCostSpec D R ι).Domain)
    (next : (SourceCostSpec D R ι).Range input → OracleComp (SourceCostSpec D R ι) α) :
    withReveals (liftM ((SourceCostSpec D R ι).query input) >>= next) =
      liftM ((SourceCostSpec D R ι).query input) >>= fun value =>
        (fun result => (result.1, revealed input ++ result.2)) <$> withReveals (next value) := by
  simp only [withReveals, OracleComp.construct_query_bind, map_eq_bind_pure_comp]
  rfl

theorem fst_withReveals {α : Type} (computation : OracleComp (SourceCostSpec D R ι) α) :
    Prod.fst <$> withReveals computation = computation := by
  induction computation using OracleComp.inductionOn with
  | pure value => rfl
  | query_bind input next ih =>
      rw [withReveals_query_bind, map_bind]
      congr 1
      funext value
      rw [Functor.map_map]
      exact ih value

theorem cap_query_bind_gen {α : Type} (input : (SourceCostSpec D R ι).Domain)
    (next : (SourceCostSpec D R ι).Range input → OracleComp (SourceCostSpec D R ι) α) (budget : Nat) :
    cap (liftM ((SourceCostSpec D R ι).query input) >>= next) budget =
      if sourceCost input ≤ budget then
        liftM ((SourceCostSpec D R ι).query input) >>= fun value => cap (next value) (budget - sourceCost input)
      else pure none := rfl

theorem cap_map {α β : Type} (g : α → β) (computation : OracleComp (SourceCostSpec D R ι) α)
    (budget : Nat) : cap (g <$> computation) budget = Option.map g <$> cap computation budget := by
  induction computation using OracleComp.inductionOn generalizing budget with
  | pure value => rfl
  | query_bind input next ih =>
      rw [map_bind, cap_query_bind_gen, cap_query_bind_gen]
      split
      · rw [map_bind]
        congr 1
        funext value
        exact ih value _
      · rfl

theorem trace_map {α β : Type} (g : α → β) (computation : OracleComp (SourceCostSpec D R ι) α) :
    trace (g <$> computation) = (fun result => (g result.1, result.2)) <$> trace computation := by
  induction computation using OracleComp.inductionOn with
  | pure value => rfl
  | query_bind input next ih =>
      rw [map_bind, trace_query_bind, trace_query_bind, map_bind]
      congr 1
      funext value
      rw [ih value, Functor.map_map, Functor.map_map]

theorem erase_map {α β : Type} (g : α → β) (computation : OracleComp (SourceCostSpec D R ι) α) :
    erase (g <$> computation) = g <$> erase computation := by
  simp only [erase, simulateQ_map]

end Generic

theorem outside_stopped_map {A α β : Type}
    (model : HiddenRows.Model HashInput HashOutput A HiddenGraph.Coordinate) (table : HiddenGraph.Table)
    (g : α → β)
    (computation : OracleComp (HiddenRows.SourceSpec HashInput HashOutput HiddenGraph.Coordinate) α)
    (known : HiddenReveal.Knowledge HiddenGraph.Coordinate) (cache : QueryCache HashSpec) :
    HiddenOutside.stopped model table (g <$> computation) known cache =
      Option.map (fun result => (g result.1, result.2)) <$>
        HiddenOutside.stopped model table computation known cache := by
  induction computation using OracleComp.inductionOn generalizing known cache with
  | pure value => rfl
  | query_bind input next ih =>
      rw [map_bind]
      rcases input with draw | (bytes | coordinate)
      · rw [outside_stopped_private, outside_stopped_private, map_bind]
        congr 1
        funext value
        exact ih value known cache
      · rw [outside_stopped_hash, outside_stopped_hash]
        cases model.parse bytes with
        | none =>
            simp only [map_bind]
            congr 1
            funext result
            exact ih _ known _
        | some query =>
            dsimp only
            split_ifs
            · simp
            · exact ih _ _ cache
            · simp only [map_bind]
              congr 1
              funext result
              exact ih _ known _
      · rw [outside_stopped_reveal, outside_stopped_reveal]
        exact ih _ _ cache

variable [Params]

/-- Forgery, signing log and verifier answer of the graph-view game. -/
abbrev Outcome := Forgery × QueryLog SigningSpec × Bool

def outcomeWins (outcome : Outcome) : Bool :=
  decide (SigningTranscript.Valid outcome.2.1 ∧ ¬SigningTranscript.Contains outcome.2.1 outcome.1) &&
    outcome.2.2

noncomputable def costRestX (parameter : PublicParameter) (data : PublicData) (adversary : Adversary) :
    OracleComp CostSpec Outcome := do
  let pk : PublicKey := ⟨data.root, parameter⟩
  let (forgery, log) ← (simulateQ (costInteraction parameter data) (adversary.main pk)).run
  let verified ← liftM (Concrete.verify pk forgery.message forgery.signature : OracleComp HashSpec Bool)
  return (forgery, log, verified)

noncomputable def costGameX (parameter : PublicParameter) (data : PublicData) (adversary : Adversary) :
    OracleComp CostSpec Outcome := do
  HiddenCost.tick (226 * 2 ^ subtreeHeight + 2 * (totalHeight - subtreeHeight))
  costRestX parameter data adversary

theorem costGame_eq_map (parameter : PublicParameter) (data : PublicData) (adversary : Adversary) :
    costGame parameter data adversary = outcomeWins <$> costGameX parameter data adversary := by
  simp only [costGame, costGameX, costRest, costRestX, map_bind, map_pure, outcomeWins]

/-- The rich program run in the stopped and comparison worlds. -/
noncomputable def richProgram (adversary : Adversary) (q : Nat) (parameter : PublicParameter)
    (data : PublicData) : OracleComp CostSpec (Option Outcome × List HiddenGraph.Coordinate) :=
  withReveals (cap (costGameX parameter data adversary) q)

theorem cap_costGame_eq (adversary : Adversary) (q : Nat) (parameter : PublicParameter)
    (data : PublicData) :
    cap (costGame parameter data adversary) q =
      (fun result => Option.map outcomeWins result.1) <$> richProgram adversary q parameter data := by
  rw [richProgram, ← Functor.map_map, fst_withReveals, costGame_eq_map, cap_map]

open Completeness SeedModel Graph Assembly Reduce HiddenGraph Internalize

attribute [local instance] sampleCellFintypeInst sampleCellDecEq hiddenTableSampleable highsSampleable
  remainingSampleable

/-- A stopped rich result that wins the original game. -/
def RichWin (result : ((Option Outcome × List HiddenGraph.Coordinate) × List (Entry HashInput)) ×
    QueryCache HashSpec) : Prop :=
  ∃ value, result.1.1.1 = some value ∧ outcomeWins value = true

/-- The data of one public/structural sample. -/
noncomputable def sampleData (parameterOutput : HashOutput) (fixed : HiddenGraph.Table)
    (highs : CoordinateHighs) (remaining : RemainingOutputs) : PublicData :=
  GraphView.publicData (labelsOf (splitMaterial parameterOutput highs remaining fixed)
    (splitAnswers highs remaining fixed))

end Sphincs.Security.HiddenBridge
