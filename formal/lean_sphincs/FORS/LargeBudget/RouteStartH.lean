module

public import FORS.Reduction.AdvProgBridgeH
public import FORS.Reduction.SeedEliminationAdv
public import FORS.LazyRun.Expose

@[expose] public section

/-! The honest-reading seed-free experiment (`AdvCount.seedFreeExperiment`) in the stopped
prepared world and then in the interpreted run, as `seedFree_le_prep` and `stopped_le_interp` for
the charged game: the honest program is short (its stopped form follows the charged one's,
`Corr.onlyShort`), and its winning stopped runs are bad (`win_implies_bad`). -/

open OracleComp OracleSpec ENNReal

namespace FORS.Security.HiddenBridge

variable [Params]

open HiddenReveal HiddenCost Eager Short Concrete Stop
open Completeness SeedModel _root_.FORS.Security.Graph Assembly Reduce HiddenGraph Internalize GraphView

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
set_option linter.constructorNameAsVariable false
attribute [local instance] Classical.propDecidable

section Until

variable {A : Type}

theorem erase_trace_query_bindH {α : Type} (input : CostSpecH.Domain)
    (next : CostSpecH.Range input → OracleComp CostSpecH α) :
    erase (trace (liftM (CostSpecH.query input) >>= next)) =
      eraseQuery input >>= fun value =>
        (fun result => (result.1, recorded input ++ result.2)) <$>
          erase (trace (next value)) := by
  rw [trace_query_bind, erase, simulateQ_bind, simulateQ_spec_query]
  simp only [simulateQ_map]
  rfl

/-- Identical until a hidden guess, with honest reads: every event of the fixed-function run is an event of
the
stopped execution unless that execution has stopped. -/
theorem costRunH_le_stopped {α : Type} (model : HiddenRows.Model HashInput HashOutput A Coordinate)
    (table : HiddenGraph.Table) (outside : HashInput → HashOutput)
    (computation : OracleComp CostSpecH α) (known : HiddenReveal.Knowledge Coordinate)
    (hknown : HiddenRows.KnownAgrees table known) (event : α × List (Entry HashInput) → Prop) :
    Pr{let x ← costRunH (HiddenRows.answer model table outside) table computation}[event x] ≤
      Pr{let x ← HiddenRows.stopped model table outside (erase (trace computation)) known}[(HiddenReveal.StopOr event) x] := by
  induction computation using OracleComp.inductionOn generalizing known event with
  | pure value =>
      rw [costRunH_pure]
      change _ ≤ Pr{let x ← (pure (some (value, [])) : ProbComp _)}[(HiddenReveal.StopOr event) x]
      simp [HiddenReveal.StopOr]
  | query_bind input next ih =>
      rw [costRunH_query_bind, erase_trace_query_bindH]
      rcases input with (draw | (bytes | coordinate)) | (amount | honest)
      · change _ ≤ Pr{let x ← (HiddenRows.stopped model table outside
          (liftM ((HiddenRows.SourceSpec HashInput HashOutput Coordinate).query (.inl draw)) >>= _) known)}[(HiddenReveal.StopOr event) x]
        rw [HiddenRows.stopped_private]
        simp only [OracleComp.prEvent_bind_eq_tsum]
        refine ENNReal.tsum_le_tsum fun value => mul_le_mul' le_rfl ?_
        rw [stopped_map, probEvent_stopOr_map, prEvent_map]
        exact ih value known hknown _
      · change _ ≤ Pr{let x ← (HiddenRows.stopped model table outside
          (liftM ((HiddenRows.SourceSpec HashInput HashOutput Coordinate).query (.inr (.inl bytes))) >>= _) known)}[(HiddenReveal.StopOr event) x]
        rw [HiddenRows.stopped_hash]
        change Pr{let x ← pure (HiddenRows.answer model table outside bytes) >>= _}[event x] ≤ _
        rw [pure_bind]
        cases hp : model.parse bytes with
        | none =>
            dsimp only
            rw [stopped_map, probEvent_stopOr_map, prEvent_map]
            exact ih _ known hknown _
        | some query =>
            dsimp only
            split_ifs with hstop hcanonical
            · simp [HiddenReveal.StopOr]
            · rw [stopped_map, probEvent_stopOr_map, prEvent_map]
              exact ih _ _ (hknown.reveal _) _
            · rw [stopped_map, probEvent_stopOr_map, prEvent_map]
              exact ih _ known hknown _
      · change _ ≤ Pr{let x ← (HiddenRows.stopped model table outside
          (liftM ((HiddenRows.SourceSpec HashInput HashOutput Coordinate).query (.inr (.inr coordinate))) >>= _) known)}[(HiddenReveal.StopOr event) x]
        rw [HiddenRows.stopped_reveal]
        change Pr{let x ← pure (table coordinate) >>= _}[event x] ≤ _
        rw [pure_bind, stopped_map, probEvent_stopOr_map, prEvent_map]
        exact ih _ _ (hknown.reveal coordinate) _
      · change Pr{let x ← pure () >>= _}[event x] ≤ Pr{let x ← HiddenRows.stopped model table outside (pure () >>= _) known}[(HiddenReveal.StopOr event) x]
        rw [pure_bind, pure_bind, stopped_map, probEvent_stopOr_map, prEvent_map]
        exact ih () known hknown _
      · change _ ≤ Pr{let x ← (HiddenRows.stopped model table outside
          (liftM ((HiddenRows.SourceSpec HashInput HashOutput Coordinate).query (.inr (.inl honest))) >>= _) known)}[(HiddenReveal.StopOr event) x]
        rw [HiddenRows.stopped_hash]
        change Pr{let x ← pure (HiddenRows.answer model table outside honest) >>= _}[event x] ≤ _
        rw [pure_bind]
        cases hp : model.parse honest with
        | none =>
            dsimp only
            rw [stopped_map, probEvent_stopOr_map, prEvent_map]
            exact ih _ known hknown _
        | some query =>
            dsimp only
            split_ifs with hstop hcanonical
            · simp [HiddenReveal.StopOr]
            · rw [stopped_map, probEvent_stopOr_map, prEvent_map]
              exact ih _ _ (hknown.reveal _) _
            · rw [stopped_map, probEvent_stopOr_map, prEvent_map]
              exact ih _ known hknown _

end Until

/-! ### The honest program is short -/

theorem onlyShort_query_bind_iff {α : Type} (input : SrcSpec.Domain) (next : SrcSpec.Range input → OracleComp SrcSpec α) :
    OnlyShort (liftM (SrcSpec.query input) >>= next) ↔ ¬LongSource input ∧ ∀ value, OnlyShort (next value) := by
  unfold OnlyShort
  rw [isQueryBoundP_query_bind_iff]
  simp only [Nat.lt_irrefl, or_false, Nat.zero_sub, ite_self]

/-- The honest program's stopped form is short where the charged one's is. -/
theorem Corr.onlyShort {α : Type} {left : OracleComp CostSpecH α} {right : OracleComp CostSpec α}
    (h : Corr left right) :
    ∀ budget budget', CostAtMost right budget' → OnlyShort (erun right budget') → OnlyShort (erun left budget) := by
  induction h with
  | pure a =>
      intro budget _ _ _
      rw [erun_pure]
      trivial
  | source input left right _ ih =>
      intro budget budget' hc hs
      rw [costAtMost_query_bind] at hc
      rw [erun_query_bind, ite_eq_left hc.1] at hs
      rw [erun_query_bind]
      split_ifs
      · change OnlyShort (liftM (SrcSpec.query input) >>= _) at hs ⊢
        rw [onlyShort_query_bind_iff] at hs ⊢
        exact ⟨hs.1, fun value => (isQueryBoundP_map_iff _ _ _).2
          (ih value _ _ (hc.2 value) ((isQueryBoundP_map_iff _ _ _).1 (hs.2 value)))⟩
      · trivial
  | tick amount left right _ ih =>
      intro budget budget' hc hs
      rw [costAtMost_query_bind] at hc
      rw [erun_query_bind, ite_eq_left hc.1] at hs
      rw [erun_query_bind]
      split_ifs
      · change OnlyShort (Pure.pure () >>= _) at hs ⊢
        rw [pure_bind] at hs ⊢
        exact (isQueryBoundP_map_iff _ _ _).2 (ih _ _ (hc.2 ()) ((isQueryBoundP_map_iff _ _ _).1 hs))
      · trivial
  | honest input _ left right _ ih =>
      intro budget budget' hc hs
      rw [costAtMost_query_bind] at hc
      rw [erun_query_bind, ite_eq_left hc.1] at hs
      rw [erun_query_bind, ite_eq_left (show @sourceCost HashInput HashOutput Coordinate HashInput
        (Sum.inr (Sum.inr input)) ≤ budget from Nat.zero_le _)]
      change OnlyShort (liftM (SrcSpec.query (.inr (.inl input))) >>= _) at hs ⊢
      rw [onlyShort_query_bind_iff] at hs ⊢
      exact ⟨hs.1, fun value => (isQueryBoundP_map_iff _ _ _).2
        (ih value _ _ (hc.2 value) ((isQueryBoundP_map_iff _ _ _).1 (hs.2 value)))⟩
  | extra amount left right _ ih =>
      intro budget budget' hc hs
      rw [costAtMost_query_bind] at hc
      rw [erun_query_bind, ite_eq_left hc.1] at hs
      change OnlyShort (Pure.pure () >>= _) at hs
      rw [pure_bind] at hs
      exact ih budget _ (hc.2 ()) ((isQueryBoundP_map_iff _ _ _).1 hs)

theorem onlyShort_richProgramH (adversary : Adversary) (q : Nat) (parameter : PublicParameter) (data : PublicData) :
    OnlyShort (erase (trace (richProgramH (internalize adversary) q parameter data))) := by
  obtain ⟨budget, hbudget⟩ := exists_costAtMost (costGameX parameter data (internalize adversary))
  exact (corr_costGameX parameter data (internalize adversary)).onlyShort q budget hbudget
    (OnlyC.erase (OnlyC.trace (OnlyC.withReveals (OnlyC.cap (OnlyC.costGameX parameter data adversary) budget))))

/-! ### The seed-free experiment in the stopped world -/

attribute [local instance] sampleCellFintypeInst sampleCellDecEq hiddenTableSampleable highsSampleable
  remainingSampleable

/-- The honest seed-free run at a mixed coordinate table is the hidden-row run. -/
theorem seedFreeRunH_mix (parameterOutput : HashOutput) (highs : CoordinateHighs) (remaining : RemainingOutputs)
    (adversary : Adversary) (q : Nat) (steps : Message → Randomness)
    (fixed fresh : HiddenGraph.Table) (table : Eager.Table) :
    AdvCount.seedFreeRun adversary q steps
        (splitMaterial parameterOutput highs remaining (mix (truncateHash parameterOutput) fixed fresh))
        (splitAnswers highs remaining (mix (truncateHash parameterOutput) fixed fresh)) table =
      Stop.costRunH
        (HiddenGraph.answer (truncateHash parameterOutput) (candidateActive (truncateHash parameterOutput))
          (tableExtending (knownOf (truncateHash parameterOutput) fixed) fresh)
          (fun address => highs address.outputCoordinate)
          (outsideFn (splitMaterial parameterOutput highs remaining fixed)
            (splitAnswers highs remaining fixed) table))
        (tableExtending (knownOf (truncateHash parameterOutput) fixed) fresh)
        (HiddenCost.cap (GraphView.costGame (truncateHash parameterOutput)
          (GraphView.publicData (labelsOf (splitMaterial parameterOutput highs remaining fixed)
            (splitAnswers highs remaining fixed)) steps) adversary) q) := by
  have hagree := mix_agree parameterOutput (fixed := fixed) (fresh := fresh)
  unfold AdvCount.seedFreeRun
  rw [graphFn_eq_answer, graphCoordinates_split, masked_mix, splitMaterial_parameter,
    publicData_agree parameterOutput highs remaining _ fixed steps hagree]
  rw [answer_congr_high _ _ _ _ (fun address => highs address.outputCoordinate) _
    (fun address hactive => highHalves_split parameterOutput highs remaining _ address hactive)]
  unfold outsideFn
  rw [structCache_agree parameterOutput highs remaining _ fixed hagree]

/-- One public/structural sample's hidden-row run at coordinate table `table`. -/
noncomputable def hiddenRun (adversary : Adversary) (q : Nat) (steps : Message → Randomness) (parameterOutput : HashOutput)
    (fixed : HiddenGraph.Table) (highs : CoordinateHighs) (remaining : RemainingOutputs)
    (outsideTable : Eager.Table) (table : HiddenGraph.Table) :
    ProbComp (Option Bool × List (HiddenCost.Entry HashInput)) :=
  Stop.costRunH
    (HiddenGraph.answer (truncateHash parameterOutput) (candidateActive (truncateHash parameterOutput))
      table (fun address => highs address.outputCoordinate)
      (outsideFn (splitMaterial parameterOutput highs remaining fixed)
        (splitAnswers highs remaining fixed) outsideTable))
    table
    (HiddenCost.cap (GraphView.costGame (truncateHash parameterOutput)
      (GraphView.publicData (labelsOf (splitMaterial parameterOutput highs remaining fixed)
        (splitAnswers highs remaining fixed)) steps) adversary) q)

/-- **Hidden decomposition.** The seed-free experiment samples every public and structural
value first and then the coordinate table as an exact completion of the known coordinates. -/
theorem evalDist_seedFree_completion (adversary : Adversary) (q : Nat) (steps : Message → Randomness) :
    AdvCount.seedFreeExperiment adversary q steps =ᵈ (do
        let parameterOutput ← $ᵗ HashOutput
        let fixed ← $ᵗ HiddenGraph.Table
        let highs ← $ᵗ CoordinateHighs
        let remaining ← $ᵗ RemainingOutputs
        let outsideTable ← $ᵗ Eager.Table
        let table ← HiddenReveal.completion (knownOf (truncateHash parameterOutput) fixed)
        hiddenRun adversary q steps parameterOutput fixed highs remaining outsideTable table) := by
  unfold AdvCount.seedFreeExperiment
  refine (evalDist_material_graph_continuation _).trans ?_
  refine EvalDistEq.bind_right _ fun parameterOutput => ?_
  rw [show (fun prf : HashOutput => sampleSplitPair >>= fun pair =>
      ($ᵗ Eager.Table) >>= AdvCount.seedFreeRun adversary q steps ((parameterOutput, prf), pair.1) pair.2) =
      fun _ => sampleSplitPair >>= fun pair =>
        ($ᵗ Eager.Table) >>= AdvCount.seedFreeRun adversary q steps ((parameterOutput, 0), pair.1) pair.2 from rfl]
  refine (OracleComp.EvalDistEq.bind_const _ _).trans ?_
  simp only [sampleSplitPair, bind_assoc, bind_map_left]
  refine (evalDist_mix_bind (truncateHash parameterOutput) _).trans ?_
  refine EvalDistEq.bind_right _ fun fixed => ?_
  simp only [joinedPair]
  change ($ᵗ HiddenGraph.Table) >>= (fun fresh => ($ᵗ CoordinateHighs) >>= fun highs =>
      ($ᵗ RemainingOutputs) >>= fun remaining => ($ᵗ Eager.Table) >>= fun outsideTable =>
        AdvCount.seedFreeRun adversary q steps
          (splitMaterial parameterOutput highs remaining (mix (truncateHash parameterOutput) fixed fresh))
          (splitAnswers highs remaining (mix (truncateHash parameterOutput) fixed fresh)) outsideTable) =ᵈ _
  simp only [seedFreeRunH_mix]
  refine (OracleComp.EvalDistEq.bind_bind_swap _ _ _).trans ?_
  refine EvalDistEq.bind_right _ fun highs => ?_
  refine (OracleComp.EvalDistEq.bind_bind_swap _ _ _).trans ?_
  refine EvalDistEq.bind_right _ fun remaining => ?_
  refine (OracleComp.EvalDistEq.bind_bind_swap _ _ _).trans ?_
  refine EvalDistEq.bind_right _ fun outsideTable => ?_
  refine EvalDistEq.trans ?_ (evalDist_completion_bind
    (knownOf (truncateHash parameterOutput) fixed) _).symm
  exact EvalDistEq.rfl

/-- The capped graph-view program of one sample. -/
noncomputable def sampleProgram (adversary : Adversary) (q : Nat) (steps : Message → Randomness) (parameterOutput : HashOutput)
    (fixed : HiddenGraph.Table) (highs : CoordinateHighs) (remaining : RemainingOutputs) :
    OracleComp GraphView.CostSpecH (Option Bool) :=
  HiddenCost.cap (GraphView.costGame (truncateHash parameterOutput)
    (GraphView.publicData (labelsOf (splitMaterial parameterOutput highs remaining fixed)
      (splitAnswers highs remaining fixed)) steps) adversary) q

theorem hiddenRunH_eq (adversary : Adversary) (q : Nat) (steps : Message → Randomness) (parameterOutput : HashOutput)
    (fixed : HiddenGraph.Table) (highs : CoordinateHighs) (remaining : RemainingOutputs)
    (outsideTable : Eager.Table) (table : HiddenGraph.Table) :
    hiddenRun adversary q steps parameterOutput fixed highs remaining outsideTable table =
      Stop.costRunH (HiddenRows.answer (sampleModel parameterOutput highs) table
        (outsideFn (splitMaterial parameterOutput highs remaining fixed)
          (splitAnswers highs remaining fixed) outsideTable)) table
        (sampleProgram adversary q steps parameterOutput fixed highs remaining) := by
  unfold hiddenRun sampleModel sampleProgram
  rw [rowModel_answer]

/-- **Seed-free to stopped**, with honest reads. -/
theorem seedFree_le_stopped (adversary : Adversary) (q : Nat) (steps : Message → Randomness)
    (event : Option Bool × List (HiddenCost.Entry HashInput) → Prop) :
    Pr{let x ← AdvCount.seedFreeExperiment adversary q steps}[event x] ≤
      Pr{let x ← (do
        let parameterOutput ← $ᵗ HashOutput
        let fixed ← $ᵗ HiddenGraph.Table
        let highs ← $ᵗ CoordinateHighs
        let remaining ← $ᵗ RemainingOutputs
        let outsideTable ← $ᵗ Eager.Table
        HiddenRows.stoppedExperiment (sampleModel parameterOutput highs)
          (outsideFn (splitMaterial parameterOutput highs remaining fixed)
            (splitAnswers highs remaining fixed) outsideTable)
          (HiddenCost.erase (HiddenCost.trace
            (sampleProgram adversary q steps parameterOutput fixed highs remaining)))
          (knownOf (truncateHash parameterOutput) fixed))}[(HiddenReveal.StopOr event) x] := by
  rw [(evalDist_seedFree_completion adversary q steps).prEvent_eq]
  refine probEvent_bind_mono_support _ _ _ _ _ fun parameterOutput _ => ?_
  refine probEvent_bind_mono_support _ _ _ _ _ fun fixed _ => ?_
  refine probEvent_bind_mono_support _ _ _ _ _ fun highs _ => ?_
  refine probEvent_bind_mono_support _ _ _ _ _ fun remaining _ => ?_
  refine probEvent_bind_mono_support _ _ _ _ _ fun outsideTable _ => ?_
  unfold HiddenRows.stoppedExperiment
  rw [(evalDist_completion_bind _ _).prEvent_eq, (evalDist_completion_bind _ _).prEvent_eq]
  refine probEvent_bind_mono_support _ _ _ _ _ fun fresh _ => ?_
  have hagree := HiddenRows.knownAgrees_completion (knownOf (truncateHash parameterOutput) fixed) fresh
  have h := costRunH_le_stopped (sampleModel parameterOutput highs)
    (tableExtending (knownOf (truncateHash parameterOutput) fixed) fresh)
    (outsideFn (splitMaterial parameterOutput highs remaining fixed)
      (splitAnswers highs remaining fixed) outsideTable)
    (sampleProgram adversary q steps parameterOutput fixed highs remaining)
    (knownOf (truncateHash parameterOutput) fixed) hagree event
  rw [hiddenRunH_eq]
  exact h

set_option maxRecDepth 100000 in
/-- **The honest seed-free win in the stopped prepared world.** -/
theorem seedFree_le_prep (adversary : Adversary) (q : Nat) (steps : Message → Randomness) :
    Pr{let z ← AdvCount.seedFreeExperiment (internalize adversary) q steps}[Win z] ≤
      Pr{let z ← (do
        let parameterOutput ← $ᵗ HashOutput
        let fixed ← $ᵗ HiddenGraph.Table
        let highs ← $ᵗ CoordinateHighs
        let remaining ← $ᵗ RemainingOutputs
        let prepared ← preparation parameterOutput fixed highs remaining
        HiddenOutside.stoppedExperiment (sampleModel parameterOutput highs)
          (erase (trace (richProgramH (internalize adversary) q (truncateHash parameterOutput)
            (sampleData parameterOutput fixed highs remaining steps))))
          (knownOf (truncateHash parameterOutput) fixed) prepared.2)}[(HiddenReveal.StopOr RichWin) z] := by
  refine (seedFree_le_stopped (internalize adversary) q steps Win).trans (le_of_eq ?_)
  refine probEvent_bind_congr₂ _ _ _ _ _ fun parameterOutput => ?_
  refine probEvent_bind_congr₂ _ _ _ _ _ fun fixed => ?_
  refine probEvent_bind_congr₂ _ _ _ _ _ fun highs => ?_
  refine probEvent_bind_congr₂ _ _ _ _ _ fun remaining => ?_
  have hprog : sampleProgram (internalize adversary) q steps parameterOutput fixed highs remaining =
      (fun result => Option.map outcomeWins result.1) <$> richProgramH (internalize adversary) q
        (truncateHash parameterOutput) (sampleData parameterOutput fixed highs remaining steps) :=
    cap_costGameH_eq _ _ _ _
  have hshort : OnlyShort (HiddenCost.erase (HiddenCost.trace
      (sampleProgram (internalize adversary) q steps parameterOutput fixed highs remaining))) := by
    rw [hprog, trace_map, erase_map]
    exact (isQueryBoundP_map_iff _ _ _).2 (onlyShort_richProgramH adversary q _ _)
  unfold outsideFn
  rw [(evalDist_stoppedExperiment_prep (sampleModel parameterOutput highs) _ (truncateHash parameterOutput)
      (sampleData parameterOutput fixed highs remaining) _ hshort _).prEvent_eq]
  refine probEvent_bind_congr₂ _ _ _ _ _ fun prepared => ?_
  rw [probEvent_stopOr_map]
  unfold HiddenOutside.stoppedExperiment
  refine probEvent_bind_congr₂ _ _ _ _ _ fun table => ?_
  rw [hprog, trace_map, erase_map, outside_stopped_map, probEvent_stopOr_map]
  have hevent : (HiddenReveal.StopOr ((Win ∘ Prod.fst) ∘ fun result :
      ((Option Outcome × List HiddenGraph.Coordinate) × List (Entry HashInput)) × QueryCache HashSpec =>
        ((Option.map outcomeWins result.1.1.1, result.1.2), result.2))) =
      HiddenReveal.StopOr RichWin := by
    funext result
    rcases result with _ | ⟨⟨⟨outcome, reveals⟩, entries⟩, cache⟩
    · rfl
    · rcases outcome with _ | value <;> simp [HiddenReveal.StopOr, Win, RichWin]
  rw [hevent]

end FORS.Security.HiddenBridge

section

open OracleComp OracleSpec ENNReal

namespace FORS.Security.ForsPotential

variable [Params]

open Concrete HiddenGraph HiddenCost HiddenDebt GraphView Domination ForsPrice ForsSigner HiddenReveal FORS.Base.Domination
open HiddenBridge Completeness SeedModel _root_.FORS.Security.Graph Assembly Reduce Internalize

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
set_option linter.constructorNameAsVariable false
attribute [local instance] Classical.propDecidable
attribute [local instance] sampleCellFintypeInst sampleCellDecEq hiddenTableSampleable highsSampleable
  remainingSampleable

/-- One table, honest program: the stopped run against the comparison run. -/
theorem stopped_table_le (hb : 0 < keptHeight topLayer) (adversary : Adversary) (q : ℕ) (hq : q < 2 ^ 256)
    (parameterOutput : HashOutput) (fixed : HiddenGraph.Table) (highs : CoordinateHighs)
    (remaining : RemainingOutputs) (steps : Message → Randomness)
    (prepared : (OtsKey → Option (Counter × Encoding)) × QueryCache HashSpec)
    (hprepared : prepared ∈ support (preparation parameterOutput fixed highs remaining))
    (table : Coordinate → Digest) (hagree : Agrees (knownOf (truncateHash parameterOutput) fixed) table) :
    Pr{let x ← (HiddenOutside.stopped (sampleModel parameterOutput highs) table
        (erase (trace (richProgramH (internalize adversary) q (truncateHash parameterOutput)
          (sampleData parameterOutput fixed highs remaining steps))))
        (knownOf (truncateHash parameterOutput) fixed) prepared.2)}[(HiddenReveal.StopOr RichWin) x] ≤
      Pr{let r ← (fixedRun (sampleModel parameterOutput highs) table
          (erase (trace (richProgramH (internalize adversary) q (truncateHash parameterOutput)
            (sampleData parameterOutput fixed highs remaining steps))))
          (DebtState.start prepared.2 (knownOf (truncateHash parameterOutput) fixed)))}[CorrectGuess table r.2 ∨
          badFor parameterOutput fixed highs remaining prepared.1 table (r.1, r.2.cache)] := by
  have htable := (agrees_iff_extending _ table).1 hagree
  refine le_trans (prEvent_mono_of_support _ _ _ fun r hr hwin => ?_)
    (stopped_le_fixedRun (sampleModel parameterOutput highs) table _ _
      (DebtState.start prepared.2 (knownOf (truncateHash parameterOutput) fixed)) hagree)
  rcases r with _ | ⟨⟨⟨res, reveals⟩, entries⟩, cacheF⟩
  · trivial
  · obtain ⟨outcome, hres, hw⟩ := hwin
    simp only at hres
    subst hres
    rcases win_implies_bad hb adversary q hq parameterOutput fixed highs remaining steps prepared hprepared table htable
      outcome reveals entries cacheF hr hw with h | h
    · exact Or.inl h
    · exact Or.inr ⟨outcome, rfl, h⟩

set_option maxRecDepth 100000 in
/-- **From the stopped experiment to the interpreted run**, honest program. -/
theorem stopped_le_interp (hb : 0 < keptHeight topLayer) (adversary : Adversary) (q : ℕ) (hq : q < 2 ^ 256)
    (parameterOutput : HashOutput) (fixed : HiddenGraph.Table) (highs : CoordinateHighs)
    (remaining : RemainingOutputs) (steps : Message → Randomness)
    (prepared : (OtsKey → Option (Counter × Encoding)) × QueryCache HashSpec)
    (hprepared : prepared ∈ support (preparation parameterOutput fixed highs remaining))
    (tg : Targeting HashInput HashOutput Coordinate) :
    Pr{let x ← (HiddenOutside.stoppedExperiment (sampleModel parameterOutput highs)
        (erase (trace (richProgramH (internalize adversary) q (truncateHash parameterOutput)
          (sampleData parameterOutput fixed highs remaining steps))))
        (knownOf (truncateHash parameterOutput) fixed) prepared.2)}[(HiddenReveal.StopOr RichWin) x] ≤
      Pr{let x ← (interp tg prepared.2 (sampleModel parameterOutput highs)
          (costGameXH (truncateHash parameterOutput) (sampleData parameterOutput fixed highs remaining steps)
            (internalize adversary)) q (DebtState.start prepared.2 (knownOf (truncateHash parameterOutput) fixed)) >>=
          fun result => (fun table => (table, result)) <$> completion result.2.known)}[CorrectGuess x.1 x.2.2 ∨
          badFor parameterOutput fixed highs remaining prepared.1 x.1 (((x.2.1.1, x.2.1.2.1), x.2.1.2.2.1), x.2.2.cache)] := by
  unfold HiddenOutside.stoppedExperiment
  rw [OracleComp.prEvent_bind_eq_tsum]
  calc _ ≤ ∑' table, Pr{let x ← completion (knownOf (truncateHash parameterOutput) fixed)}[x = table] *
        Pr{let r ← (fixedRun (sampleModel parameterOutput highs) table
            (erase (trace (richProgramH (internalize adversary) q (truncateHash parameterOutput)
              (sampleData parameterOutput fixed highs remaining steps))))
            (DebtState.start prepared.2 (knownOf (truncateHash parameterOutput) fixed)))}[CorrectGuess table r.2 ∨
            badFor parameterOutput fixed highs remaining prepared.1 table (r.1, r.2.cache)] := by
        refine ENNReal.tsum_le_tsum fun table => ?_
        by_cases htab : table ∈ support (completion (knownOf (truncateHash parameterOutput) fixed))
        · have hag : Agrees (knownOf (truncateHash parameterOutput) fixed) table := by
            unfold completion at htab
            rw [support_map] at htab
            obtain ⟨t, _, rfl⟩ := htab
            exact fun c v hc => completion_known _ c v hc t
          have := stopped_table_le hb adversary q hq parameterOutput fixed highs remaining steps prepared
            hprepared table hag
          exact mul_le_mul_right this _
        · rw [(prEvent_eq_zero_of_not_mem_support _) htab, zero_mul, zero_mul]
    _ = Pr{let x ← (withTable (fun table => fixedRun (sampleModel parameterOutput highs) table
            (erase (trace (richProgramH (internalize adversary) q (truncateHash parameterOutput)
              (sampleData parameterOutput fixed highs remaining steps))))
            (DebtState.start prepared.2 (knownOf (truncateHash parameterOutput) fixed)))
            (knownOf (truncateHash parameterOutput) fixed))}[CorrectGuess x.1 x.2.2 ∨
            badFor parameterOutput fixed highs remaining prepared.1 x.1 (x.2.1, x.2.2.cache)] := by
        unfold withTable
        rw [OracleComp.prEvent_bind_eq_tsum]
        refine tsum_congr fun table => ?_
        rw [prEvent_map]
    _ = Pr{let x ← (lazyRun (sampleModel parameterOutput highs)
            (erase (trace (richProgramH (internalize adversary) q (truncateHash parameterOutput)
              (sampleData parameterOutput fixed highs remaining steps))))
            (DebtState.start prepared.2 (knownOf (truncateHash parameterOutput) fixed)) >>= fun result =>
              (fun table => (table, result)) <$> completion result.2.known)}[CorrectGuess x.1 x.2.2 ∨
            badFor parameterOutput fixed highs remaining prepared.1 x.1 (x.2.1, x.2.2.cache)] :=
        (withTable_fixedRun _ _ _).prEvent_eq _
    _ = _ := by
        unfold richProgramH
        rw [lazyRun_wrapped tg prepared.2]
        have hcomp : ((fun out : Run HashInput Coordinate HiddenBridge.Outcome × State =>
              (((out.1.1, out.1.2.1), out.1.2.2.1), out.2)) <$>
            interp tg prepared.2 (sampleModel parameterOutput highs)
              (costGameXH (truncateHash parameterOutput) (sampleData parameterOutput fixed highs remaining steps)
                (internalize adversary)) q (DebtState.start prepared.2 (knownOf (truncateHash parameterOutput) fixed))) >>=
              (fun result => (fun table => (table, result)) <$> completion result.2.known) =
            (fun x : (Coordinate → Digest) × (Run HashInput Coordinate HiddenBridge.Outcome × State) =>
              (x.1, (((x.2.1.1, x.2.1.2.1), x.2.1.2.2.1), x.2.2))) <$>
            (interp tg prepared.2 (sampleModel parameterOutput highs)
              (costGameXH (truncateHash parameterOutput) (sampleData parameterOutput fixed highs remaining steps)
                (internalize adversary)) q (DebtState.start prepared.2 (knownOf (truncateHash parameterOutput) fixed)) >>=
              fun result => (fun table => (table, result)) <$> completion result.2.known) := by
          rw [bind_map_left, map_bind]
          refine bind_congr fun out => ?_
          rw [Functor.map_map]
        rw [hcomp, prEvent_map]

end FORS.Security.ForsPotential

end
