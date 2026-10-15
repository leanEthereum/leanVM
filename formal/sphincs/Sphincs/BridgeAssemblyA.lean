import Sphincs.BridgeImplicationA

/-! The refined classification keeps the finished, valid outcome of a winning run, as the bounds
on FORS contacts require. -/

open OracleComp OracleSpec ENNReal

namespace Sphincs.Security.HiddenBridge

open HiddenGraph

variable [Params]

/-- The refined bad event of a finished run with a valid transcript. -/
def badAV (parameterOutput : HashOutput) (fixed : HiddenGraph.Table) (highs : CoordinateHighs)
    (remaining : RemainingOutputs) (results : Index → Option (Counter × Encoding)) (table : Coordinate → Digest)
    (v : ((Option HiddenBridge.Outcome × List Coordinate) × List (HiddenCost.Entry HashInput)) × QueryCache HashSpec) :
    Prop :=
  badA parameterOutput fixed highs remaining results table v ∧
    ∃ outcome, v.1.1.1 = some outcome ∧ SigningTranscript.Valid outcome.2.1

end Sphincs.Security.HiddenBridge

namespace Sphincs.Security.ForsPotential

open Concrete HiddenGraph HiddenCost HiddenDebt GraphView Domination ForestPrice ForestSigner HiddenReveal SphincsFors.Security.Domination
open HiddenBridge Completeness SeedModel Graph Assembly Reduce Internalize

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
set_option linter.constructorNameAsVariable false
attribute [local instance] Classical.propDecidable

variable [Params]

attribute [local instance] sampleCellFintypeInst sampleCellDecEq hiddenTableSampleable highsSampleable
  remainingSampleable

set_option maxRecDepth 100000 in
/-- One table, keeping the valid outcome. -/
theorem stopped_table_leV (hb : 0 < subtreeHeight) (adversary : Adversary) (q : ℕ) (hq : q < 2 ^ 256)
    (parameterOutput : HashOutput) (fixed : HiddenGraph.Table) (highs : CoordinateHighs)
    (remaining : RemainingOutputs)
    (prepared : (Index → Option (Counter × Encoding)) × QueryCache HashSpec)
    (hprepared : prepared ∈ support (preparation parameterOutput fixed highs remaining))
    (known : Knowledge Coordinate)
    (hknownOf : ∀ c v, knownOf (truncateHash parameterOutput) fixed c = some v → known c = some v)
    (hknown : ∀ c v, known c = some v →
      knownOf (truncateHash parameterOutput) fixed c = some v ∨ AboveWord (truncateHash parameterOutput) prepared.1 c)
    (table : Coordinate → Digest) (hagree : Agrees known table) :
    Pr[HiddenReveal.StopOr RichWin | HiddenOutside.stopped (sampleModel parameterOutput highs) table
        (erase (trace (richProgram (internalize adversary) q (truncateHash parameterOutput)
          (sampleData parameterOutput fixed highs remaining))))
        known prepared.2] ≤
      Pr[fun r => CorrectGuess table r.2 ∨
          badAV parameterOutput fixed highs remaining prepared.1 table (r.1, r.2.cache) |
        fixedRun (sampleModel parameterOutput highs) table
          (erase (trace (richProgram (internalize adversary) q (truncateHash parameterOutput)
            (sampleData parameterOutput fixed highs remaining))))
          (DebtState.start prepared.2 known)] := by
  have htable := (agrees_iff_extending _ table).1 hagree
  refine le_trans (probEvent_mono fun r hr hwin => ?_)
    (stopped_le_fixedRun (sampleModel parameterOutput highs) table _ _
      (DebtState.start prepared.2 known) hagree)
  rcases r with _ | ⟨⟨⟨res, reveals⟩, entries⟩, cacheF⟩
  · trivial
  · obtain ⟨outcome, hres, hw⟩ := hwin
    simp only at hres
    subst hres
    refine ⟨win_implies_badA hb adversary q hq parameterOutput fixed highs remaining prepared hprepared known
      hknownOf hknown table htable outcome reveals entries cacheF hr hw, outcome, rfl, ?_⟩
    simp only [outcomeWins, Bool.and_eq_true, decide_eq_true_eq] at hw
    exact hw.1.1

set_option maxRecDepth 100000 in
/-- **From the stopped experiment with exposed knowledge to the interpreted run.** -/
theorem stopped_le_interpV (hb : 0 < subtreeHeight) (adversary : Adversary) (q : ℕ) (hq : q < 2 ^ 256)
    (parameterOutput : HashOutput) (fixed : HiddenGraph.Table) (highs : CoordinateHighs)
    (remaining : RemainingOutputs)
    (prepared : (Index → Option (Counter × Encoding)) × QueryCache HashSpec)
    (hprepared : prepared ∈ support (preparation parameterOutput fixed highs remaining))
    (tg : Targeting HashInput HashOutput Coordinate)
    (known : Knowledge Coordinate)
    (hknownOf : ∀ c v, knownOf (truncateHash parameterOutput) fixed c = some v → known c = some v)
    (hknown : ∀ c v, known c = some v →
      knownOf (truncateHash parameterOutput) fixed c = some v ∨ AboveWord (truncateHash parameterOutput) prepared.1 c) :
    Pr[HiddenReveal.StopOr RichWin | HiddenOutside.stoppedExperiment (sampleModel parameterOutput highs)
        (erase (trace (richProgram (internalize adversary) q (truncateHash parameterOutput)
          (sampleData parameterOutput fixed highs remaining))))
        known prepared.2] ≤
      Pr[fun x => CorrectGuess x.1 x.2.2 ∨
          badAV parameterOutput fixed highs remaining prepared.1 x.1
            (((x.2.1.1, x.2.1.2.1), x.2.1.2.2.1), x.2.2.cache) |
        interp tg prepared.2 (sampleModel parameterOutput highs)
          (costGameX (truncateHash parameterOutput) (sampleData parameterOutput fixed highs remaining)
            (internalize adversary)) q (DebtState.start prepared.2 known) >>=
          fun result => (fun table => (table, result)) <$> completion result.2.known] := by
  unfold HiddenOutside.stoppedExperiment
  rw [probEvent_bind_eq_tsum]
  calc _ ≤ ∑' table, Pr[= table | completion known] *
        Pr[fun r => CorrectGuess table r.2 ∨
            badAV parameterOutput fixed highs remaining prepared.1 table (r.1, r.2.cache) |
          fixedRun (sampleModel parameterOutput highs) table
            (erase (trace (richProgram (internalize adversary) q (truncateHash parameterOutput)
              (sampleData parameterOutput fixed highs remaining))))
            (DebtState.start prepared.2 known)] := by
        refine ENNReal.tsum_le_tsum fun table => ?_
        by_cases htab : table ∈ support (completion known)
        · have hag : Agrees known table := by
            unfold completion at htab
            rw [support_map] at htab
            obtain ⟨t, _, rfl⟩ := htab
            exact fun c v hc => completion_known _ c v hc t
          have := stopped_table_leV hb adversary q hq parameterOutput fixed highs remaining prepared
            hprepared known hknownOf hknown table hag
          exact mul_le_mul_right this _
        · rw [probOutput_eq_zero_of_not_mem_support htab, zero_mul, zero_mul]
    _ = Pr[fun x => CorrectGuess x.1 x.2.2 ∨
            badAV parameterOutput fixed highs remaining prepared.1 x.1 (x.2.1, x.2.2.cache) |
          withTable (fun table => fixedRun (sampleModel parameterOutput highs) table
            (erase (trace (richProgram (internalize adversary) q (truncateHash parameterOutput)
              (sampleData parameterOutput fixed highs remaining))))
            (DebtState.start prepared.2 known)) known] := by
        unfold withTable
        rw [probEvent_bind_eq_tsum]
        refine tsum_congr fun table => ?_
        rw [probEvent_map]
        rfl
    _ = Pr[fun x => CorrectGuess x.1 x.2.2 ∨
            badAV parameterOutput fixed highs remaining prepared.1 x.1 (x.2.1, x.2.2.cache) |
          lazyRun (sampleModel parameterOutput highs)
            (erase (trace (richProgram (internalize adversary) q (truncateHash parameterOutput)
              (sampleData parameterOutput fixed highs remaining))))
            (DebtState.start prepared.2 known) >>= fun result =>
              (fun table => (table, result)) <$> completion result.2.known] :=
        probEvent_congr' (fun _ _ => Iff.rfl) (withTable_fixedRun _ _ _)
    _ = _ := by
        unfold richProgram
        rw [lazyRun_wrapped tg prepared.2]
        have hcomp : ((fun out : Run HashInput Coordinate HiddenBridge.Outcome × State =>
              (((out.1.1, out.1.2.1), out.1.2.2.1), out.2)) <$>
            interp tg prepared.2 (sampleModel parameterOutput highs)
              (costGameX (truncateHash parameterOutput) (sampleData parameterOutput fixed highs remaining)
                (internalize adversary)) q (DebtState.start prepared.2 known)) >>=
              (fun result => (fun table => (table, result)) <$> completion result.2.known) =
            (fun x : (Coordinate → Digest) × (Run HashInput Coordinate HiddenBridge.Outcome × State) =>
              (x.1, (((x.2.1.1, x.2.1.2.1), x.2.1.2.2.1), x.2.2))) <$>
            (interp tg prepared.2 (sampleModel parameterOutput highs)
              (costGameX (truncateHash parameterOutput) (sampleData parameterOutput fixed highs remaining)
                (internalize adversary)) q (DebtState.start prepared.2 known) >>=
              fun result => (fun table => (table, result)) <$> completion result.2.known) := by
          rw [bind_map_left, map_bind]
          refine bind_congr fun out => ?_
          rw [Functor.map_map]
        rw [hcomp, probEvent_map]
        rfl

set_option maxRecDepth 100000 in
/-- **From the stopped experiment with the above-word exposure to the interpreted run.** -/
theorem stopped_le_interp_exposeV (hb : 0 < subtreeHeight) (adversary : Adversary) (q : ℕ) (hq : q < 2 ^ 256)
    (parameterOutput : HashOutput) (fixed : HiddenGraph.Table) (highs : CoordinateHighs)
    (remaining : RemainingOutputs)
    (prepared : (Index → Option (Counter × Encoding)) × QueryCache HashSpec)
    (hprepared : prepared ∈ support (preparation parameterOutput fixed highs remaining))
    (tg : Targeting HashInput HashOutput Coordinate) (known : Knowledge Coordinate)
    (hk : known ∈ support (exposeR (aboveList (truncateHash parameterOutput) prepared.1)
      (knownOf (truncateHash parameterOutput) fixed))) :
    Pr[HiddenReveal.StopOr RichWin | HiddenOutside.stoppedExperiment (sampleModel parameterOutput highs)
        (erase (trace (richProgram (internalize adversary) q (truncateHash parameterOutput)
          (sampleData parameterOutput fixed highs remaining))))
        known prepared.2] ≤
      Pr[fun x => CorrectGuess x.1 x.2.2 ∨
          badAV parameterOutput fixed highs remaining prepared.1 x.1
            (((x.2.1.1, x.2.1.2.1), x.2.1.2.2.1), x.2.2.cache) |
        interp tg prepared.2 (sampleModel parameterOutput highs)
          (costGameX (truncateHash parameterOutput) (sampleData parameterOutput fixed highs remaining)
            (internalize adversary)) q (DebtState.start prepared.2 known) >>=
          fun result => (fun table => (table, result)) <$> completion result.2.known] :=
  stopped_le_interpV hb adversary q hq parameterOutput fixed highs remaining prepared hprepared tg known
    (expose_known_support _ fixed prepared.1 known hk).1 (expose_known_support _ fixed prepared.1 known hk).2

end Sphincs.Security.ForsPotential
