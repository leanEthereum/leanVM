module

public import FORS.SmallBudget.ClosingH
public import FORS.LargeBudget.RouteStartH
public import FORS.Classification.RefinedOutcome

@[expose] public section

/-! **The small route's program bridge, the signer honest** (`SmallBridgeH`): the honest seed-free
experiment in the stopped prepared world with the above-word values exposed (`seedFree_le_exposeP`,
as `seedFree_le_exposeP`), then in the interpreted honest game (`stopped_le_interp_exposeV`, as
`stopped_le_interp_exposeV`). The refined win implication carries over through the coupling of the
honest program with the charged one (`stopped_richH`), the seed avoided by the recorded inputs of a
seed's length (`win_implies_badAM`). -/

open OracleComp OracleSpec ENNReal

namespace FORS.Security.HiddenBridge

variable [Params]

open Concrete Completeness _root_.FORS.Security.Graph GraphCorrectness TargetAssignment HiddenGraph Assembly SeedModel
  Reduce Eager

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
set_option linter.constructorNameAsVariable false
attribute [local instance] Classical.propDecidable

attribute [local irreducible] ReferenceChoice.selection encodingAttemptLimit

/-- **Refined win implication at any budget**, the seed avoided by the recorded inputs of a seed's
length alone (`win_implies_badA` with `seedMarks` in place of the budget). In every non-stopped lazy run of the rich program from
knowledge that contains the fixed knowledge and otherwise only above-word chain values, a
winning outcome yields the refined bad event of the table. -/
theorem win_implies_badAM (hb : 0 < keptHeight topLayer) (adversary : Adversary) (q : Nat)
    (parameterOutput : HashOutput) (fixed : HiddenGraph.Table) (highs : CoordinateHighs)
    (remaining : RemainingOutputs) (steps : Message → Randomness)
    (prepared : (OtsKey → Option (Counter × Encoding)) × QueryCache HashSpec)
    (hprepared : prepared ∈ support (preparation parameterOutput fixed highs remaining))
    (known : HiddenReveal.Knowledge Coordinate)
    (hknownOf : ∀ c v, knownOf (truncateHash parameterOutput) fixed c = some v → known c = some v)
    (hknown : ∀ c v, known c = some v →
      knownOf (truncateHash parameterOutput) fixed c = some v ∨ AboveWord (truncateHash parameterOutput) prepared.1 c)
    (table : HiddenGraph.Table) (htable : tableExtending known table = table)
    (outcome : Outcome) (reveals : List Coordinate) (entries : List (HiddenCost.Entry HashInput))
    (cacheF : QueryCache HashSpec)
    (hstop : some (((some outcome, reveals), entries), cacheF) ∈ support
      (HiddenOutside.stopped (sampleModel parameterOutput highs) table
        (HiddenCost.erase (HiddenCost.trace (richProgram (Internalize.internalize adversary) q
          (truncateHash parameterOutput) (sampleData parameterOutput fixed highs remaining steps))))
        known prepared.2))
    (hwin : outcomeWins outcome = true) (hmarks : seedMarks entries < 2 ^ 256) :
    badA parameterOutput fixed highs remaining prepared.1 table (((some outcome, reveals), entries), cacheF) := by
  have htable' : tableExtending (knownOf (truncateHash parameterOutput) fixed) table = table := by
    have hag := (ForsPotential.agrees_iff_extending known table).2 htable
    exact (ForsPotential.agrees_iff_extending _ table).1 fun c v hc => hag c v (hknownOf c v hc)
  obtain ⟨hgrow, hrun, hguess⟩ := lazy_support (sampleModel parameterOutput highs) table _
    known prepared.2 cacheF _ entries hstop
  obtain ⟨-, hcached⟩ := lazy_cached (sampleModel parameterOutput highs) table _
    known prepared.2 cacheF _ entries hstop
  have hOnly : OnlyC (richProgram (Internalize.internalize adversary) q (truncateHash parameterOutput)
      (sampleData parameterOutput fixed highs remaining steps)) :=
    OnlyC.withReveals (OnlyC.cap (OnlyC.costGameX _ _ adversary) q)
  have hshortE := costRun_entries_short _ table _ hOnly _ hrun
  obtain ⟨seed, hseed⟩ := exists_seed_avoiding _ hmarks
  have hseed' : ∀ input, Sum.inl input ∈ entries → ¬SeedGuess.SeedHit input seed := fun input hinput hhit =>
    hseed input (List.mem_filter.2 ⟨List.mem_filterMap.mpr ⟨_, hinput, rfl⟩,
      decide_eq_true ((Stop.seedHit_length hhit).symm.imp id id)⟩) hhit
  have hstructPrep := (preparation_support _ _ _ prepared hprepared
    (preferCache prepared.2 (sampleFn (materialT parameterOutput fixed highs remaining table) seed
      (answersT parameterOutput fixed highs remaining table) (finalTable parameterOutput highs table cacheF)))
    (preferCache_agrees _ _))
  have hstruct : ∀ input answer, structCache (splitMaterial parameterOutput highs remaining fixed)
      (splitAnswers highs remaining fixed) input = some answer → cacheF input = some answer :=
    fun input answer h => hgrow input answer (hstructPrep.1 h)
  have hagreeAll := sampleFn_final parameterOutput fixed highs remaining table htable' cacheF seed hstruct
  have hagree : ∀ input, Sum.inl input ∈ entries →
      sampleFn (materialT parameterOutput fixed highs remaining table) seed
        (answersT parameterOutput fixed highs remaining table) (finalTable parameterOutput highs table cacheF) input =
      finalFn (sampleModel parameterOutput highs) table cacheF input :=
    fun input hinput => hagreeAll input (hshortE input hinput) (hseed' input hinput)
  set f' := sampleFn (materialT parameterOutput fixed highs remaining table) seed
    (answersT parameterOutput fixed highs remaining table) (finalTable parameterOutput highs table cacheF) with hf'
  have hrun' := costRun_support_congr _ f' table _ _ hrun (fun input hinput => (hagree input hinput).symm)
  have hagreement := sample_agreement (materialT parameterOutput fixed highs remaining table) seed
    (answersT parameterOutput fixed highs remaining table) (finalTable parameterOutput highs table cacheF)
  have hcons := sample_consistent (materialT parameterOutput fixed highs remaining table) seed
    (answersT parameterOutput fixed highs remaining table) (finalTable parameterOutput highs table cacheF)
  have hbound := sample_boundary (materialT parameterOutput fixed highs remaining table) seed
    (answersT parameterOutput fixed highs remaining table) (finalTable parameterOutput highs table cacheF)
  have hdata : GraphView.DataCorrect f' (truncateHash parameterOutput) seed
      (sampleData parameterOutput fixed highs remaining steps) := by
    have h := GraphView.publicData_correct f' _ seed _ hcons hbound steps
    rwa [publicData_T] at h
  have hcoord : GraphView.CoordinatesCorrect f' (truncateHash parameterOutput) seed table := by
    have h := GraphView.coordinates_correct f' _ seed _ hcons
    have heq := (Reduce.sampleCoordinates_eq (materialT parameterOutput fixed highs remaining table) seed
      (answersT parameterOutput fixed highs remaining table) (finalTable parameterOutput highs table cacheF)).trans
      (graphCoordinates_T parameterOutput fixed highs remaining table htable')
    unfold Assembly.sampleCoordinates at heq
    rwa [heq] at h
  obtain ⟨hverified, htrace, hgood⟩ := rich_support f' table (Internalize.internalize adversary) q
    (truncateHash parameterOutput) seed (sampleData parameterOutput fixed highs remaining steps) hdata hcoord
    outcome reveals entries hrun'
  have hsigned := rich_revealed f' table (Internalize.internalize adversary) q (truncateHash parameterOutput)
    (sampleData parameterOutput fixed highs remaining steps) outcome reveals entries hrun'
  have hencAgree : ∀ (key : OtsKey) (counter : Counter),
      f' (Wots.encodingInput (truncateHash parameterOutput) key.1 key.2.1 key.2.2
        (keyMessages (sampleData parameterOutput fixed highs remaining) key) counter) =
      preferCache prepared.2 f' (Wots.encodingInput (truncateHash parameterOutput) key.1 key.2.1 key.2.2
        (keyMessages (sampleData parameterOutput fixed highs remaining) key) counter) :=
    fun key counter => encoding_preferCache parameterOutput highs table cacheF prepared.2 f' seed
      (fun input hshort hnot => hagreeAll input hshort hnot) hgrow _ _ _ _
      (shortMessage_keyMessage _ _ _ _) counter
  have hselection := selection_of_agree (truncateHash parameterOutput)
    (keyMessages (sampleData parameterOutput fixed highs remaining)) prepared.1 f' (preferCache prepared.2 f')
    hstructPrep.2 hencAgree
  have hfull := fullTable_eq parameterOutput fixed highs remaining table prepared.1 f' seed hagreement
    hselection
  have hword : ∀ key : OtsKey, PrunedGraph.KeyActive (truncateHash parameterOutput) key.1 key.2.1 key.2.2 →
      ReferenceChoice.word f' (truncateHash parameterOutput) key.1 key.2.1 key.2.2
        (SignatureWitness.keyMessageValue f' (truncateHash parameterOutput) seed key) =
      preparedWord prepared.1 key := by
    intro key hactive
    have hmsg : SignatureWitness.keyMessageValue f' (truncateHash parameterOutput) seed key =
        keyMessages (sampleData parameterOutput fixed highs remaining) key :=
      (hdata.keyMessage key.1 key.2.1 key.2.2 hactive).symm
    unfold ReferenceChoice.word preparedWord
    rw [hmsg, hselection key]
  obtain ⟨forgery, log, verified⟩ := outcome
  simp only [outcomeWins, Bool.and_eq_true, decide_eq_true_eq] at hwin
  obtain ⟨⟨hvalid, hnotContains⟩, rfl⟩ := hwin
  exact badA_of_accepted hb parameterOutput fixed highs remaining steps table htable' prepared.1 cacheF reveals entries
    f' seed hcons hbound hdata hcoord hfull hword hagree hcached known hknown hguess forgery log
    htrace hgood hsigned hverified.symm hvalid hnotContains

/-! ### Exposed knowledge -/

/-- **Refined win implication, the signer honest**: a finished stopped run of the honest program is
one of the charged program at a budget it cannot exhaust (`stopped_richH`), whose seed-length
recorded inputs the honest budget bounds. -/
theorem win_implies_badA (hb : 0 < keptHeight topLayer) (adversary : Adversary) (q : Nat) (hq : q < 2 ^ 256)
    (parameterOutput : HashOutput) (fixed : HiddenGraph.Table) (highs : CoordinateHighs)
    (remaining : RemainingOutputs) (steps : Message → Randomness)
    (prepared : (OtsKey → Option (Counter × Encoding)) × QueryCache HashSpec)
    (hprepared : prepared ∈ support (preparation parameterOutput fixed highs remaining))
    (known : HiddenReveal.Knowledge Coordinate)
    (hknownOf : ∀ c v, knownOf (truncateHash parameterOutput) fixed c = some v → known c = some v)
    (hknown : ∀ c v, known c = some v →
      knownOf (truncateHash parameterOutput) fixed c = some v ∨ AboveWord (truncateHash parameterOutput) prepared.1 c)
    (table : HiddenGraph.Table) (htable : tableExtending known table = table)
    (outcome : Outcome) (reveals : List Coordinate) (entries : List (HiddenCost.Entry HashInput))
    (cacheF : QueryCache HashSpec)
    (hstop : some (((some outcome, reveals), entries), cacheF) ∈ support
      (HiddenOutside.stopped (sampleModel parameterOutput highs) table
        (HiddenCost.erase (HiddenCost.trace (richProgramH (Internalize.internalize adversary) q
          (truncateHash parameterOutput) (sampleData parameterOutput fixed highs remaining steps))))
        known prepared.2))
    (hwin : outcomeWins outcome = true) :
    badA parameterOutput fixed highs remaining prepared.1 table (((some outcome, reveals), entries), cacheF) := by
  obtain ⟨budget, entries', hmarks, hstop'⟩ := stopped_richH _ table _ q _ _ _ _ outcome reveals entries cacheF hstop
  exact win_implies_badAM hb adversary budget parameterOutput fixed highs remaining steps prepared hprepared known
    hknownOf hknown table htable outcome reveals entries' cacheF hstop' hwin (lt_of_le_of_lt hmarks hq)

end FORS.Security.HiddenBridge

namespace FORS.Security.HiddenBridge

variable [Params]

open HiddenReveal HiddenCost Eager Short Concrete Stop
open Completeness SeedModel _root_.FORS.Security.Graph Assembly Reduce HiddenGraph Internalize GraphView

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
set_option linter.constructorNameAsVariable false
attribute [local instance] Classical.propDecidable

attribute [local instance] sampleCellFintypeInst sampleCellDecEq hiddenTableSampleable highsSampleable
  remainingSampleable

/-- **Seed-free to stopped, with exposure.** The stopped experiment may start from the known
coordinates together with any list of table coordinates, chosen from the public, structural and
outside samples. -/
theorem seedFree_le_expose (adversary : Adversary) (q : Nat) (steps : Message → Randomness)
    (event : Option Bool × List (HiddenCost.Entry HashInput) → Prop)
    (cs : HashOutput → HiddenGraph.Table → CoordinateHighs → RemainingOutputs → Eager.Table → List Coordinate) :
    Pr{let z ← AdvCount.seedFreeExperiment adversary q steps}[event z] ≤
      Pr{let z ← (do
        let parameterOutput ← $ᵗ HashOutput
        let fixed ← $ᵗ HiddenGraph.Table
        let highs ← $ᵗ CoordinateHighs
        let remaining ← $ᵗ RemainingOutputs
        let outsideTable ← $ᵗ Eager.Table
        let known ← exposeR (cs parameterOutput fixed highs remaining outsideTable)
          (knownOf (truncateHash parameterOutput) fixed)
        HiddenRows.stoppedExperiment (sampleModel parameterOutput highs)
          (outsideFn (splitMaterial parameterOutput highs remaining fixed)
            (splitAnswers highs remaining fixed) outsideTable)
          (HiddenCost.erase (HiddenCost.trace
            (sampleProgram adversary q steps parameterOutput fixed highs remaining)))
          known)}[(HiddenReveal.StopOr event) z] := by
  rw [(evalDist_seedFree_completion adversary q steps).prEvent_eq]
  refine probEvent_bind_mono_support _ _ _ _ _ fun parameterOutput _ => ?_
  refine probEvent_bind_mono_support _ _ _ _ _ fun fixed _ => ?_
  refine probEvent_bind_mono_support _ _ _ _ _ fun highs _ => ?_
  refine probEvent_bind_mono_support _ _ _ _ _ fun remaining _ => ?_
  refine probEvent_bind_mono_support _ _ _ _ _ fun outsideTable _ => ?_
  unfold HiddenRows.stoppedExperiment
  rw [(evalDist_completion_exposeT
    (fun table known => HiddenRows.stopped (sampleModel parameterOutput highs) table
      (outsideFn (splitMaterial parameterOutput highs remaining fixed)
        (splitAnswers highs remaining fixed) outsideTable)
      (HiddenCost.erase (HiddenCost.trace (sampleProgram adversary q steps parameterOutput fixed highs remaining)))
      known)
    (cs parameterOutput fixed highs remaining outsideTable) (knownOf (truncateHash parameterOutput) fixed)).symm.prEvent_eq]
  refine probEvent_bind_mono_support _ _ _ _ _ fun table htable => ?_
  have hagree : HiddenRows.KnownAgrees table (knownOf (truncateHash parameterOutput) fixed) := by
    unfold completion at htable
    rw [support_map] at htable
    obtain ⟨t, _, rfl⟩ := htable
    exact HiddenRows.knownAgrees_completion _ t
  rw [hiddenRunH_eq]
  exact costRunH_le_stopped (sampleModel parameterOutput highs) table
    (outsideFn (splitMaterial parameterOutput highs remaining fixed) (splitAnswers highs remaining fixed) outsideTable)
    (sampleProgram adversary q steps parameterOutput fixed highs remaining) _
    (knownAgrees_exposeT table _ _ hagree) event


set_option maxRecDepth 100000 in
/-- **The seed-free win in the stopped prepared world, with the above-word values exposed.** -/
theorem seedFree_le_exposeP (adversary : Adversary) (q : Nat) (steps : Message → Randomness) :
    Pr{let z ← AdvCount.seedFreeExperiment (internalize adversary) q steps}[Win z] ≤
      Pr{let z ← (do
        let parameterOutput ← $ᵗ HashOutput
        let fixed ← $ᵗ HiddenGraph.Table
        let highs ← $ᵗ CoordinateHighs
        let remaining ← $ᵗ RemainingOutputs
        let prepared ← preparation parameterOutput fixed highs remaining
        let known ← exposeR (aboveList (truncateHash parameterOutput) prepared.1)
          (knownOf (truncateHash parameterOutput) fixed)
        HiddenOutside.stoppedExperiment (sampleModel parameterOutput highs)
          (erase (trace (richProgramH (internalize adversary) q (truncateHash parameterOutput)
            (sampleData parameterOutput fixed highs remaining steps))))
          known prepared.2)}[(HiddenReveal.StopOr RichWin) z] := by
  refine (seedFree_le_expose (internalize adversary) q steps Win
    (fun parameterOutput fixed highs remaining outsideTable =>
      aboveList (truncateHash parameterOutput)
        (resultsOf (truncateHash parameterOutput) (keyMessages (sampleData parameterOutput fixed highs remaining))
          (outsideFn (splitMaterial parameterOutput highs remaining fixed)
            (splitAnswers highs remaining fixed) outsideTable)))).trans (le_of_eq ?_)
  refine probEvent_bind_congr₂ _ _ _ _ _ fun parameterOutput => ?_
  refine probEvent_bind_congr₂ _ _ _ _ _ fun fixed => ?_
  refine probEvent_bind_congr₂ _ _ _ _ _ fun highs => ?_
  refine probEvent_bind_congr₂ _ _ _ _ _ fun remaining => ?_
  have hprog0 : sampleProgram (internalize adversary) q steps parameterOutput fixed highs remaining =
      (fun result => Option.map outcomeWins result.1) <$> richProgramH (internalize adversary) q
        (truncateHash parameterOutput) (sampleData parameterOutput fixed highs remaining steps) :=
    cap_costGameH_eq _ _ _ _
  have hshort : OnlyShort (HiddenCost.erase (HiddenCost.trace
      (sampleProgram (internalize adversary) q steps parameterOutput fixed highs remaining))) := by
    rw [hprog0, trace_map, erase_map]
    exact (isQueryBoundP_map_iff _ _ _).2 (onlyShort_richProgramH _ q _ _)
  unfold outsideFn
  rw [(evalDist_expose_prep (sampleModel parameterOutput highs) _ (truncateHash parameterOutput)
      (keyMessages (sampleData parameterOutput fixed highs remaining))
      (fun key => shortMessage_keyMessage _ _ _ _) _ hshort _
      (aboveList (truncateHash parameterOutput))).prEvent_eq]
  refine probEvent_bind_congr₂ _ _ _ _ _ fun prepared => ?_
  refine probEvent_bind_congr₂ _ _ _ _ _ fun known => ?_
  rw [probEvent_stopOr_map]
  unfold HiddenOutside.stoppedExperiment
  refine probEvent_bind_congr₂ _ _ _ _ _ fun table => ?_
  have hprog : sampleProgram (internalize adversary) q steps parameterOutput fixed highs remaining =
      (fun result => Option.map outcomeWins result.1) <$> richProgramH (internalize adversary) q
        (truncateHash parameterOutput) (sampleData parameterOutput fixed highs remaining steps) :=
    cap_costGameH_eq _ _ _ _
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

set_option maxRecDepth 100000 in
/-- One table, keeping the valid outcome, the signer honest. -/
theorem stopped_table_leV (hb : 0 < keptHeight topLayer) (adversary : Adversary) (q : ℕ) (hq : q < 2 ^ 256)
    (parameterOutput : HashOutput) (fixed : HiddenGraph.Table) (highs : CoordinateHighs)
    (remaining : RemainingOutputs) (steps : Message → Randomness)
    (prepared : (OtsKey → Option (Counter × Encoding)) × QueryCache HashSpec)
    (hprepared : prepared ∈ support (preparation parameterOutput fixed highs remaining))
    (known : Knowledge Coordinate)
    (hknownOf : ∀ c v, knownOf (truncateHash parameterOutput) fixed c = some v → known c = some v)
    (hknown : ∀ c v, known c = some v →
      knownOf (truncateHash parameterOutput) fixed c = some v ∨ AboveWord (truncateHash parameterOutput) prepared.1 c)
    (table : Coordinate → Digest) (hagree : Agrees known table) :
    Pr{let x ← (HiddenOutside.stopped (sampleModel parameterOutput highs) table
        (erase (trace (richProgramH (internalize adversary) q (truncateHash parameterOutput)
          (sampleData parameterOutput fixed highs remaining steps))))
        known prepared.2)}[(HiddenReveal.StopOr RichWin) x] ≤
      Pr{let r ← (fixedRun (sampleModel parameterOutput highs) table
          (erase (trace (richProgramH (internalize adversary) q (truncateHash parameterOutput)
            (sampleData parameterOutput fixed highs remaining steps))))
          (DebtState.start prepared.2 known))}[CorrectGuess table r.2 ∨
          badAV parameterOutput fixed highs remaining prepared.1 table (r.1, r.2.cache)] := by
  have htable := (agrees_iff_extending _ table).1 hagree
  refine le_trans (prEvent_mono_of_support _ _ _ fun r hr hwin => ?_)
    (stopped_le_fixedRun (sampleModel parameterOutput highs) table _ _
      (DebtState.start prepared.2 known) hagree)
  rcases r with _ | ⟨⟨⟨res, reveals⟩, entries⟩, cacheF⟩
  · trivial
  · obtain ⟨outcome, hres, hw⟩ := hwin
    simp only at hres
    subst hres
    refine ⟨win_implies_badA hb adversary q hq parameterOutput fixed highs remaining steps prepared hprepared known
      hknownOf hknown table htable outcome reveals entries cacheF hr hw, outcome, rfl, ?_⟩
    simp only [outcomeWins, Bool.and_eq_true, decide_eq_true_eq] at hw
    exact hw.1.1

set_option maxRecDepth 100000 in
/-- **From the stopped experiment with exposed knowledge to the interpreted run.** -/
theorem stopped_le_interpV (hb : 0 < keptHeight topLayer) (adversary : Adversary) (q : ℕ) (hq : q < 2 ^ 256)
    (parameterOutput : HashOutput) (fixed : HiddenGraph.Table) (highs : CoordinateHighs)
    (remaining : RemainingOutputs) (steps : Message → Randomness)
    (prepared : (OtsKey → Option (Counter × Encoding)) × QueryCache HashSpec)
    (hprepared : prepared ∈ support (preparation parameterOutput fixed highs remaining))
    (tg : Targeting HashInput HashOutput Coordinate)
    (known : Knowledge Coordinate)
    (hknownOf : ∀ c v, knownOf (truncateHash parameterOutput) fixed c = some v → known c = some v)
    (hknown : ∀ c v, known c = some v →
      knownOf (truncateHash parameterOutput) fixed c = some v ∨ AboveWord (truncateHash parameterOutput) prepared.1 c) :
    Pr{let x ← (HiddenOutside.stoppedExperiment (sampleModel parameterOutput highs)
        (erase (trace (richProgramH (internalize adversary) q (truncateHash parameterOutput)
          (sampleData parameterOutput fixed highs remaining steps))))
        known prepared.2)}[(HiddenReveal.StopOr RichWin) x] ≤
      Pr{let x ← (interp tg prepared.2 (sampleModel parameterOutput highs)
          (ForsPotential.costGameXH (truncateHash parameterOutput) (sampleData parameterOutput fixed highs remaining steps)
            (internalize adversary)) q (DebtState.start prepared.2 known) >>=
          fun result => (fun table => (table, result)) <$> completion result.2.known)}[CorrectGuess x.1 x.2.2 ∨
          badAV parameterOutput fixed highs remaining prepared.1 x.1
            (((x.2.1.1, x.2.1.2.1), x.2.1.2.2.1), x.2.2.cache)] := by
  unfold HiddenOutside.stoppedExperiment
  rw [OracleComp.prEvent_bind_eq_tsum]
  calc _ ≤ ∑' table, Pr{let x ← completion known}[x = table] *
        Pr{let r ← (fixedRun (sampleModel parameterOutput highs) table
            (erase (trace (richProgramH (internalize adversary) q (truncateHash parameterOutput)
              (sampleData parameterOutput fixed highs remaining steps))))
            (DebtState.start prepared.2 known))}[CorrectGuess table r.2 ∨
            badAV parameterOutput fixed highs remaining prepared.1 table (r.1, r.2.cache)] := by
        refine ENNReal.tsum_le_tsum fun table => ?_
        by_cases htab : table ∈ support (completion known)
        · have hag : Agrees known table := by
            unfold completion at htab
            rw [support_map] at htab
            obtain ⟨t, _, rfl⟩ := htab
            exact fun c v hc => completion_known _ c v hc t
          have := stopped_table_leV hb adversary q hq parameterOutput fixed highs remaining steps prepared
            hprepared known hknownOf hknown table hag
          exact mul_le_mul_right this _
        · rw [(prEvent_eq_zero_of_not_mem_support _) htab, zero_mul, zero_mul]
    _ = Pr{let x ← (withTable (fun table => fixedRun (sampleModel parameterOutput highs) table
            (erase (trace (richProgramH (internalize adversary) q (truncateHash parameterOutput)
              (sampleData parameterOutput fixed highs remaining steps))))
            (DebtState.start prepared.2 known)) known)}[CorrectGuess x.1 x.2.2 ∨
            badAV parameterOutput fixed highs remaining prepared.1 x.1 (x.2.1, x.2.2.cache)] := by
        unfold withTable
        rw [OracleComp.prEvent_bind_eq_tsum]
        refine tsum_congr fun table => ?_
        rw [prEvent_map]
    _ = Pr{let x ← (lazyRun (sampleModel parameterOutput highs)
            (erase (trace (richProgramH (internalize adversary) q (truncateHash parameterOutput)
              (sampleData parameterOutput fixed highs remaining steps))))
            (DebtState.start prepared.2 known) >>= fun result =>
              (fun table => (table, result)) <$> completion result.2.known)}[CorrectGuess x.1 x.2.2 ∨
            badAV parameterOutput fixed highs remaining prepared.1 x.1 (x.2.1, x.2.2.cache)] :=
        (withTable_fixedRun _ _ _).prEvent_eq _
    _ = _ := by
        unfold richProgramH
        rw [lazyRun_wrapped tg prepared.2]
        have hcomp : ((fun out : Run HashInput Coordinate HiddenBridge.Outcome × State =>
              (((out.1.1, out.1.2.1), out.1.2.2.1), out.2)) <$>
            interp tg prepared.2 (sampleModel parameterOutput highs)
              (ForsPotential.costGameXH (truncateHash parameterOutput) (sampleData parameterOutput fixed highs remaining steps)
                (internalize adversary)) q (DebtState.start prepared.2 known)) >>=
              (fun result => (fun table => (table, result)) <$> completion result.2.known) =
            (fun x : (Coordinate → Digest) × (Run HashInput Coordinate HiddenBridge.Outcome × State) =>
              (x.1, (((x.2.1.1, x.2.1.2.1), x.2.1.2.2.1), x.2.2))) <$>
            (interp tg prepared.2 (sampleModel parameterOutput highs)
              (ForsPotential.costGameXH (truncateHash parameterOutput) (sampleData parameterOutput fixed highs remaining steps)
                (internalize adversary)) q (DebtState.start prepared.2 known) >>=
              fun result => (fun table => (table, result)) <$> completion result.2.known) := by
          rw [bind_map_left, map_bind]
          refine bind_congr fun out => ?_
          rw [Functor.map_map]
        rw [hcomp, prEvent_map]

set_option maxRecDepth 100000 in
/-- **From the stopped experiment with the above-word exposure to the interpreted run.** -/
theorem stopped_le_interp_exposeV (hb : 0 < keptHeight topLayer) (adversary : Adversary) (q : ℕ) (hq : q < 2 ^ 256)
    (parameterOutput : HashOutput) (fixed : HiddenGraph.Table) (highs : CoordinateHighs)
    (remaining : RemainingOutputs) (steps : Message → Randomness)
    (prepared : (OtsKey → Option (Counter × Encoding)) × QueryCache HashSpec)
    (hprepared : prepared ∈ support (preparation parameterOutput fixed highs remaining))
    (tg : Targeting HashInput HashOutput Coordinate) (known : Knowledge Coordinate)
    (hk : known ∈ support (exposeR (aboveList (truncateHash parameterOutput) prepared.1)
      (knownOf (truncateHash parameterOutput) fixed))) :
    Pr{let x ← (HiddenOutside.stoppedExperiment (sampleModel parameterOutput highs)
        (erase (trace (richProgramH (internalize adversary) q (truncateHash parameterOutput)
          (sampleData parameterOutput fixed highs remaining steps))))
        known prepared.2)}[(HiddenReveal.StopOr RichWin) x] ≤
      Pr{let x ← (interp tg prepared.2 (sampleModel parameterOutput highs)
          (ForsPotential.costGameXH (truncateHash parameterOutput) (sampleData parameterOutput fixed highs remaining steps)
            (internalize adversary)) q (DebtState.start prepared.2 known) >>=
          fun result => (fun table => (table, result)) <$> completion result.2.known)}[CorrectGuess x.1 x.2.2 ∨
          badAV parameterOutput fixed highs remaining prepared.1 x.1
            (((x.2.1.1, x.2.1.2.1), x.2.1.2.2.1), x.2.2.cache)] :=
  stopped_le_interpV hb adversary q hq parameterOutput fixed highs remaining steps prepared hprepared tg known
    (expose_known_support _ fixed prepared.1 known hk).1 (expose_known_support _ fixed prepared.1 known hk).2


/-- Averaging a pointwise bound over the support. -/
theorem tsum_mul_mono_support {α : Type} (mx : ProbComp α) (f g : α → ℝ≥0∞) (h : ∀ x ∈ support mx, f x ≤ g x) :
    ∑' x, Pr{let y ← mx}[y = x] * f x ≤ ∑' x, Pr{let y ← mx}[y = x] * g x :=
  ENNReal.tsum_le_tsum fun x => by
    by_cases hx : x ∈ support mx
    · exact mul_le_mul_right (h x hx) _
    · rw [(prEvent_eq_zero_of_not_mem_support _) hx, zero_mul, zero_mul]

set_option maxRecDepth 100000 in
/-- **The small route's program bridge holds**, the signer honest. -/
theorem smallBridgeH_holds (hb : 0 < keptHeight topLayer) (adversary : Adversary) (q : ℕ) (hq : q < 2 ^ 256)
    (steps : Message → Randomness) : SmallBridgeH (internalize adversary) q steps := by
  unfold SmallBridgeH
  refine le_trans (seedFree_le_exposeP adversary q steps) ?_
  simp only [OracleComp.prEvent_bind_eq_tsum]
  refine tsum_mul_mono_support _ _ _ fun parameterOutput _ => ?_
  refine tsum_mul_mono_support _ _ _ fun fixed _ => ?_
  refine tsum_mul_mono_support _ _ _ fun highs _ => ?_
  refine tsum_mul_mono_support _ _ _ fun remaining _ => ?_
  refine tsum_mul_mono_support _ _ _ fun prepared hprepared => ?_
  refine tsum_mul_mono_support _ _ _ fun known hk => ?_
  have h := stopped_le_interp_exposeV hb adversary q hq parameterOutput fixed highs remaining steps prepared hprepared
    (PotentialA.targetingA parameterOutput fixed highs remaining prepared.1) known hk
  simpa only [OracleComp.prEvent_bind_eq_tsum] using h

end FORS.Security.ForsPotential
