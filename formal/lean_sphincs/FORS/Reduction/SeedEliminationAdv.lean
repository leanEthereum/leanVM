module

public import FORS.Reduction.WinValueAdv
public import FORS.Reduction.SeedElimination

@[expose] public section

/-! **Seed elimination at the adversary's own count**, the signer honest: the internalized adversary-count experiment (`experimentAdv`) wins within a
count `q` at most as often as the seed-free capped run of `costGame` (the signer's reads honest,
the verification charged) for the internalized memoizing adversary, plus `2 q / 2^256` for naming
`SK.seed` or `SK.prf` (`budgetedWinAdv_le_seedFreeH`). The signer reads neither (its honest reads
have other lengths, `Stop.honestUnmarked_signCostSourceH_of_length`), so the "identical until a
marked input" step needs no budget for them. With the adversary's own hash calls bounded by `q` and
the verification's by `V`, `forgeAdvantage_le_seedFree` bounds the advantage at the count
`keygenHashCost + q + V`. -/

open OracleComp OracleSpec ENNReal

namespace FORS.Security.AdvCount

variable [Params]

open Completeness SeedCoupling Internalize Eager Short SeedModel _root_.FORS.Security.Graph Assembly Stop
  HiddenCost GraphView Reduce DetValue Det

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
attribute [local instance] Classical.propDecidable
attribute [local irreducible] encodingAttemptLimit digestAttemptLimit

noncomputable local instance advSeedLabelsSampleable : SampleableType CanonicalGraphLabels :=
  graphLabelsSampleable

/-! ### The seed-free game with honest reads -/

/-- Every realized capped trace respects the budget, with honest reads. -/
theorem costRunH_cap_cost_le {α : Type} (f : HashInput → HashOutput) (table : HiddenGraph.Table)
    (computation : OracleComp CostSpecH α) (budget : Nat)
    (result : Option α × List (Entry HashInput))
    (hresult : result ∈ support (costRunH f table (cap computation budget))) :
    traceCost result.2 ≤ budget := by
  induction computation using OracleComp.inductionOn generalizing budget result with
  | pure value =>
      rw [capH_pure, costRunH_pure, support_pure, Set.mem_singleton_iff] at hresult
      subst hresult
      simp [traceCost]
  | query_bind input next ih =>
      rw [capH_query_bind] at hresult
      split at hresult
      · rename_i hcost
        rw [costRunH_query_bind, mem_support_bind_iff] at hresult
        obtain ⟨answer, _, hmap⟩ := hresult
        rw [support_map] at hmap
        obtain ⟨tail, htail, rfl⟩ := hmap
        have h := ih answer (budget - sourceCost input) tail htail
        simp only [traceCost_append, recorded_cost]
        omega
      · rw [costRunH_pure, support_pure, Set.mem_singleton_iff] at hresult
        subst hresult
        simp [traceCost]

/-- One seed-free capped run of the honest-reading game, with the walk steps `steps`. -/
noncomputable def seedFreeRun (adversary : Adversary) (q : Nat) (steps : Message → Randomness)
    (material : Material) (answers : CanonicalGraphLabels) (table : Eager.Table) :
    ProbComp (Option Bool × List (Entry HashInput)) :=
  costRunH (graphFn material answers table) (graphCoordinates material answers)
    (cap (costGame (parameter material) (publicData (labelsOf material answers) steps) adversary) q)

/-- The seed-free honest-reading experiment for a fixed table of walk steps. -/
noncomputable def seedFreeExperiment (adversary : Adversary) (q : Nat) (steps : Message → Randomness) :
    ProbComp (Option Bool × List (Entry HashInput)) := do
  let material ← sampleMaterial
  let answers ← $ᵗ CanonicalGraphLabels
  let table ← $ᵗ Eager.Table
  seedFreeRun adversary q steps material answers table

/-! ### The deterministic program reads no marked input honestly -/

theorem honestUnmarked_liftRawH (marked : HashInput → Prop) {α : Type} (computation : OracleComp HashSpec α) :
    HonestUnmarked marked (liftRawH computation) := by
  induction computation using OracleComp.inductionOn with
  | pure value => rw [liftRawH_pure]; exact honestUnmarked_pure marked value
  | query_bind input next ih =>
      rw [liftRawH_query_bind]
      exact (honestUnmarked_query_bind marked _ _).2 ⟨fun _ h => (by cases h), ih⟩

theorem honestUnmarked_map (marked : HashInput → Prop) {α β : Type} (g : α → β)
    {computation : OracleComp CostSpecH α} (h : HonestUnmarked marked computation) :
    HonestUnmarked marked (g <$> computation) := by
  rw [map_eq_bind_pure_comp]
  exact honestUnmarked_bind marked h fun _ => honestUnmarked_pure marked _

/-- The marked inputs: a seed's (44 or 80 bytes) or a randomizer derivation's (93 bytes). -/
theorem marked_length (seed : MasterSeed) (prf : HashOutput) (input : HashInput)
    (h : Marked seed prf input) : input.length = 44 ∨ input.length = 80 ∨ input.length = 93 := by
  rcases h with hseed | ⟨parameter, message, rfl⟩
  · rcases seedHit_length hseed with h | h <;> omega
  · rw [randomizerHashInput_length]
    omega

/-- The honest scan from any start reads no input of a marked length. -/
theorem honestUnmarked_signCostSourceLoopH (marked : HashInput → Prop)
    (hlength : ∀ input, marked input → input.length = 44 ∨ input.length = 80 ∨ input.length = 93)
    (parameter : PublicParameter) (data : PublicData) (message : Message) (step : Randomness) :
    ∀ attempts randomness,
      HonestUnmarked marked (signCostSourceLoopH parameter data message step attempts randomness) := by
  have hmsg : ∀ parameter root message randomness call,
      ¬marked (messageDigestInput parameter root message randomness call) := fun _ _ _ _ _ h => by
    have := hlength _ h
    rw [messageDigestInput_length] at this
    omega
  have htrial : ∀ lay tree leaf start,
      ¬marked (trialInput parameter lay tree leaf (data.keyMessage lay tree leaf) start) := fun _ _ _ _ h => by
    have := hlength _ h
    rw [trialInput_keyMessage_length] at this
    omega
  have hfinish : ∀ randomness, HonestUnmarked marked (finishCostSourceH parameter data message randomness) := by
    intro randomness
    rw [finishCostSourceH]
    refine honestUnmarked_bind marked (honestUnmarked_liftHonest marked _
      (noMarked_messageDigest marked hmsg parameter data.root message randomness)) fun digest => ?_
    refine honestUnmarked_bind marked (honestUnmarked_sequenceDep marked _ fun lay =>
      honestUnmarked_liftHonest marked _ (noMarked_search marked parameter lay _ _ _
        (htrial lay _ _) _ _)) fun found => ?_
    cases found with
    | none => exact honestUnmarked_pure marked _
    | some found =>
        refine honestUnmarked_bind marked (honestUnmarked_sequenceFin marked _ fun lay =>
          honestUnmarked_sequenceFin marked _ fun chain => honestUnmarked_reveal marked _) fun values => ?_
        refine honestUnmarked_bind marked (honestUnmarked_sequenceFin marked _ fun κ => ?_)
          fun _ => honestUnmarked_pure marked _
        rw [treeCostSourceH]
        exact honestUnmarked_bind marked (honestUnmarked_sequenceFin marked _ fun _ =>
          honestUnmarked_reveal marked _) fun _ => honestUnmarked_pure marked _
  intro attempts
  induction attempts with
  | zero => intro randomness; rw [signCostSourceLoopH]; exact honestUnmarked_pure marked _
  | succ attempts ih =>
      intro randomness
      rw [signCostSourceLoopH]
      refine honestUnmarked_bind marked (honestUnmarked_liftHonest marked _
        (noMarked_messageDigestCall marked hmsg parameter data.root message randomness firstCall))
        fun first => ?_
      split
      · exact hfinish randomness
      · exact ih (randomness + step)

theorem honestUnmarked_interactionDetH (marked : HashInput → Prop)
    (hlength : ∀ input, marked input → input.length = 44 ∨ input.length = 80 ∨ input.length = 93)
    (parameter : PublicParameter) (data : PublicData) (rnd : RTable) {β : Type} (M : OracleComp AdvSpec β) :
    HonestUnmarked marked (simulateQ (costInteractionDet parameter data rnd) M).run := by
  induction M using OracleComp.inductionOn with
  | pure value => simpa using honestUnmarked_pure marked _
  | query_bind input next ih =>
      rw [simulateQ_bind, WriterT.run_bind, simulateQ_spec_query]
      refine honestUnmarked_bind marked ?_ fun result => honestUnmarked_map marked _ (ih result.1)
      rcases input with (draw | bytes) | message
      · change HonestUnmarked marked ((fun value => (value, (∅ : QueryLog SigningSpec))) <$>
          ordinaryCostSourceH (.inl draw))
        exact honestUnmarked_map marked _ (honestUnmarked_query_of_ne marked _ fun _ h => by cases h)
      · change HonestUnmarked marked ((fun value => (value, (∅ : QueryLog SigningSpec))) <$>
          ordinaryCostSourceH (.inr bytes))
        exact honestUnmarked_map marked _ (honestUnmarked_query_of_ne marked _ fun _ h => by cases h)
      · change HonestUnmarked marked (QueryImpl.withLogging (spec := SigningSpec) (m := OracleComp CostSpecH)
          (fun message => signCostDet parameter data rnd message) message).run
        rw [QueryImpl.run_withLogging_apply]
        exact honestUnmarked_bind marked (honestUnmarked_signCostSourceLoopH marked hlength _ _ _ _ _ _)
          fun _ => honestUnmarked_pure marked _

/-- The honest deterministic game reads no input of a marked length honestly. -/
theorem honestUnmarked_costGameDetH (marked : HashInput → Prop)
    (hlength : ∀ input, marked input → input.length = 44 ∨ input.length = 80 ∨ input.length = 93)
    (parameter : PublicParameter) (data : PublicData) (rnd : RTable) (adversary : Adversary) :
    HonestUnmarked marked (costGameDet parameter data rnd adversary) := by
  rw [costGameDet]
  refine honestUnmarked_bind marked (honestUnmarked_query_of_ne marked _ fun _ h => by cases h) fun _ => ?_
  rw [costRestDet]
  refine honestUnmarked_bind marked (honestUnmarked_interactionDetH marked hlength parameter data rnd _)
    fun result => ?_
  rcases result with ⟨forgery, log⟩
  exact honestUnmarked_bind marked (honestUnmarked_liftRawH marked _) fun _ => honestUnmarked_pure marked _

theorem honestUnmarked_cap (marked : HashInput → Prop) {α : Type} (computation : OracleComp CostSpecH α)
    (h : HonestUnmarked marked computation) (budget : Nat) : HonestUnmarked marked (cap computation budget) := by
  induction computation using OracleComp.inductionOn generalizing budget with
  | pure value => rw [capH_pure]; exact honestUnmarked_pure marked _
  | query_bind input next ih =>
      obtain ⟨hin, hnext⟩ := (honestUnmarked_query_bind marked input next).1 h
      rw [capH_query_bind]
      split
      · exact (honestUnmarked_query_bind marked input _).2 ⟨hin, fun value => ih value (hnext value) _⟩
      · exact honestUnmarked_pure marked _

/-! ### One sample -/

/-- Every sample of the internalized adversary-count game equals its honest graph-view cost game. -/
theorem sample_costGameDet (adversary : Adversary) (material : Material) (seed : MasterSeed)
    (answers : CanonicalGraphLabels) (table : Eager.Table) (rnd : RTable) :
    simulateQ (fixedRom (extend (preparedCache material seed answers)
          (plant (prf material) (SeedModel.parameter material) table rnd)))
        (gameAfterSeedAdv adversary seed) =ᵈ
      ((simulateQ (fixedCostSource
          (sampleFn material seed answers (plant (prf material) (SeedModel.parameter material) table rnd))
          (sampleCoordinates material seed answers (plant (prf material) (SeedModel.parameter material) table rnd)))
        (costGameDet (SeedModel.parameter material)
          (GraphView.publicData (labelsOf material answers) (highsOf rnd)) rnd
          adversary)).run) := by
  set table' := plant (prf material) (SeedModel.parameter material) table rnd
  rw [show (extend (preparedCache material seed answers) table') =
      sampleFn material seed answers table' from rfl]
  refine (evalDist_fixedRom_eq_fixedHashWorld _ _).trans ?_
  rw [costGameDetH_correct (sampleFn material seed answers table') (SeedModel.parameter material) seed
      (GraphView.publicData (labelsOf material answers) (highsOf rnd))
      (sampleCoordinates material seed answers table')
      (GraphView.publicData_correct _ _ _ _ (sample_consistent material seed answers table')
        (sample_boundary material seed answers table') _)
      (GraphView.coordinates_correct _ _ _ _ (sample_consistent material seed answers table'))
      (sample_parameter material seed answers table') (prf material)
      (eval_prf_prepared _ seed material (sample_agreement material seed answers table')) rnd
      (fun message => sampleFn_randomizer material seed answers table rnd message)]

/-- The seed-free capped deterministic run of one sample. -/
noncomputable def detRun (adversary : Adversary) (q : Nat) (material : Material)
    (answers : CanonicalGraphLabels) (table : Eager.Table) (rnd : RTable) :
    ProbComp (Option Bool × List (Entry HashInput)) :=
  costRunH (graphFn material answers table) (graphCoordinates material answers)
    (cap (costGameDet (SeedModel.parameter material) (publicData (labelsOf material answers) (highsOf rnd))
      rnd adversary) q)

/-- One sample: the capped win in the deterministic game is at most the seed-free capped win
plus naming the seed. -/
theorem per_sampleDet (adversary : Adversary) (q : Nat) (material : Material) (seed : MasterSeed)
    (answers : CanonicalGraphLabels) (table : Eager.Table) (rnd : RTable) :
    Pr{let result ← (simulateQ (fixedRom (extend (preparedCache material seed answers)
          (plant (prf material) (SeedModel.parameter material) table rnd)))
          (gameAfterSeedAdv adversary seed))}[result.1 = true ∧ result.2 ≤ q] ≤
      Pr{let x ← detRun adversary q material answers table rnd}[Win x] +
        Pr{let result ← detRun adversary q material answers table rnd}[
          Hits (Marked seed (prf material)) result.2] := by
  set table' := plant (prf material) (SeedModel.parameter material) table rnd
  have hrun := (sample_costGameDet adversary material seed answers table rnd).trans
    (evalDist_fixedCostSource _ _ _)
  rw [(hrun).prEvent_eq, prEvent_map]
  refine le_trans (le_of_eq ?_) (le_trans (probEvent_costRunH_le_cap (sampleFn material seed answers table')
    (sampleCoordinates material seed answers table')
    (costGameDet (SeedModel.parameter material) (publicData (labelsOf material answers) (highsOf rnd)) rnd
      adversary)
    q (fun value => value = true)) ?_)
  · rfl
  · rw [sampleCoordinates_eq]
    exact probEvent_costRunH_le (sampleFn material seed answers table') (graphFn material answers table)
      (graphCoordinates material answers) (Marked seed (prf material))
      (sampleFn_plant_agree material seed answers table rnd)
      (cap (costGameDet (SeedModel.parameter material) (publicData (labelsOf material answers) (highsOf rnd)) rnd
        adversary) q)
      (honestUnmarked_cap _ _ (honestUnmarked_costGameDetH _ (marked_length seed (prf material)) _ _ _ _) q) Win

/-! ### The whole game -/

attribute [local irreducible] experiment sampleMasterSeed

/-- **Seed elimination from a uniform `SK.seed`.** If the seed-free capped win of the internalized
memoizing adversary in the fresh-randomizer graph-view game is at most `B` for every table of walk
steps, the capped win of the internalized game is at most `B` plus `2 q / 2^256` for naming
`SK.seed` or `SK.prf`. The step halves are fixed and the base randomizers averaged. -/
theorem budgetedWinAdv_le_seedFreeH (adversary : Adversary) (q : Nat) (B : ℝ≥0∞)
    (hB : ∀ steps,
      Pr{let z ← seedFreeExperiment (internalize (Memo.memoAdv adversary)) q steps}[Win z] ≤ B) :
    Pr{let result ← experimentAdv (internalize adversary)}[result.1 = true ∧ result.2 ≤ q] ≤
      B + 2 * (q / (2 : ℝ≥0∞) ^ 256) := by
  calc
    _ = Pr{let result ← (do
          let material ← sampleMaterial
          let seed ← sampleMasterSeed
          let answers ← $ᵗ CanonicalGraphLabels
          let table ← $ᵗ Eager.Table
          simulateQ (fixedRom (extend (preparedCache material seed answers) table))
            (gameAfterSeedAdv (internalize adversary) seed))}[
              result.1 = true ∧ result.2 ≤ q] :=
      (evalDist_experimentAdv_fixed adversary).prEvent_eq _
    _ = Pr{let result ← (do
          let material ← sampleMaterial
          let seed ← sampleMasterSeed
          let answers ← $ᵗ CanonicalGraphLabels
          let table ← $ᵗ Eager.Table
          let rnd ← $ᵗ RTable
          simulateQ (fixedRom (extend (preparedCache material seed answers)
              (plant (prf material) (SeedModel.parameter material) table rnd)))
            (gameAfterSeedAdv (internalize adversary) seed))}[
              result.1 = true ∧ result.2 ≤ q] := by
      refine EvalDistEq.prEvent_eq ?_ _
      refine EvalDistEq.bind_right _ fun material => EvalDistEq.bind_right _ fun seed =>
        EvalDistEq.bind_right _ fun answers => ?_
      exact evalDist_table_split (prf material) (SeedModel.parameter material) _
    _ ≤ Pr{let x ← (do
          let material ← sampleMaterial
          let _seed ← sampleMasterSeed
          let answers ← $ᵗ CanonicalGraphLabels
          let table ← $ᵗ Eager.Table
          let rnd ← $ᵗ RTable
          detRun (internalize adversary) q material answers table rnd)}[Win x] +
        Pr{let pair ← (do
          let material ← sampleMaterial
          let seed ← sampleMasterSeed
          let answers ← $ᵗ CanonicalGraphLabels
          let table ← $ᵗ Eager.Table
          let rnd ← $ᵗ RTable
          (fun result => ((seed, prf material), result)) <$>
            detRun (internalize adversary) q material answers table rnd :
            ProbComp ((MasterSeed × HashOutput) × (Option Bool × List (Entry HashInput))))}[
              Hits (Marked pair.1.1 pair.1.2) pair.2.2] := by
      refine probEvent_bind_le_add _ _ _ _ _ _ _ fun material => ?_
      refine probEvent_bind_le_add _ _ _ _ _ _ _ fun seed => ?_
      refine probEvent_bind_le_add _ _ _ _ _ _ _ fun answers => ?_
      refine probEvent_bind_le_add _ _ _ _ _ _ _ fun table => ?_
      refine probEvent_bind_le_add _ _ _ _ _ _ _ fun rnd => ?_
      rw [prEvent_map]
      exact per_sampleDet (internalize adversary) q material seed answers table rnd
    _ ≤ B + (q / (2 : ℝ≥0∞) ^ 256 + q / (2 : ℝ≥0∞) ^ 256) := by
      refine add_le_add ?_ ?_
      · have hsteps : ∀ steps : LTable, Pr{let z ← (do
            let material ← sampleMaterial
            let _seed ← sampleMasterSeed
            let answers ← $ᵗ CanonicalGraphLabels
            let table ← $ᵗ Eager.Table
            let lows ← ($ᵗ LTable : ProbComp LTable)
            detRun (internalize adversary) q material answers table (joinTable lows steps))}[Win z] ≤ B := by
          intro steps
          refine le_trans ?_ (hB steps)
          unfold seedFreeExperiment
          refine probEvent_bind_mono _ _ _ _ fun material => ?_
          refine probEvent_bind_le_of _ _ _ _ fun _ => ?_
          refine probEvent_bind_mono _ _ _ _ fun answers => ?_
          refine probEvent_bind_mono _ _ _ _ fun table => ?_
          unfold detRun seedFreeRun
          simp only [highsOf_joinTable]
          rw [Memo.internalize_memoAdv]
          exact win_avg_le (graphFn material answers table) (graphCoordinates material answers)
            (SeedModel.parameter material) (publicData (labelsOf material answers) steps) (internalize adversary)
            (noRepeat_internalize_memoAdv adversary) q
        have hsplit : Pr{let z ← (do
            let material ← sampleMaterial
            let _seed ← sampleMasterSeed
            let answers ← $ᵗ CanonicalGraphLabels
            let table ← $ᵗ Eager.Table
            let rnd ← $ᵗ RTable
            detRun (internalize adversary) q material answers table rnd)}[Win z] =
          Pr{let z ← (do
            let steps ← ($ᵗ LTable : ProbComp LTable)
            let material ← sampleMaterial
            let _seed ← sampleMasterSeed
            let answers ← $ᵗ CanonicalGraphLabels
            let table ← $ᵗ Eager.Table
            let lows ← ($ᵗ LTable : ProbComp LTable)
            detRun (internalize adversary) q material answers table (joinTable lows steps))}[Win z] := by
          refine EvalDistEq.prEvent_eq ?_ _
          refine EvalDistEq.trans ?_
            (OracleComp.EvalDistEq.bind_bind_swap sampleMaterial ($ᵗ LTable : ProbComp LTable) _)
          refine EvalDistEq.bind_right _ fun material => ?_
          refine EvalDistEq.trans ?_
            (OracleComp.EvalDistEq.bind_bind_swap sampleMasterSeed ($ᵗ LTable : ProbComp LTable) _)
          refine EvalDistEq.bind_right _ fun _ => ?_
          refine EvalDistEq.trans ?_
            (OracleComp.EvalDistEq.bind_bind_swap ($ᵗ CanonicalGraphLabels) ($ᵗ LTable : ProbComp LTable) _)
          refine EvalDistEq.bind_right _ fun answers => ?_
          refine EvalDistEq.trans ?_
            (OracleComp.EvalDistEq.bind_bind_swap ($ᵗ Eager.Table) ($ᵗ LTable : ProbComp LTable) _)
          refine EvalDistEq.bind_right _ fun table => ?_
          exact evalDist_rtable_split _
        rw [hsplit]
        exact probEvent_bind_le_of _ _ _ _ fun steps => hsteps steps
      · refine le_trans (prEvent_mono_of_support _ _ (fun pair :
            (MasterSeed × HashOutput) × (Option Bool × List (Entry HashInput)) =>
            Hits (fun input => SeedGuess.SeedHit input pair.1.1) pair.2.2 ∨
              Hits (fun input => RandHit input pair.1.2) pair.2.2) fun pair _ hpair => ?_)
          ((prEvent_or_le _ _ _).trans (add_le_add ?_ ?_))
        · obtain ⟨input, hmem, hinput | hinput⟩ := hpair
          · exact Or.inl ⟨input, hmem, hinput⟩
          · exact Or.inr ⟨input, hmem, hinput⟩
        · -- `SK.seed`: drawn independently of the seed-free run
          refine probEvent_bind_le_of _ _ _ _ fun material => ?_
          rw [(OracleComp.EvalDistEq.bind_bind_swap sampleMasterSeed
            ($ᵗ CanonicalGraphLabels) _).prEvent_eq]
          refine probEvent_bind_le_of _ _ _ _ fun answers => ?_
          rw [(OracleComp.EvalDistEq.bind_bind_swap sampleMasterSeed
            ($ᵗ Eager.Table) _).prEvent_eq]
          refine probEvent_bind_le_of _ _ _ _ fun table => ?_
          rw [(OracleComp.EvalDistEq.bind_bind_swap sampleMasterSeed
            ($ᵗ RTable) _).prEvent_eq]
          refine probEvent_bind_le_of _ _ _ _ fun rnd => ?_
          refine le_trans (marked_hit_le sampleMasterSeed (fun seed input => SeedGuess.SeedHit input seed)
            (1 / (2 : ℝ≥0∞) ^ 256) SeedGuess.seedHit_probability_le
            (detRun (internalize adversary) q material answers table rnd) (fun result => result.2) q
            (fun result hresult => costRunH_cap_cost_le _ _ _ q result hresult)
            (fun seed result => ((seed, prf material), result)) _ (fun _ _ h => h)) (le_of_eq ?_)
          rw [mul_one_div]
        · -- `SK.prf`: drawn last in the material, and never read by the seed-free run
          simp only [sampleMaterial, bind_assoc, pure_bind]
          refine probEvent_bind_le_of _ _ _ _ fun parameterOutput => ?_
          refine probEvent_bind_le_of _ _ _ _ fun outputs => ?_
          have hprog : ∀ key : HashOutput, (do
              let seed ← sampleMasterSeed
              let answers ← $ᵗ CanonicalGraphLabels
              let table ← $ᵗ Eager.Table
              let rnd ← $ᵗ RTable
              (fun result => ((seed, prf ((parameterOutput, key), outputs)), result)) <$>
                detRun (internalize adversary) q ((parameterOutput, key), outputs) answers table rnd :
                ProbComp ((MasterSeed × HashOutput) × (Option Bool × List (Entry HashInput)))) =
              (fun pair => ((pair.1, key), pair.2)) <$> (do
                let seed ← sampleMasterSeed
                let answers ← $ᵗ CanonicalGraphLabels
                let table ← $ᵗ Eager.Table
                let rnd ← $ᵗ RTable
                (fun result => (seed, result)) <$>
                  detRun (internalize adversary) q ((parameterOutput, 0), outputs) answers table rnd) := by
            intro key
            simp only [map_bind, Functor.map_map]
            rfl
          simp only [hprog]
          have hcost : ∀ pair ∈ support (do
                let seed ← sampleMasterSeed
                let answers ← $ᵗ CanonicalGraphLabels
                let table ← $ᵗ Eager.Table
                let rnd ← $ᵗ RTable
                (fun result => (seed, result)) <$>
                  detRun (internalize adversary) q ((parameterOutput, 0), outputs) answers table rnd :
                ProbComp (MasterSeed × (Option Bool × List (Entry HashInput)))),
              traceCost pair.2.2 ≤ q := by
            intro pair hpair
            simp only [mem_support_bind_iff, support_map, Set.mem_image] at hpair
            obtain ⟨_, _, _, _, _, _, _, _, result, hresult, rfl⟩ := hpair
            exact costRunH_cap_cost_le _ _ _ q result hresult
          exact le_trans (marked_hit_le (S := HashOutput)
            (Ω := MasterSeed × (Option Bool × List (Entry HashInput)))
            ($ᵗ HashOutput) (fun key input => RandHit input key)
            (1 / (2 : ℝ≥0∞) ^ 256) randHit_probability_le _ (fun pair => pair.2.2) q hcost
            (fun key pair => ((pair.1, key), pair.2)) _ (fun _ _ h => h)) (le_of_eq (mul_one_div _ _))
    _ = B + 2 * (q / (2 : ℝ≥0∞) ^ 256) := by rw [two_mul]


/-- **The adversary-count bound.** If the adversary makes at most `q` hash calls of its own on
every path and the verification at most `V`, and the seed-free capped win of the internalized
memoizing adversary in the honest-reading game at the count `keygenHashCost + q + V` is at most `B`
for every table of walk steps, then the SUF-CMA advantage is at most `B` plus
`2 (keygenHashCost + q + V) / 2^256`. -/
theorem forgeAdvantage_le_seedFree (adversary : Adversary) (q V : Nat)
    (hq : ∀ pk, (adversary.main pk).IsQueryBoundP AdvHash q)
    (hV : ∀ pk message signature,
      (Concrete.verify pk message signature : OracleComp HashSpec Bool).IsQueryBoundP (fun _ => True) V)
    (B : ℝ≥0∞)
    (hB : ∀ steps, Pr{let z ← (seedFreeExperiment (internalize (Memo.memoAdv adversary))
      (Prefix.keygenHashCost + q + V) steps)}[Win z] ≤ B) :
    forgeAdvantage adversary ≤ B + 2 * ((Prefix.keygenHashCost + q + V : Nat) / (2 : ℝ≥0∞) ^ 256) := by
  rw [← forgeAdvantage_internalize, ← winAdv_eq]
  calc
    _ = Pr{let result ← experimentAdv (internalize adversary)}[result.1 = true ∧
          result.2 ≤ Prefix.keygenHashCost + q + V] :=
      prEvent_congr_of_support _ _ _ fun result hresult =>
        ⟨fun h => ⟨h, experimentAdv_count_le _ q V (isQueryBoundP_internalize adversary q hq) hV result
          hresult⟩, And.left⟩
    _ ≤ _ := budgetedWinAdv_le_seedFreeH adversary _ B hB

end FORS.Security.AdvCount
