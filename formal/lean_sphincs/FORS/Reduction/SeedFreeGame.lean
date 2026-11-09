module

public import FORS.Reduction.UntilSeed
public import FORS.LazyRun.Cost
public import FORS.Seed.Guess

@[expose] public section

/-! The seed-free, budget-capped graph-view game: the canonical graph cache and answer function of
a sample without any seed-addressed entry, the seed-free run and experiment averaged over
independent material, graph labels and remaining answers, and its win event. `Reduction/SeedElimination` bounds
the SUF-CMA advantage of the deterministic signer by this game plus the cost of naming the seed. -/

open OracleComp OracleSpec ENNReal

namespace FORS.Security.Reduce

variable [Params]

open Completeness SeedCoupling Internalize Eager Short SeedModel Graph Assembly Stop HiddenCost
  GraphView

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
attribute [local instance] Classical.propDecidable

theorem programGraphCache_congr_base (parameter : PublicParameter)
    (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest)
    (ftsSecret : ForsSecrets) (positions : List Position)
    (labels : CanonicalGraphLabels) (base base' : QueryCache HashSpec) (input : HashInput)
    (h : base input = base' input) :
    programGraphCache parameter otsSecret ftsSecret positions labels base input =
      programGraphCache parameter otsSecret ftsSecret positions labels base' input := by
  induction positions generalizing base base' with
  | nil => exact h
  | cons first rest ih =>
      apply ih
      by_cases heq : input = canonicalGraphInput parameter otsSecret ftsSecret first labels
      · subst heq
        show (base.cacheQuery _ _) _ = (base'.cacheQuery _ _) _
        simp [QueryCache.cacheQuery_self]
      · show (base.cacheQuery _ _) input = (base'.cacheQuery _ _) input
        rw [QueryCache.cacheQuery_of_ne _ _ heq, QueryCache.cacheQuery_of_ne _ _ heq]
        exact h

noncomputable local instance reduceLabelsSampleable : SampleableType CanonicalGraphLabels :=
  graphLabelsSampleable

/-- The canonical graph cache without any seed-addressed entry. -/
noncomputable def graphCache (material : Material) (answers : CanonicalGraphLabels) :
    QueryCache HashSpec :=
  programGraphCache (parameter material) (GraphCorrectness.materialOts material)
    (GraphCorrectness.materialFts material) (graphOrder (PrunedGraph.active (parameter material)))
    (labelsOf material answers) ∅

noncomputable def graphFn (material : Material) (answers : CanonicalGraphLabels) (table : Eager.Table) :
    HashInput → HashOutput :=
  extend (graphCache material answers) table

noncomputable def graphCoordinates (material : Material) (answers : CanonicalGraphLabels) :
    HiddenGraph.Table :=
  HiddenGraph.coordinates (GraphCorrectness.materialOts material) (GraphCorrectness.materialFts material)
    (labelsOf material answers)

theorem sampleFn_agree (material : Material) (seed : MasterSeed) (answers : CanonicalGraphLabels)
    (table : Eager.Table) (input : HashInput) (hnot : ¬SeedGuess.SeedHit input seed) :
    sampleFn material seed answers table input = graphFn material answers table input := by
  simp only [sampleFn, graphFn, extend, preparedCache, graphCache]
  rw [programGraphCache_congr_base _ _ _ _ _ _ ∅ input (programCache_agreeOutside ∅ seed material input hnot)]

theorem sampleCoordinates_eq (material : Material) (seed : MasterSeed) (answers : CanonicalGraphLabels)
    (table : Eager.Table) :
    sampleCoordinates material seed answers table = graphCoordinates material answers := by
  rw [sampleCoordinates, graphCoordinates,
    ← GraphCorrectness.materialOts_eq _ seed material (sample_agreement material seed answers table),
    ← GraphCorrectness.materialFts_eq _ seed material (sample_agreement material seed answers table)]

def Win (result : Option Bool × List (Entry HashInput)) : Prop :=
  ∃ value, result.1 = some value ∧ value = true

theorem probEvent_bind_le_add {α β γ δ : Type} (p : ProbComp α) (k : α → ProbComp β)
    (k₁ : α → ProbComp γ) (k₂ : α → ProbComp δ) (event : β → Prop) (event₁ : γ → Prop)
    (event₂ : δ → Prop) (h : ∀ a, Pr{let x ← k a}[event x] ≤ Pr{let x ← k₁ a}[event₁ x] + Pr{let x ← k₂ a}[event₂ x]) :
    Pr{let x ← p >>= k}[event x] ≤ Pr{let x ← p >>= k₁}[event₁ x] + Pr{let x ← p >>= k₂}[event₂ x] := by
  simp only [OracleComp.prEvent_bind_eq_tsum]
  rw [← ENNReal.tsum_add]
  exact ENNReal.tsum_le_tsum fun a => (mul_le_mul' le_rfl (h a)).trans_eq (mul_add ..)

theorem probEvent_bind_le_of {α β : Type} (p : ProbComp α) (k : α → ProbComp β) (event : β → Prop)
    (bound : ℝ≥0∞) (h : ∀ a, Pr{let x ← k a}[event x] ≤ bound) : Pr{let x ← p >>= k}[event x] ≤ bound := by
  rw [OracleComp.prEvent_bind_eq_tsum]
  calc
    _ ≤ ∑' a, Pr{let x ← p}[x = a] * bound := ENNReal.tsum_le_tsum fun a => mul_le_mul' le_rfl (h a)
    _ ≤ bound := by
      rw [ENNReal.tsum_mul_right]
      exact mul_le_of_le_one_left bot_le (OracleComp.tsum_prEvent_le_one _)

theorem probEvent_bind_mono {α β : Type} (p : ProbComp α) (k₁ k₂ : α → ProbComp β)
    (event : β → Prop) (h : ∀ a, Pr{let x ← k₁ a}[event x] ≤ Pr{let x ← k₂ a}[event x]) :
    Pr{let x ← p >>= k₁}[event x] ≤ Pr{let x ← p >>= k₂}[event x] := by
  simp only [OracleComp.prEvent_bind_eq_tsum]
  exact ENNReal.tsum_le_tsum fun a => mul_le_mul' le_rfl (h a)

end FORS.Security.Reduce
