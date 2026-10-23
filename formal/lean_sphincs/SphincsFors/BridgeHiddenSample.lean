import SphincsFors.BridgeHidden

/-! Resampling the hidden coordinates: the seed-free experiment is an average, over every
public and structural sample, of the hidden-row run whose coordinate table is an exact
uniform completion of the known coordinates. -/

open OracleComp OracleSpec ENNReal

namespace SphincsFors.Security.HiddenBridge

open Completeness SeedModel Graph Assembly Reduce HiddenGraph
open SphincsBase.Concrete.UniformTableSplit

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
attribute [local instance] Classical.propDecidable

variable [Params]

/-- Swapping the known parts of two tables is an involution. -/
noncomputable def swapKnown (parameter : PublicParameter) (pair : HiddenGraph.Table × HiddenGraph.Table) :
    HiddenGraph.Table × HiddenGraph.Table :=
  (mix parameter pair.1 pair.2, mix parameter pair.2 pair.1)

theorem swapKnown_involutive (parameter : PublicParameter) :
    Function.Involutive (swapKnown parameter) := by
  intro pair
  apply Prod.ext <;> funext coordinate <;>
    by_cases h : KnownCoordinate parameter coordinate <;> simp [swapKnown, mix, h]

omit [Params] in
theorem uniform_map_fst {α β : Type} [Fintype α] [Fintype β] [Nonempty α] [Nonempty β] :
    (PMF.uniformOfFintype (α × β)).map Prod.fst = PMF.uniformOfFintype α := by
  rw [uniform_product, PMF.map_bind]
  simp only [PMF.map_comp, Function.comp_def]
  have hconst : ∀ a : α, PMF.map (fun _ : β => a) (PMF.uniformOfFintype β) = PMF.pure a :=
    fun a => PMF.map_const _ a
  simp only [hconst]
  exact PMF.bind_pure _

theorem uniform_mix (parameter : PublicParameter) :
    (PMF.uniformOfFintype HiddenGraph.Table).bind (fun fixed =>
      (PMF.uniformOfFintype HiddenGraph.Table).map (mix parameter fixed)) =
      PMF.uniformOfFintype HiddenGraph.Table := by
  have hpair : (PMF.uniformOfFintype HiddenGraph.Table).bind (fun fixed =>
      (PMF.uniformOfFintype HiddenGraph.Table).map (mix parameter fixed)) =
      ((PMF.uniformOfFintype (HiddenGraph.Table × HiddenGraph.Table)).map (swapKnown parameter)).map
        Prod.fst := by
    rw [PMF.map_comp, uniform_product, PMF.map_bind]
    simp only [PMF.map_comp, Function.comp_def, swapKnown]
  rw [hpair, PMF.uniformOfFintype_map_of_bijective _ (swapKnown_involutive parameter).bijective,
    uniform_map_fst]

omit [Params] in
theorem evalDist_uniform_congr {α : Type} [Fintype α] [Nonempty α] (left right : SampleableType α) :
    (@uniformSample α left : ProbComp α) =ᵈ (@uniformSample α right : ProbComp α) := by
  exact fun p => SampleableType.prEvent_uniformSample_inst_irrel left right p

noncomputable local instance sampleCellFintypeInst : Fintype SampleCell := sampleCellFintype
noncomputable local instance sampleCellDecEq : DecidableEq SampleCell := Classical.decEq _
noncomputable local instance secretOutputsSampleableInst : SampleableType SecretOutputs :=
  secretOutputsSampleableType
noncomputable local instance labelsSampleableInst : SampleableType CanonicalGraphLabels :=
  graphLabelsSampleable
noncomputable local instance hiddenTableSampleable : SampleableType HiddenGraph.Table :=
  SampleableType.ofFintype _
noncomputable local instance highsSampleable : SampleableType CoordinateHighs := SampleableType.ofFintype _
noncomputable local instance remainingSampleable : SampleableType RemainingOutputs :=
  SampleableType.ofFintype _

omit [Params] in
private theorem uniformSample_evalDistEq_pmf (T : Type) [Fintype T] [Nonempty T] [SampleableType T] :
    ($ᵗ T : ProbComp T) =ᵈ PMF.uniformOfFintype T := by
  refine evalDistEq_iff_forall_prEvent_eq_output.mpr fun x => ?_
  rw [SampleableType.prEvent_uniformSample_eq_singleton, PMF.probOutput_eq_apply,
    PMF.uniformOfFintype_apply]

theorem evalDist_mix (parameter : PublicParameter) :
    (($ᵗ HiddenGraph.Table) >>= fun fixed => mix parameter fixed <$> ($ᵗ HiddenGraph.Table)) =ᵈ ($ᵗ HiddenGraph.Table : ProbComp HiddenGraph.Table) := by
  have hu := uniformSample_evalDistEq_pmf HiddenGraph.Table
  refine (hu.bind fun fixed => hu.map (mix parameter fixed)).trans ?_
  rw [show ((PMF.uniformOfFintype HiddenGraph.Table) >>= fun fixed =>
      mix parameter fixed <$> PMF.uniformOfFintype HiddenGraph.Table) =
        PMF.uniformOfFintype HiddenGraph.Table from uniform_mix parameter]
  exact hu.symm

theorem evalDist_mix_bind {β : Type} (parameter : PublicParameter) (next : HiddenGraph.Table → ProbComp β) :
    (($ᵗ HiddenGraph.Table) >>= next) =ᵈ (($ᵗ HiddenGraph.Table) >>= fun fixed => ($ᵗ HiddenGraph.Table) >>= fun fresh =>
        next (mix parameter fixed fresh)) := by
  have h := (evalDist_mix parameter).bind_left next
  simp only [bind_assoc, bind_map_left] at h
  exact h.symm

omit [Params] in
theorem evalDist_completion_bind {β : Type} (known : HiddenReveal.Knowledge Coordinate)
    (next : HiddenGraph.Table → ProbComp β) :
    (HiddenReveal.completion known >>= next) =ᵈ (($ᵗ HiddenGraph.Table) >>= fun fresh => next (tableExtending known fresh)) := by
  unfold HiddenReveal.completion
  refine (Eager.evalDist_map_bind' _ _ _).trans ?_
  exact (evalDist_uniform_congr HiddenReveal.tableSampleable hiddenTableSampleable).bind_left _

/-- One public/structural sample's hidden-row run at coordinate table `table`. -/
noncomputable def hiddenRun (adversary : Adversary) (q : Nat) (parameterOutput : HashOutput)
    (fixed : HiddenGraph.Table) (highs : CoordinateHighs) (remaining : RemainingOutputs)
    (outsideTable : Eager.Table) (table : HiddenGraph.Table) :
    ProbComp (Option Bool × List (HiddenCost.Entry HashInput)) :=
  Stop.costRun
    (HiddenGraph.answer (truncateHash parameterOutput) (candidateActive (truncateHash parameterOutput))
      table (fun address => highs address.outputCoordinate)
      (outsideFn (splitMaterial parameterOutput highs remaining fixed)
        (splitAnswers highs remaining fixed) outsideTable))
    table
    (HiddenCost.cap (GraphView.costGame (truncateHash parameterOutput)
      (GraphView.publicData (labelsOf (splitMaterial parameterOutput highs remaining fixed)
        (splitAnswers highs remaining fixed))) adversary) q)

/-- **Hidden decomposition.** The seed-free experiment samples every public and structural
value first and then the coordinate table as an exact completion of the known coordinates. -/
theorem evalDist_seedFree_completion (adversary : Adversary) (q : Nat) :
    seedFreeExperiment adversary q =ᵈ (do
        let parameterOutput ← $ᵗ HashOutput
        let fixed ← $ᵗ HiddenGraph.Table
        let highs ← $ᵗ CoordinateHighs
        let remaining ← $ᵗ RemainingOutputs
        let outsideTable ← $ᵗ Eager.Table
        let table ← HiddenReveal.completion (knownOf (truncateHash parameterOutput) fixed)
        hiddenRun adversary q parameterOutput fixed highs remaining outsideTable table) := by
  unfold seedFreeExperiment
  refine (evalDist_material_graph_continuation _).trans ?_
  refine EvalDistEq.bind_right _ fun parameterOutput => ?_
  simp only [sampleSplitPair, bind_assoc, bind_map_left]
  refine (evalDist_mix_bind (truncateHash parameterOutput) _).trans ?_
  refine EvalDistEq.bind_right _ fun fixed => ?_
  simp only [joinedPair]
  change ($ᵗ HiddenGraph.Table) >>= (fun fresh => ($ᵗ CoordinateHighs) >>= fun highs =>
      ($ᵗ RemainingOutputs) >>= fun remaining => ($ᵗ Eager.Table) >>= fun outsideTable =>
        seedFreeRun adversary q
          (splitMaterial parameterOutput highs remaining (mix (truncateHash parameterOutput) fixed fresh))
          (splitAnswers highs remaining (mix (truncateHash parameterOutput) fixed fresh)) outsideTable) =ᵈ _
  simp only [seedFreeRun_mix]
  refine (OracleComp.EvalDistEq.bind_bind_swap _ _ _).trans ?_
  refine EvalDistEq.bind_right _ fun highs => ?_
  refine (OracleComp.EvalDistEq.bind_bind_swap _ _ _).trans ?_
  refine EvalDistEq.bind_right _ fun remaining => ?_
  refine (OracleComp.EvalDistEq.bind_bind_swap _ _ _).trans ?_
  refine EvalDistEq.bind_right _ fun outsideTable => ?_
  refine EvalDistEq.trans ?_ (evalDist_completion_bind
    (knownOf (truncateHash parameterOutput) fixed) _).symm
  exact EvalDistEq.rfl

omit [Params] in
theorem probEvent_bind_mono_support {α β γ : Type} (p : ProbComp α) (k₁ : α → ProbComp β)
    (k₂ : α → ProbComp γ) (event₁ : β → Prop) (event₂ : γ → Prop)
    (h : ∀ a ∈ support p, Pr{let x ← k₁ a}[event₁ x] ≤ Pr{let x ← k₂ a}[event₂ x]) :
    Pr{let x ← p >>= k₁}[event₁ x] ≤ Pr{let x ← p >>= k₂}[event₂ x] := by
  simp only [OracleComp.prEvent_bind_eq_tsum]
  refine ENNReal.tsum_le_tsum fun a => ?_
  by_cases ha : a ∈ support p
  · exact mul_le_mul' le_rfl (h a ha)
  · rw [(prEvent_eq_zero_of_not_mem_support _) ha]
    simp

/-- The row model of one sample: high halves are the independent sampled ones. -/
noncomputable def sampleModel (parameterOutput : HashOutput) (highs : CoordinateHighs) :
    HiddenRows.Model HashInput HashOutput Address Coordinate :=
  rowModel (truncateHash parameterOutput) (candidateActive (truncateHash parameterOutput))
    (fun address => highs address.outputCoordinate)

/-- The capped graph-view program of one sample. -/
noncomputable def sampleProgram (adversary : Adversary) (q : Nat) (parameterOutput : HashOutput)
    (fixed : HiddenGraph.Table) (highs : CoordinateHighs) (remaining : RemainingOutputs) :
    OracleComp GraphView.CostSpec (Option Bool) :=
  HiddenCost.cap (GraphView.costGame (truncateHash parameterOutput)
    (GraphView.publicData (labelsOf (splitMaterial parameterOutput highs remaining fixed)
      (splitAnswers highs remaining fixed))) adversary) q

theorem hiddenRun_eq (adversary : Adversary) (q : Nat) (parameterOutput : HashOutput)
    (fixed : HiddenGraph.Table) (highs : CoordinateHighs) (remaining : RemainingOutputs)
    (outsideTable : Eager.Table) (table : HiddenGraph.Table) :
    hiddenRun adversary q parameterOutput fixed highs remaining outsideTable table =
      Stop.costRun (HiddenRows.answer (sampleModel parameterOutput highs) table
        (outsideFn (splitMaterial parameterOutput highs remaining fixed)
          (splitAnswers highs remaining fixed) outsideTable)) table
        (sampleProgram adversary q parameterOutput fixed highs remaining) := by
  unfold hiddenRun sampleModel sampleProgram
  rw [rowModel_answer]

/-- **Seed-free to stopped.** Every event of the seed-free experiment is bounded by the same
event or a hidden-input stop in the existing stopped hidden-row experiment, averaged over the
public and structural samples. -/
theorem seedFree_le_stopped (adversary : Adversary) (q : Nat)
    (event : Option Bool × List (HiddenCost.Entry HashInput) → Prop) :
    Pr{let x ← seedFreeExperiment adversary q}[event x] ≤
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
            (sampleProgram adversary q parameterOutput fixed highs remaining)))
          (knownOf (truncateHash parameterOutput) fixed))}[(HiddenReveal.StopOr event) x] := by
  rw [(evalDist_seedFree_completion adversary q).prEvent_eq]
  refine probEvent_bind_mono_support _ _ _ _ _ fun parameterOutput _ => ?_
  refine probEvent_bind_mono_support _ _ _ _ _ fun fixed _ => ?_
  refine probEvent_bind_mono_support _ _ _ _ _ fun highs _ => ?_
  refine probEvent_bind_mono_support _ _ _ _ _ fun remaining _ => ?_
  refine probEvent_bind_mono_support _ _ _ _ _ fun outsideTable _ => ?_
  unfold HiddenRows.stoppedExperiment
  rw [(evalDist_completion_bind _ _).prEvent_eq, (evalDist_completion_bind _ _).prEvent_eq]
  refine probEvent_bind_mono_support _ _ _ _ _ fun fresh _ => ?_
  have hagree := HiddenRows.knownAgrees_completion (knownOf (truncateHash parameterOutput) fixed) fresh
  have h := costRun_le_stopped (sampleModel parameterOutput highs)
    (tableExtending (knownOf (truncateHash parameterOutput) fixed) fresh)
    (outsideFn (splitMaterial parameterOutput highs remaining fixed)
      (splitAnswers highs remaining fixed) outsideTable)
    (sampleProgram adversary q parameterOutput fixed highs remaining)
    (knownOf (truncateHash parameterOutput) fixed) hagree event
  rw [hiddenRun_eq]
  exact h

end SphincsFors.Security.HiddenBridge
