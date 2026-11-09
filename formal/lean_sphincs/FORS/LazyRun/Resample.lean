module

public import FORS.LazyRun.HiddenOracle

@[expose] public section

/-! Resampling the hidden coordinates: the seed-free experiment is an average, over every
public and structural sample, of the hidden-row run whose coordinate table is an exact
uniform completion of the known coordinates. -/

open OracleComp OracleSpec ENNReal

namespace FORS.Security.HiddenBridge

variable [Params]

open Completeness SeedModel Graph Assembly Reduce HiddenGraph
open UniformTableSplit

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
attribute [local instance] Classical.propDecidable

/-- Swapping the known parts of two tables is an involution. -/
noncomputable def swapKnown (parameter : PublicParameter) (pair : HiddenGraph.Table × HiddenGraph.Table) :
    HiddenGraph.Table × HiddenGraph.Table :=
  (mix parameter pair.1 pair.2, mix parameter pair.2 pair.1)

theorem swapKnown_involutive (parameter : PublicParameter) :
    Function.Involutive (swapKnown parameter) := by
  intro pair
  apply Prod.ext <;> funext coordinate <;>
    by_cases h : KnownCoordinate parameter coordinate <;> simp [swapKnown, mix, h]

theorem uniform_map_fst {α β : Type} [Fintype α] [Fintype β] [Nonempty α] [Nonempty β] :
    (Cslib.Probability.PMF.uniformOfFintype (α × β)).map Prod.fst = Cslib.Probability.PMF.uniformOfFintype α := by
  rw [uniform_product, PMF.map_bind]
  simp only [PMF.map_comp, Function.comp_def]
  have hconst : ∀ a : α, PMF.map (fun _ : β => a) (Cslib.Probability.PMF.uniformOfFintype β) = PMF.pure a :=
    fun a => PMF.map_const _ a
  simp only [hconst]
  exact PMF.bind_pure _

theorem uniform_mix (parameter : PublicParameter) :
    (Cslib.Probability.PMF.uniformOfFintype HiddenGraph.Table).bind (fun fixed =>
      (Cslib.Probability.PMF.uniformOfFintype HiddenGraph.Table).map (mix parameter fixed)) =
      Cslib.Probability.PMF.uniformOfFintype HiddenGraph.Table := by
  have hpair : (Cslib.Probability.PMF.uniformOfFintype HiddenGraph.Table).bind (fun fixed =>
      (Cslib.Probability.PMF.uniformOfFintype HiddenGraph.Table).map (mix parameter fixed)) =
      ((Cslib.Probability.PMF.uniformOfFintype (HiddenGraph.Table × HiddenGraph.Table)).map (swapKnown parameter)).map
        Prod.fst := by
    rw [PMF.map_comp, uniform_product, PMF.map_bind]
    simp only [PMF.map_comp, Function.comp_def, swapKnown]
  rw [hpair, Cslib.Probability.PMF.uniformOfFintype_map_of_bijective _ (swapKnown_involutive parameter).bijective,
    uniform_map_fst]

theorem evalDist_uniform_congr {α : Type} [Fintype α] [Nonempty α] (left right : SampleableType α) :
    (@uniformSample α left : ProbComp α) =ᵈ (@uniformSample α right : ProbComp α) := by
  exact EvalDistEq.of_forall_prEvent_eq fun p => SampleableType.prEvent_uniformSample_inst_irrel left right p

noncomputable local instance sampleCellFintypeInst : Fintype SampleCell := sampleCellFintype
noncomputable local instance sampleCellDecEq : DecidableEq SampleCell := Classical.decEq _
noncomputable local instance hiddenTableSampleable : SampleableType HiddenGraph.Table :=
  SampleableType.ofFintype _
noncomputable local instance highsSampleable : SampleableType CoordinateHighs := SampleableType.ofFintype _
noncomputable local instance remainingSampleable : SampleableType RemainingOutputs :=
  SampleableType.ofFintype _

omit [Params] in
private theorem uniformSample_evalDistEq_pmf (T : Type) [Fintype T] [Nonempty T] [SampleableType T] :
    ($ᵗ T : ProbComp T) =ᵈ Cslib.Probability.PMF.uniformOfFintype T := by
  refine evalDistEq_iff_forall_prEvent_eq_output.mpr fun x => ?_
  rw [SampleableType.prEvent_uniformSample_eq_singleton, PMF.probOutput_eq_apply,
    Cslib.Probability.PMF.uniformOfFintype_apply]

theorem evalDist_mix (parameter : PublicParameter) :
    (($ᵗ HiddenGraph.Table) >>= fun fixed => mix parameter fixed <$> ($ᵗ HiddenGraph.Table)) =ᵈ ($ᵗ HiddenGraph.Table : ProbComp HiddenGraph.Table) := by
  have hu := uniformSample_evalDistEq_pmf HiddenGraph.Table
  refine (hu.bind fun fixed => hu.map (mix parameter fixed)).trans ?_
  rw [show ((Cslib.Probability.PMF.uniformOfFintype HiddenGraph.Table) >>= fun fixed =>
      mix parameter fixed <$> Cslib.Probability.PMF.uniformOfFintype HiddenGraph.Table) =
        Cslib.Probability.PMF.uniformOfFintype HiddenGraph.Table from uniform_mix parameter]
  exact hu.symm

theorem evalDist_mix_bind {β : Type} (parameter : PublicParameter) (next : HiddenGraph.Table → ProbComp β) :
    (($ᵗ HiddenGraph.Table) >>= next) =ᵈ (($ᵗ HiddenGraph.Table) >>= fun fixed => ($ᵗ HiddenGraph.Table) >>= fun fresh =>
        next (mix parameter fixed fresh)) := by
  have h := (evalDist_mix parameter).bind_left next
  simp only [bind_assoc, bind_map_left] at h
  exact h.symm

theorem evalDist_completion_bind {β : Type} (known : HiddenReveal.Knowledge Coordinate)
    (next : HiddenGraph.Table → ProbComp β) :
    (HiddenReveal.completion known >>= next) =ᵈ (($ᵗ HiddenGraph.Table) >>= fun fresh => next (tableExtending known fresh)) := by
  unfold HiddenReveal.completion
  refine (Eager.evalDist_map_bind' _ _ _).trans ?_
  exact (evalDist_uniform_congr HiddenReveal.tableSampleable hiddenTableSampleable).bind_left _

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

end FORS.Security.HiddenBridge
