import Mathlib.Probability.Distributions.Uniform
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import VCVio.OracleComp.Constructions.SampleableType.Measure
import VCVio.OracleComp.EvalDist.Sum
import VCVio.EvalDist.ProbabilityBounds
import VCVio.EvalDist.Monad.UniformTable

/-!
# Probability helpers

The output measure of a `PMF`, its monad equations, and uniform-table laws stated as equalities in
distribution.
-/

/-! `PMF` monad unfolding and uniform distributions under bijections (formerly in VCVio's
`ToMathlib.Probability.ProbabilityMassFunction.Lemmas`). -/

universe u

@[simp]
lemma PMF.monad_pure_eq_pure {α : Type u} (x : α) :
    (Pure.pure x : PMF α) = PMF.pure x := rfl

@[simp]
lemma PMF.monad_bind_eq_bind {α β : Type u}
      (p : PMF α) (q : α → PMF β) : p >>= q = p.bind q := rfl

open Classical in
lemma PMF.uniformOfFintype_map_of_bijective {α β : Type*} [Fintype α] [Fintype β]
    [Nonempty α] [Nonempty β] (f : α → β) (hf : Function.Bijective f) :
    (PMF.uniformOfFintype α).map f = PMF.uniformOfFintype β := by
  have heq := Fintype.card_congr (Equiv.ofBijective f hf)
  ext x; obtain ⟨a, rfl⟩ := hf.2 x
  simp only [PMF.map_apply, PMF.uniformOfFintype_apply, heq, hf.1.eq_iff, eq_comm (a := a)]
  convert tsum_ite_eq a (fun _ : α => ((Fintype.card β : ENNReal)⁻¹))

/-! The output measure of a `PMF` is `PMF.toMeasure`, so the event notation reads a `PMF` as it
reads any other computation (VCVio's earlier discrete layer gave `PMF` this semantics through its
lift to `SPMF`). -/

namespace PMF

open MeasureTheory

theorem toMeasure_eq_sum_dirac {α : Type*} [MeasurableSpace α] (p : PMF α) :
    p.toMeasure = Measure.sum fun a => p a • Measure.dirac a := by
  ext s hs
  rw [p.toMeasure_apply hs, Measure.sum_apply _ hs]
  refine tsum_congr fun a => ?_
  rw [Measure.smul_apply, Measure.dirac_apply' a hs, smul_eq_mul]
  by_cases ha : a ∈ s <;> simp [ha]

theorem lintegral_toMeasure {α : Type*} [MeasurableSpace α] (p : PMF α) {f : α → ENNReal}
    (hf : Measurable f) : ∫⁻ a, f a ∂p.toMeasure = ∑' a, p a * f a := by
  rw [toMeasure_eq_sum_dirac, lintegral_sum_measure]
  refine tsum_congr fun a => ?_
  rw [lintegral_smul_measure, lintegral_dirac' a hf, smul_eq_mul]

noncomputable instance instEvalDistSemantics : EvalDistSemantics PMF where
  denote p := p.toMeasure
  apply_univ_le_one p := by simp

instance instLawfulEvalDistSemantics : LawfulEvalDistSemantics PMF where
  denote_pure x := toMeasure_pure x
  denote_bind mx f hf := by
    ext s hs
    rw [Measure.bind_apply hs hf.aemeasurable]
    change (mx.bind f).toMeasure s = ∫⁻ a, (f a).toMeasure s ∂mx.toMeasure
    rw [toMeasure_bind_apply mx f s hs,
      lintegral_toMeasure mx (f := fun a => (f a).toMeasure s) ((Measure.measurable_coe hs).comp hf)]

theorem evalDist_eq_toMeasure {α : Type} [MeasurableSpace α] (p : PMF α) : 𝒟[p] = p.toMeasure :=
  rfl

/-- An event of a `PMF` has its outer measure. -/
theorem prEvent_eq_toOuterMeasure {α : Type} (p : PMF α) (q : α → Prop) :
    Pr{let x ← p}[q x] = p.toOuterMeasure {x | q x} := by
  let : MeasurableSpace α := ⊤
  rw [prEvent_eq_evalDist_of_discrete, evalDist_eq_toMeasure, toMeasure_apply_eq_toOuterMeasure]

/-- An event of a `PMF` is the sum of the masses of its outcomes. -/
theorem prEvent_eq_tsum_ite {α : Type} (p : PMF α) (q : α → Prop) [DecidablePred q] :
    Pr{let x ← p}[q x] = ∑' x, if q x then p x else 0 := by
  rw [prEvent_eq_toOuterMeasure, toOuterMeasure_apply]
  exact tsum_congr fun x => by by_cases h : q x <;> simp [Set.indicator, h]

/-- A point of a `PMF` has its mass. -/
@[simp] theorem probOutput_eq_apply {α : Type} (p : PMF α) (x : α) :
    Pr{let y ← p}[y = x] = p x := by
  classical
  rw [prEvent_eq_tsum_ite]
  simp

end PMF

/-- Resampling one cell of a uniform table leaves it uniform. -/
theorem uniformSample_bind_update_evalDistEq {D R : Type} [Finite D] [DecidableEq D] [Finite R]
    [Nonempty R] [SampleableType R] [SampleableType (D → R)] (t : D) :
    (do
      let u ← ($ᵗ R : ProbComp R)
      let g ← ($ᵗ (D → R) : ProbComp (D → R))
      pure (Function.update g t u)) =ᵈ ($ᵗ (D → R) : ProbComp (D → R)) := by
  let : MeasurableSpace R := ⊤
  have h := evalDist_bind_bind_update_map ($ᵗ R) ($ᵗ (D → R))
    SampleableType.evalDist_uniformSample SampleableType.evalDist_uniformSample t id
  simp only [id, bind_pure] at h
  exact EvalDistEq.of_evalDist_eq h

/-- Expose a uniform table cell before running a continuation that reads it. -/
theorem uniformSample_cell_extract_evalDistEq {D R α : Type} [Finite D] [DecidableEq D] [Finite R]
    [Nonempty R] [SampleableType R] [SampleableType (D → R)] (t : D)
    (next : (D → R) → R → ProbComp α) :
    (do let g ← ($ᵗ (D → R) : ProbComp (D → R)); next g (g t)) =ᵈ (do
      let u ← ($ᵗ R : ProbComp R)
      let g ← ($ᵗ (D → R) : ProbComp (D → R))
      next (Function.update g t u) u) := by
  let : MeasurableSpace R := ⊤
  let : MeasurableSpace α := ⊤
  exact EvalDistEq.of_evalDist_eq <| evalDist_bind_cell_extract ($ᵗ R) ($ᵗ (D → R))
    SampleableType.evalDist_uniformSample SampleableType.evalDist_uniformSample t next
