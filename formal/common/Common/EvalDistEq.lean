module

public import VCVio.EvalDist.EvalDistEq
public import VCVio.OracleComp.Constructions.SampleableType.Measure
public import VCVio.OracleComp.EvalDist.Sum
public import VCVio.EvalDist.Monad.UniformTable

@[expose] public section

/-! Generic facts about equality in distribution (`=ᵈ`) and uniform samplers. -/

universe v

/-- Syntactically equal computations are equal in distribution. -/
theorem EvalDistEq.of_eq {m : Type → Type v} [Monad m] [EvalDistSemantics m] {α : Type}
    {mx my : m α} (h : mx = my) : mx =ᵈ my :=
  h ▸ EvalDistEq.rfl

/-- Every uniform sampler of a type is equal in distribution to every other. -/
theorem SampleableType.uniformSample_evalDistEq_of_inst {A : Type} (i₁ i₂ : SampleableType A) :
    (@uniformSample A i₁) =ᵈ (@uniformSample A i₂) :=
  EvalDistEq.of_forall_prEvent_eq fun p => SampleableType.prEvent_uniformSample_inst_irrel i₁ i₂ p

/-- Two independent uniform draws are a uniform pair, for every sampler of the pair type. -/
theorem evalDist_independent_uniform_pair {α β : Type} [SampleableType α] [SampleableType β]
    [SampleableType (α × β)] :
    (do
      let left ← $ᵗ α
      let right ← $ᵗ β
      pure (left, right)) =ᵈ ($ᵗ (α × β)) :=
  (EvalDistEq.of_eq (SampleableType.uniformSample_prod_eq_bind α β).symm).trans
    (SampleableType.uniformSample_evalDistEq_of_inst _ _)

/-- Restricting a uniform table along an injection gives a uniform table. -/
theorem evalDistEq_uniformSample_map_comp_injective {A B R : Type} [Finite A] [Finite B]
    [Finite R] [Nonempty R] [SampleableType (A → R)] [SampleableType (B → R)]
    {e : A → B} (he : Function.Injective e) :
    ((fun g : B → R => g ∘ e) <$> ($ᵗ (B → R))) =ᵈ ($ᵗ (A → R)) :=
  let : MeasurableSpace R := ⊤
  EvalDistEq.of_evalDist_eq (evalDist_map_table_comp_injective ($ᵗ (A → R)) ($ᵗ (B → R))
    SampleableType.evalDist_uniformSample SampleableType.evalDist_uniformSample he)

open MeasureTheory in
/-- Continuation events within `ε` of each other at every possible output of a common prefix
stay within `ε` after the prefix. -/
theorem OracleComp.prEvent_bind_congr_le_add {ι : Type} {spec : OracleSpec ι}
    [OracleSpec.AnswerMeasure spec] {α β : Type} {mx : OracleComp spec α}
    {my oc : α → OracleComp spec β} {q : β → Prop} {ε : ENNReal}
    (h : ∀ x ∈ support mx, Pr{let y ← my x}[q y] ≤ Pr{let y ← oc x}[q y] + ε) :
    Pr{let y ← mx >>= my}[q y] ≤ Pr{let y ← mx >>= oc}[q y] + ε := by
  let : MeasurableSpace α := ⊤
  rw [prEvent_bind_eq_lintegral_of_discrete, prEvent_bind_eq_lintegral_of_discrete]
  calc ∫⁻ x, Pr{let y ← my x}[q y] ∂𝒟[mx]
      ≤ ∫⁻ x, (Pr{let y ← oc x}[q y] + ε) ∂𝒟[mx] :=
        lintegral_mono_ae (OracleComp.ae_evalDist_of_forall_mem_support mx h)
    _ = (∫⁻ x, Pr{let y ← oc x}[q y] ∂𝒟[mx]) + ε * 𝒟[mx] Set.univ := by
        rw [lintegral_add_right _ measurable_const, lintegral_const]
    _ ≤ (∫⁻ x, Pr{let y ← oc x}[q y] ∂𝒟[mx]) + ε := by
        gcongr
        exact mul_le_of_le_one_right' prob_le_one

open MeasureTheory in
/-- The expectation of a value over a `ProbComp` is the sum over its outcomes. -/
theorem OracleComp.lintegral_id_evalDist_map_eq_tsum {α : Type} (computation : ProbComp α)
    (f : α → ENNReal) :
    ∫⁻ r, r ∂𝒟[f <$> computation] = ∑' x, Pr{let y ← computation}[y = x] * f x := by
  let : MeasurableSpace α := ⊤
  rw [lintegral_evalDist_map computation .of_discrete measurable_id']
  exact lintegral_evalDist_eq_tsum computation f
