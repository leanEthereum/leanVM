import VCVio.EvalDist.EvalDistEq
import VCVio.OracleComp.Constructions.SampleableType.Measure
import VCVio.OracleComp.EvalDist.Sum
import VCVio.EvalDist.Monad.UniformTable

/-! Elaboration aids for equality in distribution (`=ᵈ`). -/

universe v

/-- Elaborate both sides of `=ᵈ` against a common type, as `=` does, so a side whose monad is
only known from the other (a `do` block or `pure` in a `calc` step) elaborates. -/
macro_rules | `($a =ᵈ $b) => `(binrel% EvalDistEq $a $b)

/-- Syntactically equal computations are equal in distribution. -/
theorem EvalDistEq.of_eq {m : Type → Type v} [Monad m] [EvalDistSemantics m] {α : Type}
    {mx my : m α} (h : mx = my) : mx =ᵈ my :=
  h ▸ EvalDistEq.rfl

/-- Every uniform sampler of a type is equal in distribution to every other. -/
theorem SampleableType.uniformSample_evalDistEq_of_inst {A : Type} (i₁ i₂ : SampleableType A) :
    (@uniformSample A i₁) =ᵈ (@uniformSample A i₂) :=
  EvalDistEq.of_forall_prEvent_eq fun p => SampleableType.prEvent_uniformSample_inst_irrel i₁ i₂ p

/-- Overwriting one cell of a uniform table with an independent uniform value leaves the table
uniform, before any continuation. -/
theorem evalDistEq_uniformSample_bind_update {D R α : Type} [Finite D] [DecidableEq D] [Finite R]
    [Nonempty R] [SampleableType R] [SampleableType (D → R)] (t : D) (f : (D → R) → ProbComp α) :
    ($ᵗ R >>= fun u => $ᵗ (D → R) >>= fun g => f (Function.update g t u)) =ᵈ
      ($ᵗ (D → R) >>= f) := by
  refine evalDistEq_iff_evalDist_eq.mpr ?_
  let : MeasurableSpace R := ⊤
  let : MeasurableSpace α := ⊤
  exact evalDist_bind_bind_update ($ᵗ R) ($ᵗ (D → R)) SampleableType.evalDist_uniformSample
    SampleableType.evalDist_uniformSample t f

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
