import SphincsSecurity.Proof.Hypertree.StructuralOracleObservation
namespace SphincsSecurity.Concrete.StructuralObservation

open _root_.OracleComp OracleSpec UniformTableCompletion RetainedObservation
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
attribute [local irreducible] structuralInputs canonicalGraphInputs Finset.univ

def TraceConsistent (key : SecretKey) (inputs : Finset HashInput) (labels : CanonicalGraphLabels)
    (trace : OtsContactTrace.Trace) (allowed : structuralInputs key.parameter inputs → Finset HashOutput) : Prop :=
  (∀ row, Active key inputs labels row.val → ∀ output, (row.val, output) ∈ trace.toList → allowed row = {output}) ∧
    ∀ row, Active key inputs labels row.val → (∀ output, (row.val, output) ∉ trace.toList) → allowed row = Finset.univ

theorem traceConsistent_one (key : SecretKey) (inputs : Finset HashInput) (labels : CanonicalGraphLabels) :
    TraceConsistent key inputs labels 1 (fun _ => Finset.univ) := by
  constructor
  · simp
  · intros; rfl

theorem TraceConsistent.inactive {key : SecretKey} {inputs : Finset HashInput} {labels : CanonicalGraphLabels}
    {trace : OtsContactTrace.Trace} {allowed : structuralInputs key.parameter inputs → Finset HashOutput}
    (h : TraceConsistent key inputs labels trace allowed) (input : HashInput) (hi : ¬Active key inputs labels input) (output : HashOutput) :
    TraceConsistent key inputs labels (trace * FreeMonoid.of (input, output)) allowed := by
  constructor
  · intro row ha answer hentry
    simp only [FreeMonoid.toList_mul, FreeMonoid.toList_of, List.mem_append, List.mem_singleton, Prod.mk.injEq] at hentry
    rcases hentry with hentry | ⟨heq, _⟩
    · exact h.1 row ha answer hentry
    · exact False.elim (hi (heq ▸ ha))
  · intro row ha hfresh
    apply h.2 row ha
    intro answer hentry
    exact hfresh answer (List.mem_append_left _ hentry)

theorem TraceConsistent.disclose {key : SecretKey} {inputs : Finset HashInput} {labels : CanonicalGraphLabels}
    {trace : OtsContactTrace.Trace} {allowed : structuralInputs key.parameter inputs → Finset HashOutput}
    (h : TraceConsistent key inputs labels trace allowed) (row : structuralInputs key.parameter inputs)
    (ha : Active key inputs labels row.val) (output : HashOutput) (houtput : output ∈ allowed row) :
    TraceConsistent key inputs labels (trace * FreeMonoid.of (row.val, output)) (discloseTableValue allowed row output) := by
  constructor
  · intro other hactive answer hentry
    simp only [FreeMonoid.toList_mul, FreeMonoid.toList_of, List.mem_append, List.mem_singleton, Prod.mk.injEq] at hentry
    rcases hentry with hentry | ⟨heq, rfl⟩
    · by_cases heq : other = row
      · subst other
        have heq : output = answer := Finset.mem_singleton.mp ((h.1 row ha answer hentry) ▸ houtput)
        simp only [discloseTableValue, Function.update_self, heq]
      · rw [discloseTableValue, Function.update_of_ne heq]
        exact h.1 other hactive answer hentry
    · have heq : other = row := Subtype.ext heq
      subst other
      exact Function.update_self row {answer} allowed
  · intro other hactive hfresh
    have heq : other ≠ row := by
      intro heq
      subst other
      exact hfresh output (List.mem_append_right _ (by simp))
    rw [discloseTableValue, Function.update_of_ne heq]
    apply h.2 other hactive
    intro answer hentry
    exact hfresh answer (List.mem_append_left _ hentry)

noncomputable def lazyWorldImpl (key : SecretKey) (inputs : Finset HashInput) (labels : CanonicalGraphLabels)
    (outside : NonstructuralRows key.parameter inputs) :
    QueryImpl OracleWorld (StateT (structuralInputs key.parameter inputs → Finset HashOutput) SPMF) :=
  (UniformTableObservation.lazyImpl (auxiliary key inputs labels outside)).compose (translate key inputs labels)

theorem lazyRun_eq_simulate {Result : Type} (key : SecretKey) (inputs : Finset HashInput) (labels : CanonicalGraphLabels)
    (outside : NonstructuralRows key.parameter inputs) (computation : OracleComp OracleWorld Result)
    (allowed : structuralInputs key.parameter inputs → Finset HashOutput) :
    lazyRun key inputs labels outside computation allowed = (simulateQ (lazyWorldImpl key inputs labels outside) computation).run allowed := by
  rw [lazyRun, UniformTableObservation.lazyRun, lazyWorldImpl, QueryImpl.simulateQ_compose]

theorem lazyRun_map {Result Next : Type} (key : SecretKey) (inputs : Finset HashInput) (labels : CanonicalGraphLabels)
    (outside : NonstructuralRows key.parameter inputs) (computation : OracleComp OracleWorld Result) (f : Result → Next)
    (allowed : structuralInputs key.parameter inputs → Finset HashOutput) :
    lazyRun key inputs labels outside (f <$> computation) allowed =
      (fun result => (f result.1, result.2)) <$> lazyRun key inputs labels outside computation allowed := by
  simp only [lazyRun_eq_simulate, simulateQ_map, StateT.run_map]

theorem lazyWorldImpl_traceConsistent (key : SecretKey) (inputs : Finset HashInput) (labels : CanonicalGraphLabels)
    (outside : NonstructuralRows key.parameter inputs) (allowed : structuralInputs key.parameter inputs → Finset HashOutput)
    (trace : OtsContactTrace.Trace) (h : TraceConsistent key inputs labels trace allowed) (input : OracleWorld.Domain)
    (result : OracleWorld.Range input × (structuralInputs key.parameter inputs → Finset HashOutput))
    (hr : (lazyWorldImpl key inputs labels outside input).run allowed result ≠ 0) :
    TraceConsistent key inputs labels (trace * hashObservationTrace input result.1) result.2 := by
  cases input with
  | inl input =>
      simp only [lazyWorldImpl, QueryImpl.compose, translate, simulateQ_spec_query,
        UniformTableObservation.lazyImpl, StateT.run_mk, ← bind_pure_comp] at hr
      obtain ⟨answer, _, heq⟩ := (bind_nonzero _ _ _).mp hr
      simp only [ne_eq, SPMF.pure_apply_eq_zero_iff, not_not] at heq
      subst result
      simpa only [hashObservationTrace, mul_one] using h
  | inr input =>
      by_cases ha : Active key inputs labels input
      · simp only [lazyWorldImpl, QueryImpl.compose, translate, dif_pos ha, simulateQ_spec_query,
          UniformTableObservation.lazyImpl, StateT.run_mk, ← bind_pure_comp] at hr
        obtain ⟨answer, ho, heq⟩ := (bind_nonzero _ _ _).mp hr
        simp only [ne_eq, SPMF.pure_apply_eq_zero_iff, not_not] at heq
        subst result
        have hin : answer ∈ allowed ⟨input, ha.1⟩ := by
          by_contra hn
          simp only [cell_apply, if_neg hn, ne_eq, not_true_eq_false] at ho
        exact h.disclose ⟨input, ha.1⟩ ha answer hin
      · simp only [lazyWorldImpl, QueryImpl.compose, translate, dif_neg ha, simulateQ_spec_query,
          UniformTableObservation.lazyImpl, StateT.run_mk, ← bind_pure_comp] at hr
        obtain ⟨answer, _, heq⟩ := (bind_nonzero _ _ _).mp hr
        simp only [ne_eq, SPMF.pure_apply_eq_zero_iff, not_not] at heq
        subst result
        exact h.inactive input ha answer

theorem TraceConsistent.cached_reply {key : SecretKey} {inputs : Finset HashInput} {labels : CanonicalGraphLabels}
    {trace : OtsContactTrace.Trace} {allowed : structuralInputs key.parameter inputs → Finset HashOutput}
    (h : TraceConsistent key inputs labels trace allowed) (row : structuralInputs key.parameter inputs)
    (ha : Active key inputs labels row.val) (previous output : HashOutput) (hp : (row.val, previous) ∈ trace.toList)
    (ho : cell (allowed row) output ≠ 0) : output = previous := by
  rw [h.1 row ha previous hp, cell_apply] at ho
  by_contra hn
  simp only [Finset.mem_singleton, hn, if_false, ne_eq, not_true_eq_false] at ho

theorem TraceConsistent.new_reply_probability_le {key : SecretKey} {inputs : Finset HashInput} {labels : CanonicalGraphLabels}
    {trace : OtsContactTrace.Trace} {allowed : structuralInputs key.parameter inputs → Finset HashOutput}
    (h : TraceConsistent key inputs labels trace allowed) (row : structuralInputs key.parameter inputs)
    (ha : Active key inputs labels row.val) (event : HashOutput → Prop) :
    Pr[fun output => event output ∧ (row.val, output) ∉ trace.toList | cell (allowed row)] ≤ Pr[event | cell Finset.univ] := by
  by_cases hfresh : ∀ output, (row.val, output) ∉ trace.toList
  · rw [h.2 row ha hfresh]
    exact _root_.probEvent_mono (fun _ _ he => he.1)
  · obtain ⟨previous, hp⟩ := not_forall.mp hfresh
    have hp : (row.val, previous) ∈ trace.toList := not_not.mp hp
    have hz : Pr[fun output => event output ∧ (row.val, output) ∉ trace.toList | cell (allowed row)] = 0 := by
      apply probEvent_eq_zero
      intro output ho he
      have heq := h.cached_reply row ha previous output hp ((SPMF.mem_support_iff _ _).mp ho)
      exact he.2 (heq.symm ▸ hp)
    rw [hz]
    exact bot_le

theorem lazyRun_neverFail {Result : Type} (key : SecretKey) (inputs : Finset HashInput) (labels : CanonicalGraphLabels)
    (outside : NonstructuralRows key.parameter inputs) (computation : OracleComp OracleWorld Result)
    (allowed : structuralInputs key.parameter inputs → Finset HashOutput) (ha : ∀ row, (allowed row).Nonempty) :
    NeverFail (lazyRun key inputs labels outside computation allowed) := by
  apply UniformTableObservation.lazyRun_neverFail _ _ _ _ ha
  intro input
  exact ⟨probFailure_eq_zero (mx := fixedHashWorld (structuralAnswer key inputs labels outside (fun _ => 0)) input)⟩

end SphincsSecurity.Concrete.StructuralObservation
