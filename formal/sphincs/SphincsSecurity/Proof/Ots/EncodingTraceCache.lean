import SphincsSecurity.Proof.Ots.EncodingOracleObservation
import SphincsSecurity.Proof.Ots.OtsEncodingMarker
import SphincsSecurity.Proof.Base.QueryTraceInvariant
namespace SphincsSecurity.Concrete.EncodingObservation

open _root_.OracleComp OracleSpec UniformTableCompletion RetainedObservation
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
attribute [local irreducible] canonicalEncodingInputs Finset.univ

def TraceConsistent (parameter : PublicParameter)
    (initial : canonicalEncodingInputs parameter → Finset HashOutput) (trace : OtsContactTrace.Trace)
    (allowed : canonicalEncodingInputs parameter → Finset HashOutput) : Prop :=
  (∀ cell output, (cell.val, output) ∈ trace.toList → allowed cell = {output}) ∧
    ∀ cell, (∀ output, (cell.val, output) ∉ trace.toList) → allowed cell = initial cell

theorem traceConsistent_one (parameter : PublicParameter)
    (initial : canonicalEncodingInputs parameter → Finset HashOutput) :
    TraceConsistent parameter initial 1 initial := by
  constructor
  · simp
  · intros; rfl

theorem TraceConsistent.outside {parameter : PublicParameter}
    {initial allowed : canonicalEncodingInputs parameter → Finset HashOutput} {trace : OtsContactTrace.Trace}
    (h : TraceConsistent parameter initial trace allowed) (input : HashInput)
    (houtside : input ∉ canonicalEncodingInputs parameter) (output : HashOutput) :
    TraceConsistent parameter initial (trace * FreeMonoid.of (input, output)) allowed := by
  constructor
  · intro cell answer hentry
    simp only [FreeMonoid.toList_mul, FreeMonoid.toList_of, List.mem_append,
      List.mem_singleton, Prod.mk.injEq] at hentry
    rcases hentry with hentry | ⟨heq, _⟩
    · exact h.1 cell answer hentry
    · exact False.elim (houtside (heq ▸ cell.property))
  · intro cell hfresh
    apply h.2 cell
    intro answer hentry
    apply hfresh answer
    exact List.mem_append_left _ hentry

theorem TraceConsistent.disclose {parameter : PublicParameter}
    {initial allowed : canonicalEncodingInputs parameter → Finset HashOutput} {trace : OtsContactTrace.Trace}
    (h : TraceConsistent parameter initial trace allowed) (cell : canonicalEncodingInputs parameter)
    (output : HashOutput) (houtput : output ∈ allowed cell) :
    TraceConsistent parameter initial (trace * FreeMonoid.of (cell.val, output))
      (discloseTableValue allowed cell output) := by
  constructor
  · intro other answer hentry
    simp only [FreeMonoid.toList_mul, FreeMonoid.toList_of, List.mem_append,
      List.mem_singleton, Prod.mk.injEq] at hentry
    rcases hentry with hentry | ⟨heq, rfl⟩
    · by_cases heq : other = cell
      · subst other
        have heq : output = answer := Finset.mem_singleton.mp ((h.1 cell answer hentry) ▸ houtput)
        simp only [discloseTableValue, Function.update_self, heq]
      · rw [discloseTableValue, Function.update_of_ne heq]
        exact h.1 other answer hentry
    · have heq : other = cell := Subtype.ext heq
      subst other
      exact Function.update_self cell {answer} allowed
  · intro other hfresh
    have heq : other ≠ cell := by
      intro heq
      subst other
      exact hfresh output (List.mem_append_right _ (by simp))
    rw [discloseTableValue, Function.update_of_ne heq]
    apply h.2 other
    intro answer hentry
    exact hfresh answer (List.mem_append_left _ hentry)

noncomputable def lazyWorldImpl (parameter : PublicParameter) (inputs : Finset HashInput)
    (hencoding : canonicalEncodingInputs parameter ⊆ inputs) (outside : NonencodingRows parameter inputs hencoding) :
    QueryImpl OracleWorld (StateT (canonicalEncodingInputs parameter → Finset HashOutput) SPMF) :=
  (UniformTableObservation.lazyImpl (auxiliary parameter inputs hencoding outside)).compose (translate parameter)

theorem lazyRun_eq_simulate {Result : Type} (parameter : PublicParameter) (inputs : Finset HashInput)
    (hencoding : canonicalEncodingInputs parameter ⊆ inputs) (outside : NonencodingRows parameter inputs hencoding)
    (computation : OracleComp OracleWorld Result) (allowed : canonicalEncodingInputs parameter → Finset HashOutput) :
    lazyRun parameter inputs hencoding outside computation allowed =
      (simulateQ (lazyWorldImpl parameter inputs hencoding outside) computation).run allowed := by
  rw [lazyRun, UniformTableObservation.lazyRun, lazyWorldImpl, QueryImpl.simulateQ_compose]

theorem lazyRun_map {Result Next : Type} (parameter : PublicParameter) (inputs : Finset HashInput)
    (hencoding : canonicalEncodingInputs parameter ⊆ inputs) (outside : NonencodingRows parameter inputs hencoding)
    (computation : OracleComp OracleWorld Result) (f : Result → Next)
    (allowed : canonicalEncodingInputs parameter → Finset HashOutput) :
    lazyRun parameter inputs hencoding outside (f <$> computation) allowed =
      (fun result => (f result.1, result.2)) <$> lazyRun parameter inputs hencoding outside computation allowed := by
  simp only [lazyRun_eq_simulate, simulateQ_map, StateT.run_map]

theorem lazyWorldImpl_traceConsistent (parameter : PublicParameter) (inputs : Finset HashInput)
    (hencoding : canonicalEncodingInputs parameter ⊆ inputs) (outside : NonencodingRows parameter inputs hencoding)
    (initial allowed : canonicalEncodingInputs parameter → Finset HashOutput) (trace : OtsContactTrace.Trace)
    (h : TraceConsistent parameter initial trace allowed) (input : OracleWorld.Domain)
    (result : OracleWorld.Range input × (canonicalEncodingInputs parameter → Finset HashOutput))
    (hr : (lazyWorldImpl parameter inputs hencoding outside input).run allowed result ≠ 0) :
    TraceConsistent parameter initial (trace * hashObservationTrace input result.1) result.2 := by
  cases input with
  | inl input =>
      simp only [lazyWorldImpl, QueryImpl.compose, translate, simulateQ_spec_query,
        UniformTableObservation.lazyImpl, StateT.run_mk, ← bind_pure_comp] at hr
      obtain ⟨answer, _, heq⟩ := (bind_nonzero _ _ _).mp hr
      simp only [ne_eq, SPMF.pure_apply_eq_zero_iff, not_not] at heq
      subst result
      simpa only [hashObservationTrace, mul_one] using h
  | inr input =>
      by_cases hc : input ∈ canonicalEncodingInputs parameter
      · simp only [lazyWorldImpl, QueryImpl.compose, translate, dif_pos hc, simulateQ_spec_query,
          UniformTableObservation.lazyImpl, StateT.run_mk, ← bind_pure_comp] at hr
        obtain ⟨answer, ha, heq⟩ := (bind_nonzero _ _ _).mp hr
        simp only [ne_eq, SPMF.pure_apply_eq_zero_iff, not_not] at heq
        subst result
        have hin : answer ∈ allowed ⟨input, hc⟩ := by
          by_contra hn
          simp only [cell_apply, if_neg hn, ne_eq, not_true_eq_false] at ha
        exact h.disclose ⟨input, hc⟩ answer hin
      · simp only [lazyWorldImpl, QueryImpl.compose, translate, dif_neg hc, simulateQ_spec_query,
          UniformTableObservation.lazyImpl, StateT.run_mk, ← bind_pure_comp] at hr
        obtain ⟨answer, _, heq⟩ := (bind_nonzero _ _ _).mp hr
        simp only [ne_eq, SPMF.pure_apply_eq_zero_iff, not_not] at heq
        subst result
        exact h.outside input hc answer

theorem TraceConsistent.cached_reply {parameter : PublicParameter}
    {initial allowed : canonicalEncodingInputs parameter → Finset HashOutput} {trace : OtsContactTrace.Trace}
    (h : TraceConsistent parameter initial trace allowed) (cell : canonicalEncodingInputs parameter)
    (previous output : HashOutput) (hp : (cell.val, previous) ∈ trace.toList)
    (ho : UniformTableCompletion.cell (allowed cell) output ≠ 0) : output = previous := by
  rw [h.1 cell previous hp, cell_apply] at ho
  by_contra hn
  simp only [Finset.mem_singleton, hn, if_false, ne_eq, not_true_eq_false] at ho

theorem TraceConsistent.new_reply_probability_le {parameter : PublicParameter}
    {initial allowed : canonicalEncodingInputs parameter → Finset HashOutput} {trace : OtsContactTrace.Trace}
    (h : TraceConsistent parameter initial trace allowed) (cell : canonicalEncodingInputs parameter)
    (event : HashOutput → Prop) :
    Pr[fun output => event output ∧ (cell.val, output) ∉ trace.toList | UniformTableCompletion.cell (allowed cell)] ≤
      Pr[event | UniformTableCompletion.cell (initial cell)] := by
  by_cases hfresh : ∀ output, (cell.val, output) ∉ trace.toList
  · rw [h.2 cell hfresh]
    exact _root_.probEvent_mono (fun _ _ he => he.1)
  · obtain ⟨previous, hp⟩ := not_forall.mp hfresh
    have hp : (cell.val, previous) ∈ trace.toList := not_not.mp hp
    have hz : Pr[fun output => event output ∧ (cell.val, output) ∉ trace.toList |
        UniformTableCompletion.cell (allowed cell)] = 0 := by
      apply probEvent_eq_zero
      intro output ho he
      have heq := h.cached_reply cell previous output hp ((SPMF.mem_support_iff _ _).mp ho)
      exact he.2 (heq.symm ▸ hp)
    rw [hz]
    exact bot_le

end SphincsSecurity.Concrete.EncodingObservation
