import SphincsSecurity.Proof.Base.Prelude
import SphincsSecurity.Proof.Fts.FewTimeTargetCompletion
namespace SphincsSecurity.Concrete

open OracleComp OracleSpec ENNReal
attribute [local instance] Classical.propDecidable

theorem probEvent_completeOption_eq {α β : Type} (comp : ProbComp α)
    (selected : α → Option β) (fallback : ProbComp β) (P : β → Prop) :
    Pr[P | comp >>= fun result => (selected result).elim fallback pure] =
      Pr[fun result => ∃ value, selected result = some value ∧ P value | comp] +
        Pr[fun result => selected result = none | comp] * Pr[P | fallback] := by
  rw [probEvent_bind_eq_tsum,
    probEvent_eq_tsum_ite comp (fun result => ∃ value, selected result = some value ∧ P value),
    probEvent_eq_tsum_ite comp (fun result => selected result = none),
    ← ENNReal.tsum_mul_right, ← ENNReal.tsum_add]
  apply tsum_congr
  intro result
  cases selected result with
  | none => simp [Option.elim]
  | some value => simp [Option.elim, probEvent_pure, mul_ite]

theorem probEvent_selectedOption_le_mass_mul {α β : Type} (comp : ProbComp α)
    (selected : α → Option β) (fallback : ProbComp β) (P : β → Prop)
    (hfail : Pr[⊥ | comp] = 0)
    (hcomplete : Pr[P | comp >>= fun result => (selected result).elim fallback pure] ≤
      Pr[P | fallback]) :
    Pr[fun result => ∃ value, selected result = some value ∧ P value | comp] ≤
      Pr[fun result => selected result ≠ none | comp] * Pr[P | fallback] := by
  have hmass : Pr[fun result => selected result ≠ none | comp] +
      Pr[fun result => selected result = none | comp] = 1 := by
    simpa only [not_not, hfail, tsub_zero] using
      probEvent_compl comp (fun result => selected result ≠ none)
  apply ENNReal.le_of_add_le_add_right (a :=
    Pr[fun result => selected result = none | comp] * Pr[P | fallback])
    (ENNReal.mul_ne_top probEvent_ne_top probEvent_ne_top)
  calc
    _ = Pr[P | comp >>= fun result => (selected result).elim fallback pure] :=
      (probEvent_completeOption_eq comp selected fallback P).symm
    _ ≤ Pr[P | fallback] := hcomplete
    _ = _ := by rw [← add_mul, hmass, one_mul]

theorem probEvent_selectedOption_eq_mass_mul {α β : Type} (comp : ProbComp α)
    (selected : α → Option β) (fallback : ProbComp β) (P : β → Prop)
    (hfail : Pr[⊥ | comp] = 0) (hfallback : Pr[⊥ | fallback] = 0)
    (hcomplete : ∀ Q : β → Prop,
      Pr[Q | comp >>= fun result => (selected result).elim fallback pure] ≤ Pr[Q | fallback]) :
    Pr[fun result => ∃ value, selected result = some value ∧ P value | comp] =
      Pr[fun result => selected result ≠ none | comp] * Pr[P | fallback] := by
  have hparts :
      Pr[fun result => ∃ value, selected result = some value ∧ P value | comp] +
        Pr[fun result => ∃ value, selected result = some value ∧ ¬ P value | comp] =
      Pr[fun result => selected result ≠ none | comp] := by
    simp only [probEvent_eq_tsum_ite, ← ENNReal.tsum_add]
    apply tsum_congr
    intro result
    cases selected result with
    | none => simp
    | some value => by_cases hP : P value <;> simp [hP]
  have hfallbackMass : Pr[P | fallback] + Pr[fun value => ¬ P value | fallback] = 1 := by
    simpa only [hfallback, tsub_zero] using probEvent_compl fallback P
  apply le_antisymm (probEvent_selectedOption_le_mass_mul comp selected fallback P hfail (hcomplete P))
  apply ENNReal.le_of_add_le_add_right (a :=
    Pr[fun result => selected result ≠ none | comp] * Pr[fun value => ¬ P value | fallback])
    (ENNReal.mul_ne_top probEvent_ne_top probEvent_ne_top)
  calc
    _ = Pr[fun result => selected result ≠ none | comp] := by
      rw [← mul_add, hfallbackMass, mul_one]
    _ = _ := hparts.symm
    _ ≤ _ := add_le_add le_rfl (probEvent_selectedOption_le_mass_mul comp selected fallback
      (fun value => ¬ P value) hfail (hcomplete _))

theorem freshSelectedLoopView?_satisfies_iff
    (referenceCache : QueryCache HashSpec) (key : SecretKey) (message : Message)
    (P : FewTimeView → Prop)
    (result : Option (Randomness × Index × (IndexGroup → FtsLeaf)) × QueryCache HashSpec) :
    (∃ view, freshSelectedLoopView? referenceCache key message result = some view ∧ P view) ↔
      FreshSelectedView referenceCache key message P result := by
  cases hresult : result.1 with
  | none => simp [freshSelectedLoopView?, FreshSelectedView, hresult]
  | some selected =>
      rcases selected with ⟨randomness, index, leaves⟩
      by_cases hfresh : referenceCache (tweakableHashInput key.parameter .message
          (messageDigestPayload key.root message randomness)) = none
      · simp [freshSelectedLoopView?, FreshSelectedView, hresult, hfresh]
      · simp [freshSelectedLoopView?, FreshSelectedView, hresult, hfresh]

theorem completeFreshSelectedLoopView_eq_elim
    (referenceCache : QueryCache HashSpec) (key : SecretKey) (message : Message)
    (result : Option (Randomness × Index × (IndexGroup → FtsLeaf)) × QueryCache HashSpec) :
    completeFreshSelectedLoopView referenceCache key message result =
      (freshSelectedLoopView? referenceCache key message result).elim
        ($ᵗ FewTimeView) pure := by
  unfold completeFreshSelectedLoopView
  cases freshSelectedLoopView? referenceCache key message result <;> rfl

theorem probEvent_signDigestLoop_freshSelected_eq_mass_mul_uniform
    (attempts : Nat) (key : SecretKey) (message : Message)
    (referenceCache workingCache : QueryCache HashSpec) (P : FewTimeView → Prop)
    (hinvariant : OnlyRejectedNewMessageEntries referenceCache workingCache key message) :
    Pr[FreshSelectedView referenceCache key message P |
      (simulateQ romImpl (signDigestLoop attempts key message)).run workingCache] =
      Pr[fun result => freshSelectedLoopView? referenceCache key message result ≠ none |
        (simulateQ romImpl (signDigestLoop attempts key message)).run workingCache] *
          Pr[P | ($ᵗ FewTimeView : ProbComp FewTimeView)] := by
  have h := probEvent_selectedOption_eq_mass_mul
    ((simulateQ romImpl (signDigestLoop attempts key message)).run workingCache)
    (freshSelectedLoopView? referenceCache key message) ($ᵗ FewTimeView) P
    (by simp) (by simp) (by
      intro Q
      simpa only [funext (completeFreshSelectedLoopView_eq_elim referenceCache key message)] using
        (probEvent_completeFreshSelectedLoopView_le_uniform attempts key message
          referenceCache workingCache Q hinvariant))
  simpa only [freshSelectedLoopView?_satisfies_iff] using h

noncomputable def freshDigestSelectionProbability
    (key : SecretKey) (message : Message) (cache : QueryCache HashSpec) : ENNReal :=
  Pr[fun result => freshSelectedLoopView? cache key message result ≠ none |
    (simulateQ romImpl (signDigestLoop digestAttemptLimit key message)).run cache]

theorem freshDigestSelectionProbability_le_one
    (key : SecretKey) (message : Message) (cache : QueryCache HashSpec) :
    freshDigestSelectionProbability key message cache ≤ 1 := probEvent_le_one

end SphincsSecurity.Concrete
