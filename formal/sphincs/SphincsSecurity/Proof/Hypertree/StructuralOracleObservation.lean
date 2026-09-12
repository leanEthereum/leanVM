import SphincsSecurity.Proof.Hypertree.StructuralMatchKernel
namespace SphincsSecurity.Concrete.StructuralObservation

open _root_.OracleComp OracleSpec UniformTableCompletion
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
attribute [local irreducible] canonicalGraphInputs canonicalEncodingInputs structuralInputs Finset.univ

def Active (key : SecretKey) (inputs : Finset HashInput) (labels : CanonicalGraphLabels) (input : HashInput) : Prop :=
  input ∈ structuralInputs key.parameter inputs ∧
    ∀ position, input ≠ canonicalGraphInput key.parameter key.otsSecret key.ftsSecret position labels

theorem answer_active (key : SecretKey) (inputs : Finset HashInput) (labels : CanonicalGraphLabels)
    (outside : NonstructuralRows key.parameter inputs) (rows : structuralInputs key.parameter inputs → HashOutput)
    (input : HashInput) (ha : Active key inputs labels input) :
    structuralAnswer key inputs labels outside rows input = rows ⟨input, ha.1⟩ := by
  rw [structuralAnswer, programmedHash_other _ _ _ _ _ input ha.2,
    finiteHashAnswer_none ∅ inputs _ input (structuralInputs_subset key.parameter inputs ha.1) (by simp)]
  exact UniformTableSplit.join_embed (structuralInputCell key.parameter inputs) (structuralInputCell_injective key.parameter inputs)
    rows outside ⟨input, ha.1⟩

theorem answer_inactive (key : SecretKey) (inputs : Finset HashInput) (labels : CanonicalGraphLabels)
    (outside : NonstructuralRows key.parameter inputs) (left right : structuralInputs key.parameter inputs → HashOutput)
    (input : HashInput) (ha : ¬Active key inputs labels input) :
    structuralAnswer key inputs labels outside left input = structuralAnswer key inputs labels outside right input := by
  by_cases hc : ∃ position, input = canonicalGraphInput key.parameter key.otsSecret key.ftsSecret position labels
  · obtain ⟨position, rfl⟩ := hc
    simp only [structuralAnswer, programmedHash_at]
  · have hn : ∀ position, input ≠ canonicalGraphInput key.parameter key.otsSecret key.ftsSecret position labels :=
      fun position he => hc ⟨position, he⟩
    have hout : input ∉ structuralInputs key.parameter inputs := fun hi => ha ⟨hi, hn⟩
    rw [structuralAnswer, structuralAnswer, programmedHash_other _ _ _ _ _ input hn,
      programmedHash_other _ _ _ _ _ input hn]
    exact joinStructuralTable_agrees_outside key.parameter inputs left right outside input hout

abbrev World (key : SecretKey) (inputs : Finset HashInput) :=
  OracleWorld + UniformTableObservation.TableSpec (structuralInputs key.parameter inputs) HashOutput

noncomputable def translate (key : SecretKey) (inputs : Finset HashInput) (labels : CanonicalGraphLabels) :
    QueryImpl OracleWorld (OracleComp (World key inputs))
  | .inl input => liftM ((World key inputs).query (.inl (.inl input)))
  | .inr input =>
      if h : Active key inputs labels input then liftM ((World key inputs).query (.inr ⟨input, h.1⟩))
      else liftM ((World key inputs).query (.inl (.inr input)))

noncomputable def auxiliary (key : SecretKey) (inputs : Finset HashInput) (labels : CanonicalGraphLabels)
    (outside : NonstructuralRows key.parameter inputs) : QueryImpl OracleWorld SPMF :=
  fun input => 𝒟[fixedHashWorld (structuralAnswer key inputs labels outside (fun _ => 0)) input]

theorem fixed_translate (key : SecretKey) (inputs : Finset HashInput) (labels : CanonicalGraphLabels)
    (outside : NonstructuralRows key.parameter inputs) (rows : structuralInputs key.parameter inputs → HashOutput)
    (input : OracleWorld.Domain) :
    simulateQ (UniformTableObservation.fixedImpl (auxiliary key inputs labels outside) rows) (translate key inputs labels input) =
      𝒟[fixedHashWorld (structuralAnswer key inputs labels outside rows) input] := by
  cases input with
  | inl input =>
      simp only [translate, simulateQ_spec_query, UniformTableObservation.fixedImpl, auxiliary, fixedHashWorld]
  | inr input =>
      by_cases ha : Active key inputs labels input
      · simp only [translate, dif_pos ha, simulateQ_spec_query, UniformTableObservation.fixedImpl,
          fixedHashWorld, evalDist_pure, answer_active key inputs labels outside rows input ha]
      · simp only [translate, dif_neg ha, simulateQ_spec_query, UniformTableObservation.fixedImpl, auxiliary,
          fixedHashWorld, evalDist_pure, answer_inactive key inputs labels outside rows (fun _ => 0) input ha]

theorem fixed_run {Result : Type} (key : SecretKey) (inputs : Finset HashInput) (labels : CanonicalGraphLabels)
    (outside : NonstructuralRows key.parameter inputs) (rows : structuralInputs key.parameter inputs → HashOutput)
    (computation : OracleComp OracleWorld Result) :
    simulateQ (UniformTableObservation.fixedImpl (auxiliary key inputs labels outside) rows)
        (simulateQ (translate key inputs labels) computation) =
      𝒟[simulateQ (fixedHashWorld (structuralAnswer key inputs labels outside rows)) computation] := by
  induction computation using OracleComp.inductionOn with
  | pure result => simp only [simulateQ_pure, evalDist_pure]
  | query_bind input next ih =>
      simp only [simulateQ_bind, simulateQ_spec_query, evalDist_bind, ih, fixed_translate]

noncomputable def lazyRun {Result : Type} (key : SecretKey) (inputs : Finset HashInput) (labels : CanonicalGraphLabels)
    (outside : NonstructuralRows key.parameter inputs) (computation : OracleComp OracleWorld Result)
    (allowed : structuralInputs key.parameter inputs → Finset HashOutput) :
    SPMF (Result × (structuralInputs key.parameter inputs → Finset HashOutput)) :=
  UniformTableObservation.lazyRun (auxiliary key inputs labels outside) (simulateQ (translate key inputs labels) computation) allowed

theorem lazyRun_original {Result : Type} (key : SecretKey) (inputs : Finset HashInput) (labels : CanonicalGraphLabels)
    (outside : NonstructuralRows key.parameter inputs) (computation : OracleComp OracleWorld Result)
    (allowed : structuralInputs key.parameter inputs → Finset HashOutput) (ha : ∀ cell, (allowed cell).Nonempty) :
    (complete allowed >>= fun rows => 𝒟[simulateQ (fixedHashWorld (structuralAnswer key inputs labels outside rows)) computation]) =
      Prod.fst <$> lazyRun key inputs labels outside computation allowed := by
  have h := UniformTableObservation.run_marginal (auxiliary key inputs labels outside)
    (simulateQ (translate key inputs labels) computation) allowed ha
  simpa only [fixed_run, lazyRun] using h

theorem uniform_rows_complete (parameter : PublicParameter) (inputs : Finset HashInput) :
    𝒟[PMF.uniformOfFintype (structuralInputs parameter inputs → HashOutput)] =
      complete (fun _ : structuralInputs parameter inputs => (Finset.univ : Finset HashOutput)) := by
  rw [complete, dif_pos (fun _ => Finset.univ_nonempty), uniformTable_univ]

theorem referenceGraphContextRest_lazy {Result : Type} (observer : FrontierObserver Result)
    (key : SecretKey) (inputs : Finset HashInput) (hencoding : canonicalEncodingInputs key.parameter ⊆ inputs)
    (hgraph : canonicalGraphInputs key.parameter ⊆ inputs) (dummy : OtsReferenceWords) (adversary : Adversary) :
    referenceGraphContextRest observer key inputs hencoding dummy adversary = (do
      let labels ← 𝒟[PMF.uniformOfFintype CanonicalGraphLabels]
      let outside ← 𝒟[PMF.uniformOfFintype (NonstructuralRows key.parameter inputs)]
      let selections := referenceTableSelection key (structuralAnswer key inputs labels outside (fun _ => 0))
      let words := referenceFamilyWords selections dummy
      let result ← Prod.fst <$> lazyRun key inputs labels outside
        (observer key.parameter words (canonicalGraphFrontier key.otsSecret labels words)
          (structuralProgram key inputs labels outside words adversary)) (fun _ => Finset.univ)
      pure (labels, selections, result)) := by
  rw [referenceGraphContextRest_conditioned observer key inputs hencoding hgraph dummy adversary]
  apply congrArg (𝒟[PMF.uniformOfFintype CanonicalGraphLabels] >>= ·)
  funext labels
  apply congrArg (𝒟[PMF.uniformOfFintype (NonstructuralRows key.parameter inputs)] >>= ·)
  funext outside
  rw [uniform_rows_complete, ← bind_assoc, lazyRun_original _ _ _ _ _ _ (fun _ => Finset.univ_nonempty)]

end SphincsSecurity.Concrete.StructuralObservation
