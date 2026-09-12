import SphincsSecurity.Proof.Ots.EncodingTablePrior
import SphincsSecurity.Proof.Ots.ReferenceEncodingErasure
import SphincsSecurity.Proof.Base.UniformTableObservationErasure
namespace SphincsSecurity.Concrete.EncodingObservation

open _root_.OracleComp OracleSpec UniformTableCompletion
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
attribute [local irreducible] canonicalEncodingInputs Finset.univ

abbrev World (parameter : PublicParameter) :=
  OracleWorld + UniformTableObservation.TableSpec (canonicalEncodingInputs parameter) HashOutput

noncomputable def translate (parameter : PublicParameter) : QueryImpl OracleWorld (OracleComp (World parameter))
  | .inl input => liftM ((World parameter).query (.inl (.inl input)))
  | .inr input =>
      if h : input ∈ canonicalEncodingInputs parameter then liftM ((World parameter).query (.inr ⟨input, h⟩))
      else liftM ((World parameter).query (.inl (.inr input)))

noncomputable def auxiliary (parameter : PublicParameter) (inputs : Finset HashInput)
    (hencoding : canonicalEncodingInputs parameter ⊆ inputs) (outside : NonencodingRows parameter inputs hencoding) :
    QueryImpl OracleWorld SPMF := fun input => 𝒟[fixedHashWorld (nonencodingAnswer parameter inputs hencoding outside) input]

theorem fixed_translate (parameter : PublicParameter) (inputs : Finset HashInput)
    (hencoding : canonicalEncodingInputs parameter ⊆ inputs) (outside : NonencodingRows parameter inputs hencoding)
    (encoding : canonicalEncodingInputs parameter → HashOutput) (input : OracleWorld.Domain) :
    simulateQ (UniformTableObservation.fixedImpl (auxiliary parameter inputs hencoding outside) encoding) (translate parameter input) =
      𝒟[fixedHashWorld (finiteHashAnswer ∅ inputs (joinEncodingTable parameter inputs hencoding encoding outside)) input] := by
  cases input with
  | inl input =>
      simp only [translate, simulateQ_spec_query, UniformTableObservation.fixedImpl, auxiliary, fixedHashWorld]
  | inr input =>
      by_cases hc : input ∈ canonicalEncodingInputs parameter
      · have hrow : finiteHashAnswer ∅ inputs (joinEncodingTable parameter inputs hencoding encoding outside) input = encoding ⟨input, hc⟩ := by
          rw [finiteHashAnswer_none ∅ inputs _ _ (hencoding hc) (by simp)]
          exact UniformTableSplit.join_embed (encodingInputCell parameter inputs hencoding)
            (encodingInputCell_injective parameter inputs hencoding) encoding outside ⟨input, hc⟩
        simp only [translate, dif_pos hc, simulateQ_spec_query, UniformTableObservation.fixedImpl, fixedHashWorld,
          evalDist_pure, hrow]
      · have hrow := joinEncodingTable_agrees_outside parameter inputs hencoding encoding (fun _ => 0) outside input hc
        simp only [translate, dif_neg hc, simulateQ_spec_query, UniformTableObservation.fixedImpl, auxiliary, fixedHashWorld,
          evalDist_pure, hrow, nonencodingAnswer]

theorem fixed_run {Result : Type} (parameter : PublicParameter) (inputs : Finset HashInput)
    (hencoding : canonicalEncodingInputs parameter ⊆ inputs) (outside : NonencodingRows parameter inputs hencoding)
    (encoding : canonicalEncodingInputs parameter → HashOutput) (computation : OracleComp OracleWorld Result) :
    simulateQ (UniformTableObservation.fixedImpl (auxiliary parameter inputs hencoding outside) encoding)
        (simulateQ (translate parameter) computation) =
      𝒟[simulateQ (fixedHashWorld (finiteHashAnswer ∅ inputs (joinEncodingTable parameter inputs hencoding encoding outside))) computation] := by
  induction computation using OracleComp.inductionOn with
  | pure result => simp only [simulateQ_pure, evalDist_pure]
  | query_bind input next ih =>
      simp only [simulateQ_bind, simulateQ_spec_query, evalDist_bind, ih, fixed_translate]

noncomputable def lazyRun {Result : Type} (parameter : PublicParameter) (inputs : Finset HashInput)
    (hencoding : canonicalEncodingInputs parameter ⊆ inputs) (outside : NonencodingRows parameter inputs hencoding)
    (computation : OracleComp OracleWorld Result) (allowed : canonicalEncodingInputs parameter → Finset HashOutput) :
    SPMF (Result × (canonicalEncodingInputs parameter → Finset HashOutput)) :=
  UniformTableObservation.lazyRun (auxiliary parameter inputs hencoding outside) (simulateQ (translate parameter) computation) allowed

theorem lazyRun_original {Result : Type} (parameter : PublicParameter) (inputs : Finset HashInput)
    (hencoding : canonicalEncodingInputs parameter ⊆ inputs) (outside : NonencodingRows parameter inputs hencoding)
    (computation : OracleComp OracleWorld Result) (allowed : canonicalEncodingInputs parameter → Finset HashOutput)
    (ha : ∀ cell, (allowed cell).Nonempty) :
    (complete allowed >>= fun encoding =>
      𝒟[simulateQ (fixedHashWorld (finiteHashAnswer ∅ inputs (joinEncodingTable parameter inputs hencoding encoding outside))) computation]) =
        Prod.fst <$> lazyRun parameter inputs hencoding outside computation allowed := by
  have h := UniformTableObservation.run_marginal (auxiliary parameter inputs hencoding outside)
    (simulateQ (translate parameter) computation) allowed ha
  simpa only [fixed_run, lazyRun] using h

end SphincsSecurity.Concrete.EncodingObservation
