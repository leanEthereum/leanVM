import SphincsSecurity.Proof.Forced.FtsGuessNearSource
namespace SphincsSecurity.Concrete.FtsGuessHash

open _root_.OracleComp OracleSpec CanonicalProbeRouting
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] canonicalEncodingInputs canonicalGraphInputs instFintypePosition
  publicDigestLoop canonicalGraphRoot canonicalGraphInput

abbrev SeedSpec (inputs : Finset HashInput) := unifSpec + (inputs →ₒ HashOutput)

noncomputable def seedAnswers (inputs : Finset HashInput) (seed : inputs → HashOutput) : QueryImpl (SeedSpec inputs) ProbComp
  | .inl input => liftM (unifSpec.query input)
  | .inr input => pure (seed input)

noncomputable def residualProgram {Row : Type} (inputs : Finset HashInput) (embed : Row → inputs)
    (rows : Row → HashOutput) (input : HashInput) : OracleComp (SeedSpec inputs) HashOutput :=
  if hi : input ∈ inputs then
    if hr : (⟨input, hi⟩ : inputs) ∈ Set.range embed then pure (rows (Classical.choose hr))
    else liftM ((SeedSpec inputs).query (.inr ⟨input, hi⟩))
  else pure 0

theorem residualProgram_fixed {Row : Type} (inputs : Finset HashInput) (embed : Row → inputs)
    (hinj : Function.Injective embed) (rows : Row → HashOutput) (seed : inputs → HashOutput) (input : HashInput) :
    simulateQ (seedAnswers inputs seed) (residualProgram inputs embed rows input) =
      pure (finiteHashAnswer ∅ inputs (UniformTableSplit.overwrite embed hinj rows seed) input) := by
  by_cases hi : input ∈ inputs
  · rw [residualProgram, dif_pos hi, finiteHashAnswer_none _ _ _ _ hi (by simp)]
    by_cases hr : (⟨input, hi⟩ : inputs) ∈ Set.range embed
    · rw [dif_pos hr, simulateQ_pure]
      have he := Classical.choose_spec hr
      exact congrArg pure ((congrArg (UniformTableSplit.overwrite embed hinj rows seed) he).symm.trans
        (UniformTableSplit.overwrite_embed embed hinj rows seed (Classical.choose hr))).symm
    · rw [dif_neg hr, simulateQ_spec_query, UniformTableSplit.overwrite_outside _ _ _ _ _ hr]
      rfl
  · simp only [residualProgram, dif_neg hi, simulateQ_pure, finiteHashAnswer, QueryCache.empty_apply, Option.getD_none]

noncomputable def publicRecordProgram {TargetIndex : Type} {targetSpec : OracleSpec TargetIndex}
    (parameter : PublicParameter) (root : Digest) (outside : QueryImpl OracleWorld (OracleComp targetSpec))
    (known : Labels) (words : OtsReferenceWords) (selections : ReferenceFamily) (message : Message) :
    OracleComp targetSpec PublicSigningRecord := do
  let selected ← simulateQ outside
    (QueryPause.traced (signingBoundaryTrace parameter) (publicDigestLoop parameter root message digestAttemptLimit))
  match selected.1 with
  | none => pure ((none, none), selected.2)
  | some (randomness, index, leaves) =>
      let plan := publicSignPlan known words selections randomness index leaves
      pure ((plan.1, some (selectedFewTimeView index leaves)), selected.2 * (FreeMonoid.of none) ^ plan.2)

theorem fixed_traced {Result : Type} (parameter : PublicParameter) (f : QueryImpl HashSpec Id)
    (computation : OracleComp OracleWorld Result) :
    simulateQ (fixedHashWorld f) (QueryPause.traced (signingBoundaryTrace parameter) computation) =
      fixedBoundaryRun parameter f computation := by
  induction computation using OracleComp.inductionOn with
  | pure value => simp only [QueryPause.traced_pure, simulateQ_pure, fixedBoundaryRun_pure]
  | query_bind input next ih =>
      simp only [QueryPause.traced_query_bind, simulateQ_bind, simulateQ_spec_query, simulateQ_map,
        ih, ResidualByteFrontend.fixedBoundaryRun_query_bind]

theorem publicRecordProgram_fixed {TargetIndex : Type} {targetSpec : OracleSpec TargetIndex}
    (parameter : PublicParameter) (root : Digest) (outside : QueryImpl OracleWorld (OracleComp targetSpec))
    (known : Labels) (words : OtsReferenceWords) (selections : ReferenceFamily) (message : Message)
    (runtime : QueryImpl targetSpec ProbComp) (f : QueryImpl HashSpec Id)
    (houtside : ∀ input, simulateQ runtime (outside input) = fixedHashWorld f input) :
    simulateQ runtime (publicRecordProgram parameter root outside known words selections message) =
      publicSigningRecord parameter root f known words selections message := by
  have hcompose : runtime.compose outside = fixedHashWorld f := funext houtside
  rw [publicRecordProgram, simulateQ_bind, ← QueryImpl.simulateQ_compose, hcompose, fixed_traced, publicSigningRecord]
  apply congrArg (fixedBoundaryRun parameter f (publicDigestLoop parameter root message digestAttemptLimit) >>= ·)
  funext selected
  cases selected.1 <;> rfl

noncomputable def residualWorld (parameter : PublicParameter) (inputs : Finset HashInput)
    (hencoding : canonicalEncodingInputs parameter ⊆ inputs) (known : Labels) (rows : CanonicalEncodingRows) :
    QueryImpl OracleWorld (OracleComp (SeedSpec inputs))
  | .inl input => liftM ((SeedSpec inputs).query (.inl input))
  | .inr input => residualProgram inputs (knownEncodingCell parameter inputs hencoding known) rows input

theorem residualWorld_fixed (parameter : PublicParameter) (inputs : Finset HashInput)
    (hencoding : canonicalEncodingInputs parameter ⊆ inputs) (known : Labels) (rows : CanonicalEncodingRows)
    (seed : inputs → HashOutput) (input : OracleWorld.Domain) :
    simulateQ (seedAnswers inputs seed) (residualWorld parameter inputs hencoding known rows input) =
      fixedHashWorld (finiteHashAnswer ∅ inputs (knownReferenceResidual parameter inputs hencoding known rows seed)) input := by
  cases input with
  | inl input => rfl
  | inr input => exact residualProgram_fixed inputs _ (knownEncodingCell_injective parameter inputs hencoding known) rows seed input

noncomputable def auxiliaryHashProgram (parameter : PublicParameter)
    (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest) (labels : CanonicalGraphLabels)
    (inputs : Finset HashInput) (hencoding : canonicalEncodingInputs parameter ⊆ inputs)
    (rows : CanonicalEncodingRows) (input : HashInput) : OracleComp (SeedSpec inputs) HashOutput :=
  let residual := residualProgram inputs (canonicalEncodingCell parameter inputs hencoding labels) rows input
  match FtsProbeSimulation.decodeProbe? parameter input with
  | some _ => residual
  | none => match decodePosition parameter input with
    | none => residual
    | some position =>
        if input = canonicalGraphInput parameter otsSecret (fun _ _ _ => 0) position labels then pure (labels position)
        else residual

theorem auxiliaryHashProgram_fixed (parameter : PublicParameter)
    (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest) (labels : CanonicalGraphLabels)
    (inputs : Finset HashInput) (hencoding : canonicalEncodingInputs parameter ⊆ inputs)
    (rows : CanonicalEncodingRows) (seed : inputs → HashOutput) (input : HashInput) :
    simulateQ (seedAnswers inputs seed) (auxiliaryHashProgram parameter otsSecret labels inputs hencoding rows input) =
      pure (auxiliaryHash parameter otsSecret labels
        (finiteHashAnswer ∅ inputs (canonicalReferenceResidual parameter inputs hencoding labels rows seed)) input) := by
  have hr := residualProgram_fixed inputs (canonicalEncodingCell parameter inputs hencoding labels)
    (canonicalEncodingCell_injective parameter inputs hencoding labels) rows seed input
  simp only [canonicalReferenceResidual]
  cases hp : FtsProbeSimulation.decodeProbe? parameter input with
  | some probe => simpa only [auxiliaryHashProgram, auxiliaryHash, hp] using hr
  | none =>
      simp only [auxiliaryHashProgram, auxiliaryHash, hp, programmedHash]
      cases hd : decodePosition parameter input with
      | none => simpa only [Option.elim_none] using hr
      | some position =>
          simp only [Option.elim_some]
          split <;> simp only [simulateQ_pure, hr]

noncomputable def referenceProgram (parameter : PublicParameter) (root : Digest)
    (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest) (labels : CanonicalGraphLabels)
    (inputs : Finset HashInput) (hencoding : canonicalEncodingInputs parameter ⊆ inputs)
    (selections : ReferenceFamily) (rows : CanonicalEncodingRows) (dummy : OtsReferenceWords) :
    QueryImpl Auxiliary (OracleComp (SeedSpec inputs))
  | .inl (.inl input) => liftM ((SeedSpec inputs).query (.inl input))
  | .inl (.inr input) => auxiliaryHashProgram parameter otsSecret labels inputs hencoding rows input
  | .inr message => publicRecordProgram parameter root
      (residualWorld parameter inputs hencoding (known otsSecret labels) rows)
      (known otsSecret labels) (referenceFamilyWords selections dummy) selections message

theorem referenceProgram_fixed (parameter : PublicParameter) (root : Digest)
    (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest) (labels : CanonicalGraphLabels)
    (inputs : Finset HashInput) (hencoding : canonicalEncodingInputs parameter ⊆ inputs)
    (selections : ReferenceFamily) (rows : CanonicalEncodingRows) (seed : inputs → HashOutput)
    (dummy : OtsReferenceWords) (input : Auxiliary.Domain) :
    simulateQ (seedAnswers inputs seed)
      (referenceProgram parameter root otsSecret labels inputs hencoding selections rows dummy input) =
        referenceAnswers parameter root otsSecret labels inputs hencoding ⟨selections, rows, seed⟩ dummy input := by
  cases input with
  | inl input =>
      cases input with
      | inl input => rfl
      | inr input => exact auxiliaryHashProgram_fixed parameter otsSecret labels inputs hencoding rows seed input
  | inr message =>
      exact publicRecordProgram_fixed parameter root _ _ _ selections message (seedAnswers inputs seed) _
        (residualWorld_fixed parameter inputs hencoding (known otsSecret labels) rows seed)

end SphincsSecurity.Concrete.FtsGuessHash
