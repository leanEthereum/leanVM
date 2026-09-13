import SphincsSecurity.Proof.Reference.ReferenceForgeryCoverage
import SphincsSecurity.Proof.Reference.ReferencePrimitiveBound
namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec OtsContactTrace
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
attribute [local irreducible] frontierRoot maskOtsPrefixes boundaryEval canonicalGraphInputs canonicalEncodingInputs
  canonicalGraphGameInputs canonicalGraphLabels Finset.univ instFintypePosition chainWalk sequenceFin honestNode

/-- Retains the whole trace with the split immediately before verification. -/
noncomputable def completedReferenceContact (parameter : PublicParameter) (f : QueryImpl HashSpec Id)
    (words : OtsReferenceWords) (frontier : OtsFrontierValues) (before : AdversaryTrace) : ContactResult :=
  let root := frontierRoot parameter (maskOtsPrefixes parameter words f) words frontier
  let checked := boundaryEval parameter f (verify ⟨root, parameter⟩ before.1.1.1.message before.1.1.1.signature)
  { frontier := frontier
    before := before.2
    output := (decide (SigningTranscript.Valid before.1.1.2 ∧ ¬SigningTranscript.Contains before.1.1.2 before.1.1.1) && checked.1,
      (FreeMonoid.of none) ^ 1212415 * (before.1.2 * checked.2))
    after := answerTrace f (verify ⟨root, parameter⟩ before.1.1.1.message before.1.1.1.signature) }

noncomputable def referenceForgeryRest (key : SecretKey) (f : QueryImpl HashSpec Id) (labels : CanonicalGraphLabels)
    (selections : ReferenceFamily) (dummy : OtsReferenceWords) (adversary : Adversary) : ProbComp AdversaryTrace :=
  let words := referenceFamilyWords selections dummy
  let frontier := canonicalGraphFrontier key.otsSecret labels words
  let root := frontierRoot key.parameter (maskOtsPrefixes key.parameter words f) words frontier
  fixedTrace f (CausalFrontierProgram.adversaryRun key.parameter root f key.ftsSecret words frontier
    (adversary.main ⟨root, key.parameter⟩))

theorem referenceForgeryRest_trace (key : SecretKey) (f : QueryImpl HashSpec Id) (labels : CanonicalGraphLabels)
    (selections : ReferenceFamily) (dummy : OtsReferenceWords) (adversary : Adversary) :
    (fun before =>
      let result := completedReferenceContact key.parameter f (referenceFamilyWords selections dummy)
        (canonicalGraphFrontier key.otsSecret labels (referenceFamilyWords selections dummy)) before
      (result.output, result.before * result.after)) <$> referenceForgeryRest key f labels selections dummy adversary =
      fixedTrace f (CausalFrontierProgram.game key.parameter f key.ftsSecret (referenceFamilyWords selections dummy)
        (canonicalGraphFrontier key.otsSecret labels (referenceFamilyWords selections dummy)) adversary) := by
  rw [CausalFrontierProgram.game, fixedTrace_map, CausalFrontierProgram.gameRest, fixedTrace_bind]
  simp only [fixedTrace_map, fixedTrace_boundary_hash, map_pure,
    bind_pure_comp, Functor.map_map, completedReferenceContact, referenceForgeryRest]

def ContactResult.traceView (result : ContactResult) : OtsFrontierValues × (Bool × SigningBoundaryTrace) × Trace :=
  (result.frontier, result.output, result.before * result.after)

theorem referenceForgeryRest_contact_trace (key : SecretKey) (f : QueryImpl HashSpec Id) (labels : CanonicalGraphLabels)
    (selections : ReferenceFamily) (dummy : OtsReferenceWords) (adversary : Adversary) :
    (fun before => (completedReferenceContact key.parameter f (referenceFamilyWords selections dummy)
      (canonicalGraphFrontier key.otsSecret labels (referenceFamilyWords selections dummy)) before).traceView) <$>
        referenceForgeryRest key f labels selections dummy adversary =
      ContactResult.traceView <$> referenceInstrumentedRest contactObserver key f labels selections dummy adversary := by
  have h := congrArg (Functor.map (fun result =>
    (canonicalGraphFrontier key.otsSecret labels (referenceFamilyWords selections dummy), result)))
    (referenceForgeryRest_trace key f labels selections dummy adversary)
  simp only [Functor.map_map] at h
  have hc (computation : OracleComp OracleWorld (Bool × SigningBoundaryTrace)) :
      ContactResult.traceView <$> contactObserver key.parameter (referenceFamilyWords selections dummy)
        (canonicalGraphFrontier key.otsSecret labels (referenceFamilyWords selections dummy)) computation =
      (fun result => (canonicalGraphFrontier key.otsSecret labels (referenceFamilyWords selections dummy), result)) <$>
        QueryPause.traced hashObservationTrace computation := contactObserver_frontier_trace _ _ _ computation
  rw [referenceInstrumentedRest, ← simulateQ_map, hc, simulateQ_map]
  exact h

abbrev ReferenceForgerySample (inputs : Finset HashInput) := SecretKey × (ReferenceFamily × (inputs → HashOutput)) × AdversaryTrace

noncomputable def referenceForgeryGame (inputs : Finset HashInput)
    (hencoding : ∀ parameter, canonicalEncodingInputs parameter ⊆ inputs)
    (dummy : OtsReferenceWords) (adversary : Adversary) : SPMF (ReferenceForgerySample inputs) := do
  let parameter ← 𝒟[sampleParameter]
  let otsSecret ← 𝒟[sampleOtsSecrets]
  let ftsSecret ← 𝒟[sampleFtsSecrets]
  let key : SecretKey := ⟨parameter, 0, otsSecret, ftsSecret⟩
  let reference ← 𝒟[referenceFamilyOracleSample key inputs (hencoding parameter)]
  let f := finiteHashAnswer ∅ inputs reference.2
  let before ← 𝒟[referenceForgeryRest key f (canonicalGraphLabels parameter otsSecret ftsSecret f) reference.1 dummy adversary]
  pure (key, reference, before)

noncomputable def ReferenceForgerySample.context {inputs : Finset HashInput} (dummy : OtsReferenceWords)
    (sample : ReferenceForgerySample inputs) : GraphContextResult ContactResult :=
  let f := finiteHashAnswer ∅ inputs sample.2.1.2
  let labels := canonicalGraphLabels sample.1.parameter sample.1.otsSecret sample.1.ftsSecret f
  let words := referenceFamilyWords sample.2.1.1 dummy
  (sample.1, labels, sample.2.1.1,
    completedReferenceContact sample.1.parameter f words (canonicalGraphFrontier sample.1.otsSecret labels words) sample.2.2)

abbrev GraphContextTraceResult := SecretKey × CanonicalGraphLabels × ReferenceFamily × OtsFrontierValues × (Bool × SigningBoundaryTrace) × Trace

def graphContextTrace (result : GraphContextResult ContactResult) : GraphContextTraceResult :=
  (result.1, result.2.1, result.2.2.1, result.2.2.2.traceView)

theorem referenceForgeryGame_graph_trace (inputs : Finset HashInput)
    (hencoding : ∀ parameter, canonicalEncodingInputs parameter ⊆ inputs)
    (dummy : OtsReferenceWords) (adversary : Adversary) :
    (fun sample => graphContextTrace (sample.context dummy)) <$> referenceForgeryGame inputs hencoding dummy adversary =
      graphContextTrace <$> referenceGraphContextGame contactObserver inputs hencoding dummy adversary := by
  simp only [referenceForgeryGame, referenceGraphContextGame, referenceGraphContextRest, map_bind, map_pure,
    bind_assoc, pure_bind, ReferenceForgerySample.context, graphContextTrace]
  apply congrArg (𝒟[sampleParameter] >>= ·)
  funext parameter
  apply congrArg (𝒟[sampleOtsSecrets] >>= ·)
  funext otsSecret
  apply congrArg (𝒟[sampleFtsSecrets] >>= ·)
  funext ftsSecret
  apply congrArg (𝒟[referenceFamilyOracleSample _ inputs (hencoding parameter)] >>= ·)
  funext reference
  have h := congrArg (Functor.map (fun result =>
    ((⟨parameter, 0, otsSecret, ftsSecret⟩ : SecretKey),
      canonicalGraphLabels parameter otsSecret ftsSecret (finiteHashAnswer ∅ inputs reference.2), reference.1, result)))
    (referenceForgeryRest_contact_trace ⟨parameter, 0, otsSecret, ftsSecret⟩ (finiteHashAnswer ∅ inputs reference.2)
      (canonicalGraphLabels parameter otsSecret ftsSecret (finiteHashAnswer ∅ inputs reference.2)) reference.1 dummy adversary)
  have hd := congrArg (fun law : ProbComp GraphContextTraceResult => 𝒟[law]) h
  simpa only [Functor.map_map, evalDist_map, bind_pure_comp] using hd

noncomputable def GraphContextTraceResult.primitive (dummy : OtsReferenceWords) (result : GraphContextTraceResult) : Prop :=
  GraphPrimitiveEvent dummy (result.1, result.2.1, result.2.2.1,
    ⟨result.2.2.2.1, result.2.2.2.2.2, result.2.2.2.2.1, 1⟩)

theorem graphContextTrace_primitive (dummy : OtsReferenceWords) (result : GraphContextResult ContactResult) :
    (graphContextTrace result).primitive dummy = GraphPrimitiveEvent dummy result := by
  simp only [GraphContextTraceResult.primitive, graphContextTrace, ContactResult.traceView,
    GraphPrimitiveEvent, ContactResult.TwoEdge, ContactResult.TwoEdgeAt, ContactResult.TwoContacts,
    ContactResult.MarkerContact, mul_one]

theorem referenceForgeryGame_primitive (inputs : Finset HashInput)
    (hencoding : ∀ parameter, canonicalEncodingInputs parameter ⊆ inputs)
    (dummy : OtsReferenceWords) (adversary : Adversary) :
    Pr[fun sample => GraphPrimitiveEvent dummy (sample.context dummy) | referenceForgeryGame inputs hencoding dummy adversary] =
      Pr[GraphPrimitiveEvent dummy | referenceGraphContextGame contactObserver inputs hencoding dummy adversary] := by
  have h := congrArg (fun law => Pr[GraphContextTraceResult.primitive dummy | law])
    (referenceForgeryGame_graph_trace inputs hencoding dummy adversary)
  simpa only [probEvent_map, Function.comp_def, graphContextTrace_primitive] using h

theorem referenceForgeryGame_verdict (inputs : Finset HashInput)
    (hencoding : ∀ parameter, canonicalEncodingInputs parameter ⊆ inputs)
    (dummy : OtsReferenceWords) (adversary : Adversary) :
    Pr[fun sample => (sample.context dummy).2.2.2.output.1 = true | referenceForgeryGame inputs hencoding dummy adversary] =
      Pr[fun result => result.2.2.2.output.1 = true | referenceGraphContextGame contactObserver inputs hencoding dummy adversary] := by
  have h := congrArg (fun law => Pr[fun result : GraphContextTraceResult => result.2.2.2.2.1.1 = true | law])
    (referenceForgeryGame_graph_trace inputs hencoding dummy adversary)
  simpa only [probEvent_map, Function.comp_def, graphContextTrace, ContactResult.traceView] using h

theorem forgeAdvantage_eq_referenceForgery (dummy : OtsReferenceWords) (adversary : Adversary) :
    forgeAdvantage scheme adversary = Pr[fun sample => (sample.context dummy).2.2.2.output.1 = true |
      referenceForgeryGame (canonicalGraphGameInputs adversary) (canonicalEncodingInputs_subset_gameInputs adversary) dummy adversary] := by
  rw [referenceForgeryGame_verdict, forgeAdvantage_eq_referenceContact dummy adversary,
    referenceGraphContextGame_contact_event _ _ dummy adversary (fun result => result.2.2.output.1 = true)]

theorem referenceForgeryGame_support (inputs : Finset HashInput)
    (hencoding : ∀ parameter, canonicalEncodingInputs parameter ⊆ inputs)
    (dummy : OtsReferenceWords) (adversary : Adversary) (sample : ReferenceForgerySample inputs)
    (hsample : sample ∈ support (referenceForgeryGame inputs hencoding dummy adversary)) :
    sample.2.1 ∈ (referenceFamilyOracleSample sample.1 inputs (hencoding sample.1.parameter)).support ∧
      sample.2.2 ∈ support (referenceForgeryRest sample.1 (finiteHashAnswer ∅ inputs sample.2.1.2)
        (canonicalGraphLabels sample.1.parameter sample.1.otsSecret sample.1.ftsSecret (finiteHashAnswer ∅ inputs sample.2.1.2))
        sample.2.1.1 dummy adversary) := by
  simp only [referenceForgeryGame, mem_support_bind_iff] at hsample
  obtain ⟨parameter, _, otsSecret, _, ftsSecret, _, reference, href, before, hb, heq⟩ := hsample
  rw [mem_support_pure_iff] at heq
  subst sample
  constructor
  · simpa only [PMF.evalDist_eq, SPMF.support_eq_support, SPMF.support_liftM] using href
  · exact (mem_support_iff_of_evalDist_eq (mx := referenceForgeryRest _ _ _ _ dummy adversary)
      (mx' := 𝒟[referenceForgeryRest _ _ _ _ dummy adversary]) rfl before).mpr hb

theorem referenceForgeryRest_success (key : SecretKey) (f : QueryImpl HashSpec Id)
    (selections : ReferenceFamily) (dummy : OtsReferenceWords) (adversary : Adversary) (before : AdversaryTrace)
    (hselected : selections = referenceTableSelection key f)
    (hvalid : ∀ lay tree leaf, TargetSum.Valid (referenceFamilyWords selections dummy lay tree leaf))
    (hb : before ∈ support (referenceForgeryRest key f (canonicalGraphLabels key.parameter key.otsSecret key.ftsSecret f)
      selections dummy adversary))
    (hsuccess : (completedReferenceContact key.parameter f (referenceFamilyWords selections dummy)
      (canonicalGraphFrontier key.otsSecret (canonicalGraphLabels key.parameter key.otsSecret key.ftsSecret f)
        (referenceFamilyWords selections dummy)) before).output.1 = true) :
    ReferenceVerifierWitness.ForgeryWitnessFor key f (ReferenceVerifierWitness.rootedKey key f).root
      (referenceFamilyWords selections dummy) selections adversary
      (completedReferenceContact key.parameter f (referenceFamilyWords selections dummy)
        (canonicalGraphFrontier key.otsSecret (canonicalGraphLabels key.parameter key.otsSecret key.ftsSecret f)
          (referenceFamilyWords selections dummy)) before) before := by
  dsimp only [referenceForgeryRest] at hb
  rw [ReferenceVerifierWitness.source_root] at hb
  simp only [completedReferenceContact, ReferenceVerifierWitness.source_root, boundaryEval_fst,
    Bool.and_eq_true, decide_eq_true_eq] at hsuccess
  apply ReferenceVerifierWitness.SuccessWitnessFor.classification
  apply ReferenceVerifierWitness.run_success_atRoot key f _ rfl selections dummy adversary _ before
    hselected hvalid hb hsuccess.1.1 hsuccess.1.2 hsuccess.2 rfl
  dsimp only [completedReferenceContact]
  rw [ReferenceVerifierWitness.source_root]

noncomputable def ReferenceForgerySample.ftsOutcome {inputs : Finset HashInput} (dummy : OtsReferenceWords)
    (sample : ReferenceForgerySample inputs) : Prop :=
  let f := finiteHashAnswer ∅ inputs sample.2.1.2
  let result := (sample.context dummy).2.2.2
  SigningTranscript.Valid sample.2.2.1.1.2 ∧
    ReferenceFtsCoverage.Outcome (ReferenceVerifierWitness.rootedKey sample.1 f) f sample.2.2.1.1.2 sample.2.2.1.2
      (result.before * result.after) sample.2.2.1.1.1

theorem graphPrimitiveEvent_of_outcome_atRoot (key : SecretKey) (root : Digest) (f : QueryImpl HashSpec Id)
    (selections : ReferenceFamily) (dummy : OtsReferenceWords) (result : ContactResult)
    (h : ReferencePrimitiveWitness.Outcome { key with root := root } f (referenceFamilyWords selections dummy)
      (canonicalGraphMessage (canonicalGraphLabels key.parameter key.otsSecret key.ftsSecret f)) selections result) :
    GraphPrimitiveEvent dummy (key, canonicalGraphLabels key.parameter key.otsSecret key.ftsSecret f, selections, result) := by
  have hp := graphPrimitiveEvent_of_outcome { key with root := root } f selections dummy result h
  simpa only [GraphPrimitiveEvent, ReferenceStructuralMatch.Seen, ReferenceStructuralMatch.Entry] using hp

theorem referenceForgeryGame_success (inputs : Finset HashInput)
    (hencoding : ∀ parameter, canonicalEncodingInputs parameter ⊆ inputs)
    (hgraph : ∀ parameter, canonicalGraphInputs parameter ⊆ inputs)
    (dummy : OtsReferenceWords) (hdummy : ∀ lay tree leaf, TargetSum.Valid (dummy lay tree leaf))
    (adversary : Adversary) (sample : ReferenceForgerySample inputs)
    (hsample : sample ∈ support (referenceForgeryGame inputs hencoding dummy adversary))
    (hsuccess : (sample.context dummy).2.2.2.output.1 = true) :
    sample.ftsOutcome dummy ∨ GraphPrimitiveEvent dummy (sample.context dummy) := by
  obtain ⟨href, hb⟩ := referenceForgeryGame_support inputs hencoding dummy adversary sample hsample
  have h := referenceForgeryRest_success sample.1 (finiteHashAnswer ∅ inputs sample.2.1.2) sample.2.1.1 dummy adversary sample.2.2
    (referenceFamilyOracleSample_selections sample.1 inputs (hencoding sample.1.parameter) (hgraph sample.1.parameter) sample.2.1 href)
    (referenceFamilyOracleSample_words_valid sample.1 inputs (hencoding sample.1.parameter) (hgraph sample.1.parameter) sample.2.1 href dummy hdummy)
    hb hsuccess
  dsimp only [ReferenceVerifierWitness.ForgeryWitnessFor] at h
  obtain ⟨_, hvalidLog, _, _, _, _, hcases⟩ := h
  rcases hcases with hfts | hprimitive
  · exact Or.inl ⟨hvalidLog, hfts⟩
  · apply Or.inr
    dsimp only [ReferenceForgerySample.context]
    exact graphPrimitiveEvent_of_outcome_atRoot sample.1
      (ReferenceVerifierWitness.rootedKey sample.1 (finiteHashAnswer ∅ inputs sample.2.1.2)).root
      (finiteHashAnswer ∅ inputs sample.2.1.2) sample.2.1.1 dummy _ hprimitive

theorem referenceForgeryGame_cases (inputs : Finset HashInput)
    (hencoding : ∀ parameter, canonicalEncodingInputs parameter ⊆ inputs)
    (hgraph : ∀ parameter, canonicalGraphInputs parameter ⊆ inputs)
    (dummy : OtsReferenceWords) (hdummy : ∀ lay tree leaf, TargetSum.Valid (dummy lay tree leaf)) (adversary : Adversary) :
    Pr[fun sample => (sample.context dummy).2.2.2.output.1 = true | referenceForgeryGame inputs hencoding dummy adversary] ≤
      Pr[ReferenceForgerySample.ftsOutcome dummy | referenceForgeryGame inputs hencoding dummy adversary] +
      Pr[GraphPrimitiveEvent dummy | referenceGraphContextGame contactObserver inputs hencoding dummy adversary] := by
  rw [← referenceForgeryGame_primitive inputs hencoding dummy adversary]
  refine (_root_.probEvent_mono (mx := referenceForgeryGame inputs hencoding dummy adversary)
    (p := fun sample => (sample.context dummy).2.2.2.output.1 = true)
    (q := fun sample => sample.ftsOutcome dummy ∨ GraphPrimitiveEvent dummy (sample.context dummy)) ?_).trans (probEvent_or_le _ _ _)
  intro sample hsample hsuccess
  exact referenceForgeryGame_success inputs hencoding hgraph dummy hdummy adversary sample hsample hsuccess

theorem forgeAdvantage_le_referenceForgery_cases (dummy : OtsReferenceWords)
    (hdummy : ∀ lay tree leaf, TargetSum.Valid (dummy lay tree leaf)) (adversary : Adversary) :
    forgeAdvantage scheme adversary ≤
      Pr[ReferenceForgerySample.ftsOutcome dummy | referenceForgeryGame (canonicalGraphGameInputs adversary)
        (canonicalEncodingInputs_subset_gameInputs adversary) dummy adversary] +
      Pr[GraphPrimitiveEvent dummy | referenceGraphContextGame contactObserver (canonicalGraphGameInputs adversary)
        (canonicalEncodingInputs_subset_gameInputs adversary) dummy adversary] := by
  rw [forgeAdvantage_eq_referenceForgery dummy adversary]
  exact referenceForgeryGame_cases (canonicalGraphGameInputs adversary) (canonicalEncodingInputs_subset_gameInputs adversary)
    (canonicalGraphInputs_subset_gameInputs adversary) dummy hdummy adversary

end SphincsSecurity.Concrete
