import SphincsSecurity.Proof.Fts.OriginalCertificateTrace
namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec OtsContactTrace OracleComp.DeferredSampling
open FtsProbeSimulation (RetainedRestResult retainedGameRestComputation)
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
attribute [local irreducible] scheme frontierRoot canonicalGraphLabels canonicalGraphInputs canonicalEncodingInputs
  canonicalGraphGameInputs hashInputs treeRoot honestNode

noncomputable def completeCertificateRest (key : SecretKey) (f : QueryImpl HashSpec Id)
    (before : (Forgery × QueryLog SigningSpec) × SigningBoundaryTrace) : RetainedRestResult × SigningBoundaryTrace :=
  let checked := boundaryEval key.parameter f (verify ⟨key.root, key.parameter⟩ before.1.1.message before.1.1.signature)
  ((before.1, checked.1), before.2 * checked.2)

theorem fixedBoundaryRun_retained_frontier (key : SecretKey) (f : QueryImpl HashSpec Id)
    (words : OtsReferenceWords) (frontier : OtsFrontierValues)
    (hfrontier : IsSigningFrontier key f words frontier)
    (hwords : ∀ index lay, FrontierReferenceWord key.parameter f key.ftsSecret words frontier index lay)
    (adversary : Adversary) :
    fixedBoundaryRun key.parameter f (simulateQ (expandedAdversaryImpl key)
      (retainedGameRestComputation adversary ⟨key.root, key.parameter⟩)) =
    completeCertificateRest key f <$> frontierAdversaryRun key.parameter key.root f key.ftsSecret words frontier
      (adversary.main ⟨key.root, key.parameter⟩) := by
  rw [retainedGameRestComputation, simulateQ_bind,
    ← FtsProbeSimulation.simulateQ_withTraceAppend_run_eq_signingTraceComputation,
    ← forwardOracles_add_signingOracle_eq_withTraceAppend, fixedBoundaryRun_bind,
    fixedBoundaryRun_adversary_frontier key f words frontier hfrontier hwords, map_eq_bind_pure_comp]
  apply bind_congr
  rintro ⟨⟨forgery, log⟩, trace⟩
  rw [simulateQ_bind, FtsProbeSimulation.simulateQ_expanded_liftOracleWorldLeft]
  simp only [simulateQ_pure, bind_pure_comp, fixedBoundaryRun_map, scheme]
  change (fun final => (final.1, trace * final.2)) <$>
    (Prod.map (fun checked => ((forgery, log), checked)) id) <$>
      fixedBoundaryRun key.parameter f (liftM (verify (m := OracleComp HashSpec) ⟨key.root, key.parameter⟩ forgery.message forgery.signature)) = _
  rw [fixedBoundaryRun_lift_hash, map_pure, map_pure]
  rfl

noncomputable def ReferenceForgerySample.certificateRecord {inputs : Finset HashInput}
    (sample : ReferenceForgerySample inputs) : CertificateTraceRecord :=
  let f := finiteHashAnswer ∅ inputs sample.2.1.2
  let key := ReferenceVerifierWitness.rootedKey sample.1 f
  let result := completeCertificateRest key f sample.2.2.1
  (key, result.1, result.2)

theorem referenceForgeryRest_certificateRecord_atRoot (key : SecretKey) (f : QueryImpl HashSpec Id) (root : Digest)
    (hroot : root = (ReferenceVerifierWitness.rootedKey key f).root)
    (dummy : OtsReferenceWords) (adversary : Adversary) :
    (fun before : AdversaryTrace =>
      let result := completeCertificateRest ({ key with root := root } : SecretKey) f before.1
      (({ key with root := root } : SecretKey), result.1, result.2)) <$>
      referenceForgeryRest key f (canonicalGraphLabels key.parameter key.otsSecret key.ftsSecret f)
        (referenceTableSelection key f) dummy adversary =
    (fun result : RetainedRestResult × SigningBoundaryTrace =>
      (({ key with root := root } : SecretKey), result.1, result.2)) <$>
      fixedBoundaryRun key.parameter f (simulateQ (expandedAdversaryImpl ({ key with root := root } : SecretKey))
        (retainedGameRestComputation adversary ⟨root, key.parameter⟩)) := by
  rw [referenceForgeryRest, ReferenceVerifierWitness.source_root, ← hroot]
  have hw : referenceFamilyWords (referenceTableSelection key f) dummy =
      canonicalReferenceWords ({ key with root := root } : SecretKey) f dummy := by
    rw [referenceFamilyWords_selected]
    exact (ReferenceVerifierWitness.canonicalReferenceWords_root key f root dummy).symm
  rw [canonicalGraphLabels_frontier key.parameter key.otsSecret key.ftsSecret f _ root, hw]
  rw [fixedBoundaryRun_retained_frontier ({ key with root := root } : SecretKey) f _ _
    (isSigningFrontier_canonical ({ key with root := root } : SecretKey) f _)
    (frontierReferenceWord_canonical ({ key with root := root } : SecretKey) f dummy), Functor.map_map]
  have h := congrArg (Functor.map (fun before =>
    let result := completeCertificateRest ({ key with root := root } : SecretKey) f before
    (({ key with root := root } : SecretKey), result.1, result.2)))
    (fixedTrace_forget f (CausalFrontierProgram.adversaryRun key.parameter root f key.ftsSecret
      (canonicalReferenceWords ({ key with root := root } : SecretKey) f dummy)
      (canonicalFrontierValues ({ key with root := root } : SecretKey) f (canonicalReferenceWords ({ key with root := root } : SecretKey) f dummy))
      (adversary.main ⟨root, key.parameter⟩)))
  rw [Functor.map_map, CausalFrontierProgram.fixed_adversaryRun] at h
  exact h

private theorem fixedHashWorld_lift_hash {Result : Type} (f : QueryImpl HashSpec Id)
    (computation : OracleComp HashSpec Result) :
    simulateQ (fixedHashWorld f) (liftM computation : OracleComp OracleWorld Result) = pure (evalWithAnswerFn f computation) := by
  have h := fixedBoundaryRun_forget 0 f (liftM computation : OracleComp OracleWorld Result)
  rw [fixedBoundaryRun_lift_hash, map_pure, boundaryEval_fst] at h
  exact h.symm

private theorem rootedKey_root_eq_treeRoot (key : SecretKey) (f : QueryImpl HashSpec Id) :
    (ReferenceVerifierWitness.rootedKey key f).root =
      evalWithAnswerFn f (treeRoot key.parameter topLayer rootTree (key.otsSecret topLayer rootTree)) := by
  simp only [honestNode, treeRoot]

noncomputable def fixedCertificateTraceGame (f : QueryImpl HashSpec Id) (adversary : Adversary) : ProbComp CertificateTraceRecord := do
  let parameter ← sampleParameter
  let otsSecret ← sampleOtsSecrets
  let ftsSecret ← sampleFtsSecrets
  let key := ReferenceVerifierWitness.rootedKey ⟨parameter, 0, otsSecret, ftsSecret⟩ f
  let result ← fixedBoundaryRun parameter f (simulateQ (expandedAdversaryImpl key)
    (retainedGameRestComputation adversary ⟨key.root, parameter⟩))
  pure (key, result.1, result.2)

theorem simulateQ_certificateTraceProgram (f : QueryImpl HashSpec Id) (adversary : Adversary) :
    simulateQ (fixedHashWorld f) (certificateTraceProgram adversary) = fixedCertificateTraceGame f adversary := by
  rw [certificateTraceProgram, show scheme.keygen = keygen by rw [scheme], keygen, fixedCertificateTraceGame]
  simp only [simulateQ_bind, simulateQ_fixedHashWorld_lift_prob, fixedHashWorld_lift_hash, simulateQ_pure,
    bind_assoc, pure_bind]
  apply bind_congr
  intro parameter
  apply bind_congr
  intro otsSecret
  apply bind_congr
  intro ftsSecret
  rw [← fixedBoundaryRun_eq_boundaryComputation, ← rootedKey_root_eq_treeRoot ⟨parameter, 0, otsSecret, ftsSecret⟩ f]

noncomputable def referenceCertificateRest (key : SecretKey) (f : QueryImpl HashSpec Id)
    (selections : ReferenceFamily) (dummy : OtsReferenceWords) (adversary : Adversary) : ProbComp CertificateTraceRecord :=
  (fun before =>
    let actualKey := ReferenceVerifierWitness.rootedKey key f
    let result := completeCertificateRest actualKey f before.1
    (actualKey, result.1, result.2)) <$>
      referenceForgeryRest key f (canonicalGraphLabels key.parameter key.otsSecret key.ftsSecret f) selections dummy adversary

theorem referenceCertificateRest_selected (key : SecretKey) (f : QueryImpl HashSpec Id)
    (dummy : OtsReferenceWords) (adversary : Adversary) :
    referenceCertificateRest key f (referenceTableSelection key f) dummy adversary =
      (fun result : RetainedRestResult × SigningBoundaryTrace =>
        (ReferenceVerifierWitness.rootedKey key f, result.1, result.2)) <$>
        fixedBoundaryRun key.parameter f (simulateQ (expandedAdversaryImpl (ReferenceVerifierWitness.rootedKey key f))
          (retainedGameRestComputation adversary ⟨(ReferenceVerifierWitness.rootedKey key f).root, key.parameter⟩)) :=
  referenceForgeryRest_certificateRecord_atRoot key f _ rfl dummy adversary

theorem referenceForgeryGame_certificateRecord (inputs : Finset HashInput)
    (hencoding : ∀ parameter, canonicalEncodingInputs parameter ⊆ inputs)
    (hgraph : ∀ parameter, canonicalGraphInputs parameter ⊆ inputs)
    (dummy : OtsReferenceWords) (adversary : Adversary) :
    ReferenceForgerySample.certificateRecord <$> referenceForgeryGame inputs hencoding dummy adversary =
      𝒟[do
        let table ← sampleHashTable inputs
        fixedCertificateTraceGame (finiteHashAnswer ∅ inputs table) adversary] := by
  rw [referenceForgeryGame]
  simp only [map_bind, map_pure, fixedCertificateTraceGame]
  rw [evalDist_bind_comm, evalDist_bind]
  apply congrArg (𝒟[sampleParameter] >>= ·)
  funext parameter
  rw [evalDist_bind_comm, evalDist_bind]
  apply congrArg (𝒟[sampleOtsSecrets] >>= ·)
  funext otsSecret
  rw [evalDist_bind_comm, evalDist_bind]
  apply congrArg (𝒟[sampleFtsSecrets] >>= ·)
  funext ftsSecret
  simp only [ReferenceForgerySample.certificateRecord, bind_pure_comp, ← evalDist_map]
  change (𝒟[referenceFamilyOracleSample ⟨parameter, 0, otsSecret, ftsSecret⟩ inputs (hencoding parameter)] >>= fun reference =>
    𝒟[referenceCertificateRest ⟨parameter, 0, otsSecret, ftsSecret⟩ (finiteHashAnswer ∅ inputs reference.2) reference.1 dummy adversary]) = _
  rw [referenceFamilyOracleSample_bind_selected ⟨parameter, 0, otsSecret, ftsSecret⟩ inputs (hencoding parameter) (hgraph parameter)
    (fun selections table => referenceCertificateRest ⟨parameter, 0, otsSecret, ftsSecret⟩
      (finiteHashAnswer ∅ inputs table) selections dummy adversary)]
  apply evalDist_bind_congr_left
  intro table
  rw [referenceCertificateRest_selected]

theorem referenceForgeryGame_native_certificateRecord (dummy : OtsReferenceWords) (adversary : Adversary) :
    ReferenceForgerySample.certificateRecord <$>
      referenceForgeryGame (canonicalGraphGameInputs adversary) (canonicalEncodingInputs_subset_gameInputs adversary) dummy adversary =
        𝒟[(simulateQ romImpl (certificateTraceProgram adversary)).run' ∅] := by
  rw [referenceForgeryGame_certificateRecord _ _ (canonicalGraphInputs_subset_gameInputs adversary),
    evalDist_romRun_eq_finiteHash _ (canonicalGraphGameInputs adversary)
      (by rw [certificateTraceProgram_hashInputs]; exact hashInputs_subset_canonicalGraphGameInputs adversary) ∅]
  apply evalDist_bind_congr_left
  intro table
  exact congrArg evalDist (simulateQ_certificateTraceProgram (finiteHashAnswer ∅ (canonicalGraphGameInputs adversary) table) adversary).symm

end SphincsSecurity.Concrete
