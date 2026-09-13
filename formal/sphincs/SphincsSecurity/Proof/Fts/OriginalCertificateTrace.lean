import SphincsSecurity.Proof.Fts.BoundaryCertificateCache
import SphincsSecurity.Proof.Reference.ReferenceForgerySource
namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec
open FtsProbeSimulation (RetainedRestResult retainedGameRestComputation)
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
attribute [local irreducible] scheme retainedGameRestComputation

abbrev CertificateTraceRecord := SecretKey × RetainedRestResult × SigningBoundaryTrace
abbrev OriginalCertificateTraceResult := OriginalCertificateResult × SigningBoundaryTrace

noncomputable def originalCertificateTraceSource (adversary : Adversary) : ProbComp OriginalCertificateTraceResult := do
  let generated ← (simulateQ romImpl scheme.keygen).run ∅
  let result ← boundaryRun generated.1.2.parameter
    (simulateQ (expandedAdversaryImpl generated.1.2) (retainedGameRestComputation adversary generated.1.1)) generated.2
  pure ((generated.1.2, result.1.1, result.2), result.1.2)

def OriginalCertificateTraceResult.record (result : OriginalCertificateTraceResult) : CertificateTraceRecord :=
  (result.1.1, result.1.2.1, result.2)

theorem originalCertificateTraceSource_original (adversary : Adversary) :
    Prod.fst <$> originalCertificateTraceSource adversary = originalCertificateSource adversary := by
  simp only [originalCertificateTraceSource, originalCertificateSource, map_bind, map_pure]
  apply bind_congr
  intro generated
  rw [OtsProbeSimulation.simulateQ_unloggedMapped_eq_expanded]
  have h := congrArg (Functor.map (fun result : RetainedRestResult × QueryCache HashSpec => (generated.1.2, result)))
    (boundaryRun_forget generated.1.2.parameter
      (simulateQ (expandedAdversaryImpl generated.1.2) (retainedGameRestComputation adversary generated.1.1)) generated.2)
  simpa only [Functor.map_map, bind_pure_comp] using h

theorem originalCertificateTraceSource_messageCache_le (adversary : Adversary) (result : OriginalCertificateTraceResult)
    (hr : result ∈ support (originalCertificateTraceSource adversary)) :
    hashRowsCache result.2.messageCalls ≤ result.1.2.2 := by
  simp only [originalCertificateTraceSource, mem_support_bind_iff] at hr
  obtain ⟨generated, _, recorded, hrecorded, hr⟩ := hr
  rw [mem_support_pure_iff] at hr
  subst result
  exact boundaryRun_messageCache_le _ _ _ recorded hrecorded

def CertificateTraceRecord.full (record : CertificateTraceRecord) : Prop :=
  SigningTranscript.Valid record.2.1.1.2 ∧
    ∃ input, TargetCertificateAt record.1 Finset.univ (hashRowsCache record.2.2.messageCalls, record.2.1.1.2) input

theorem originalCertificateTraceSource_full_le (adversary : Adversary) :
    Pr[fun result => result.record.full | originalCertificateTraceSource adversary] ≤
      Pr[OriginalFullCertificate | originalCertificateSource adversary] := by
  rw [← originalCertificateTraceSource_original, probEvent_map]
  apply _root_.probEvent_mono
  intro result hr hfull
  obtain ⟨hvalid, input, hcertificate⟩ := hfull
  exact ⟨hvalid, input, hcertificate.mono (originalCertificateTraceSource_messageCache_le adversary result hr)⟩

noncomputable def certificateTraceProgram (adversary : Adversary) : OracleComp OracleWorld CertificateTraceRecord := do
  let generated ← scheme.keygen
  let result ← boundaryComputation generated.2.parameter
    (simulateQ (expandedAdversaryImpl generated.2) (retainedGameRestComputation adversary generated.1))
  pure (generated.2, result.1, result.2)

theorem originalCertificateTraceSource_record (adversary : Adversary) :
    OriginalCertificateTraceResult.record <$> originalCertificateTraceSource adversary =
      (simulateQ romImpl (certificateTraceProgram adversary)).run' ∅ := by
  simp only [originalCertificateTraceSource, certificateTraceProgram, simulateQ_bind, simulateQ_pure,
    StateT.run'_eq, StateT.run_bind, StateT.run_pure, map_bind, map_pure, OriginalCertificateTraceResult.record]
  apply bind_congr
  intro generated
  have h := congrArg (Functor.map (fun result : RetainedRestResult × SigningBoundaryTrace =>
    (generated.1.2, result.1, result.2)))
    (boundaryRun_fst_eq_boundaryComputation generated.1.2.parameter
      (simulateQ (expandedAdversaryImpl generated.1.2) (retainedGameRestComputation adversary generated.1.1)) generated.2)
  simpa only [Functor.map_map, bind_pure_comp, StateT.run'_eq] using h

noncomputable def CertificateTraceRecord.verdict (record : CertificateTraceRecord) : Bool :=
  decide (SigningTranscript.Valid record.2.1.1.2 ∧ ¬SigningTranscript.Contains record.2.1.1.2 record.2.1.1.1) && record.2.1.2

theorem certificateTraceProgram_verdict (adversary : Adversary) :
    CertificateTraceRecord.verdict <$> certificateTraceProgram adversary = gameCore scheme adversary := by
  rw [certificateTraceProgram, gameCore_eq]
  simp only [map_bind, bind_pure_comp]
  apply bind_congr
  intro generated
  have h := congrArg (Functor.map (fun result : RetainedRestResult =>
    decide (SigningTranscript.Valid result.1.2 ∧ ¬SigningTranscript.Contains result.1.2 result.1.1) && result.2))
    (boundaryComputation_fst generated.2.parameter
      (simulateQ (expandedAdversaryImpl generated.2) (retainedGameRestComputation adversary generated.1)))
  rw [Functor.map_map] at h
  change (fun result : RetainedRestResult × SigningBoundaryTrace => CertificateTraceRecord.verdict (generated.2, result.1, result.2)) <$> _ = _ at h
  rw [Functor.map_map, h, OtsProbeSimulation.gameRest_eq_map_retained]
  unfold retainedGameRestComputation OtsProbeSimulation.retainedGameRestComputation
  rfl

theorem certificateTraceProgram_hashInputs (adversary : Adversary) :
    hashInputs (certificateTraceProgram adversary) = hashInputs (boundaryGameCore adversary) := by
  rw [← ResidualByteFrontend.hashInputs_map CertificateTraceRecord.verdict, certificateTraceProgram_verdict,
    ← boundaryGameCore_fst, ResidualByteFrontend.hashInputs_map]

theorem certificateTraceProgram_full_le (adversary : Adversary) :
    Pr[CertificateTraceRecord.full | (simulateQ romImpl (certificateTraceProgram adversary)).run' ∅] ≤
      Pr[OriginalFullCertificate | originalCertificateSource adversary] := by
  rw [← originalCertificateTraceSource_record, probEvent_map]
  exact originalCertificateTraceSource_full_le adversary

end SphincsSecurity.Concrete
