import SphincsSecurity.Proof.Ots.OtsTraceProbability
import SphincsSecurity.Proof.Ots.EncodingMarkerAllocation
namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
attribute [local irreducible] canonicalGraphInputs canonicalEncodingInputs canonicalGraphGameInputs Finset.univ

theorem referenceCheckpointRest_frontier_trace (stop : FrontierStop)
    [∀ parameter words frontier, DecidablePred (stop parameter words frontier)] (key : SecretKey) (oracle : QueryImpl HashSpec Id)
    (labels : CanonicalGraphLabels) (selections : ReferenceFamily) (dummy : OtsReferenceWords) (adversary : Adversary) :
    (fun result : ContactResult => (result.frontier, result.output, result.before * result.after)) <$>
      referenceInstrumentedRest (checkpointObserver stop) key oracle labels selections dummy adversary =
        (fun result : ContactResult => (result.frontier, result.output, result.before * result.after)) <$>
          referenceInstrumentedRest contactObserver key oracle labels selections dummy adversary := by
  rw [referenceInstrumentedRest, referenceInstrumentedRest, ← simulateQ_map, ← simulateQ_map,
    checkpointObserver_frontier_trace, contactObserver_frontier_trace]

theorem referenceCheckpointGame_frontier_trace (stop : FrontierStop)
    [∀ parameter words frontier, DecidablePred (stop parameter words frontier)] (inputs : Finset HashInput)
    (hencoding : ∀ parameter, canonicalEncodingInputs parameter ⊆ inputs) (dummy : OtsReferenceWords) (adversary : Adversary) :
    (fun result : InstrumentedResult ContactResult => (result.1, result.2.1, result.2.2.frontier, result.2.2.output, result.2.2.before * result.2.2.after)) <$>
        referenceInstrumentedGame (checkpointObserver stop) inputs hencoding dummy adversary =
      (fun result : InstrumentedResult ContactResult => (result.1, result.2.1, result.2.2.frontier, result.2.2.output, result.2.2.before * result.2.2.after)) <$>
        referenceContactGame inputs hencoding dummy adversary := by
  unfold referenceContactGame referenceInstrumentedGame
  simp only [map_bind, map_pure]
  apply congrArg (𝒟[sampleParameter] >>= ·)
  funext parameter
  apply congrArg (𝒟[sampleOtsSecrets] >>= ·)
  funext otsSecret
  apply congrArg (𝒟[sampleFtsSecrets] >>= ·)
  funext ftsSecret
  apply congrArg (𝒟[referenceFamilyOracleSample _ inputs (hencoding parameter)] >>= ·)
  funext reference
  have h := congrArg (fun law => (fun result => (parameter, reference.1, result.1, result.2)) <$> 𝒟[law])
    (referenceCheckpointRest_frontier_trace stop ⟨parameter, 0, otsSecret, ftsSecret⟩ (finiteHashAnswer ∅ inputs reference.2)
      (canonicalGraphLabels parameter otsSecret ftsSecret (finiteHashAnswer ∅ inputs reference.2)) reference.1 dummy adversary)
  simpa only [← bind_pure_comp, evalDist_bind, evalDist_pure, bind_assoc, pure_bind] using h

def OtsEncodingMarker.stopAt (address : OtsPrefix.ChainAddress) : FrontierStop :=
  fun parameter words _ trace => OtsEncodingMarker.Seen parameter words address trace

noncomputable abbrev markerCheckpointGame (address : OtsPrefix.ChainAddress) (inputs : Finset HashInput)
    (hencoding : ∀ parameter, canonicalEncodingInputs parameter ⊆ inputs) (dummy : OtsReferenceWords) (adversary : Adversary) :=
  referenceInstrumentedGame (checkpointObserver (OtsEncodingMarker.stopAt address)) inputs hencoding dummy adversary

theorem markerCheckpointGame_marker_probability (inputs : Finset HashInput)
    (hencoding : ∀ parameter, canonicalEncodingInputs parameter ⊆ inputs) (address : OtsPrefix.ChainAddress)
    (dummy : OtsReferenceWords) (adversary : Adversary) :
    Pr[fun result => OtsEncodingMarker.Seen result.1 (referenceFamilyWords result.2.1 dummy) address (result.2.2.before * result.2.2.after) |
      markerCheckpointGame address inputs hencoding dummy adversary] =
    Pr[fun result => OtsEncodingMarker.Seen result.1 (referenceFamilyWords result.2.1 dummy) address (result.2.2.before * result.2.2.after) |
      referenceContactGame inputs hencoding dummy adversary] := by
  have h := congrArg (fun law : SPMF (PublicParameter × ReferenceFamily × OtsFrontierValues × (Bool × SigningBoundaryTrace) × OtsContactTrace.Trace) =>
    Pr[fun result => OtsEncodingMarker.Seen result.1 (referenceFamilyWords result.2.1 dummy) address result.2.2.2.2 | law])
    (referenceCheckpointGame_frontier_trace (OtsEncodingMarker.stopAt address) inputs hencoding dummy adversary)
  simpa only [probEvent_map, Function.comp_def] using h

theorem markerCheckpointGame_contact_le_marker (address : OtsPrefix.ChainAddress) (dummy : OtsReferenceWords)
    (adversary : Adversary) (budget : Nat) (hbound : HasHashQueryBound scheme adversary budget)
    (hsmall : budget < Fintype.card Digest) :
    ((1 - (budget : ENNReal) / Fintype.card Digest) * (Fintype.card Digest : ENNReal)) *
      Pr[fun result => result.2.2.ContactAfterStop (OtsEncodingMarker.stopAt address) result.1 (referenceFamilyWords result.2.1 dummy) address |
        markerCheckpointGame address (canonicalGraphGameInputs adversary) (canonicalEncodingInputs_subset_gameInputs adversary) dummy adversary] ≤
      (2 * budget : Nat) * Pr[fun result => OtsEncodingMarker.Seen result.1 (referenceFamilyWords result.2.1 dummy) address
        (result.2.2.before * result.2.2.after) | referenceContactGame (canonicalGraphGameInputs adversary)
          (canonicalEncodingInputs_subset_gameInputs adversary) dummy adversary] := by
  have h := referenceCheckpointGame_newContact_le_mark (OtsEncodingMarker.stopAt address) address dummy adversary budget hbound hsmall
  refine h.trans (mul_le_mul' le_rfl ?_)
  rw [← markerCheckpointGame_marker_probability]
  exact _root_.probEvent_mono (fun result _ hm => (OtsEncodingMarker.seen_mul _ _ _ _ _).mpr (Or.inl hm))

end SphincsSecurity.Concrete
