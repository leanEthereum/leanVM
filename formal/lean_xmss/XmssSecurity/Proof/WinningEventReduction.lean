import XmssSecurity.Proof.OutcomeClassification

open OracleComp OracleSpec ENNReal

namespace XmssSecurity

/-- A classified bad event on an execution that actually wins the signature game. Keeping the winning condition exposes transcript validity without weakening the deterministic classification. -/
def WinningOutcomeBadEventOccurs (cache : QueryCache HashSpec)
    (outcome : GameOutcome) (event : BadEvent) : Prop :=
  outcome.won = true ∧ OutcomeBadEventOccurs cache outcome event

theorem SigningTranscript.length_le_lifetime {log : QueryLog SigningSpec}
    (hvalid : SigningTranscript.Valid log) :
    log.length ≤ lifetime := by
  unfold SigningTranscript.Valid at hvalid
  simpa using List.Nodup.length_le_card hvalid

theorem SigningTranscript.returned_eq_of_same_leafIndex
    {log : QueryLog SigningSpec} {leftRequest rightRequest : SignRequest}
    {leftSignature rightSignature : Signature}
    (hvalid : SigningTranscript.Valid log)
    (hleft : SigningTranscript.Returned log leftRequest leftSignature)
    (hright : SigningTranscript.Returned log rightRequest rightSignature)
    (hleafIndex : leftRequest.leafIndex = rightRequest.leafIndex) :
    leftRequest = rightRequest ∧ leftSignature = rightSignature := by
  obtain ⟨leftEntry, hleftMem, hleftRequest, hleftSignature⟩ := hleft
  obtain ⟨rightEntry, hrightMem, hrightRequest, hrightSignature⟩ := hright
  unfold SigningTranscript.Valid at hvalid
  have hentry : leftEntry = rightEntry :=
    List.inj_on_of_nodup_map hvalid hleftMem hrightMem (by
      simpa only [hleftRequest, hrightRequest] using hleafIndex)
  subst rightEntry
  constructor
  · exact hleftRequest.symm.trans hrightRequest
  · have hoptions : some leftSignature = some rightSignature := by
      rw [← hleftSignature, ← hrightSignature]
    exact Option.some.inj hoptions

theorem WinningOutcomeBadEventOccurs.signingTranscript_valid
    {cache : QueryCache HashSpec} {outcome : GameOutcome} {event : BadEvent}
    (hevent : WinningOutcomeBadEventOccurs cache outcome event) :
    SigningTranscript.Valid outcome.signingLog :=
  ((GameOutcome.won_eq_true_iff outcome).mp hevent.1).1

theorem WinningOutcomeBadEventOccurs.signingLog_length_le_lifetime
    {cache : QueryCache HashSpec} {outcome : GameOutcome} {event : BadEvent}
    (hevent : WinningOutcomeBadEventOccurs cache outcome event) :
    outcome.signingLog.length ≤ lifetime :=
  SigningTranscript.length_le_lifetime hevent.signingTranscript_valid

theorem WinningOutcomeBadEventOccurs.forgery_decode
    {cache : QueryCache HashSpec} {outcome : GameOutcome} {event : BadEvent}
    (hevent : WinningOutcomeBadEventOccurs cache outcome event) :
    ∃ encoding, TargetSum.decodeDigest
      (Concrete.CacheView.encodingHash cache outcome.secretKey.parameter
        outcome.forgery.leafIndex
        (outcome.forgery.message, outcome.forgery.signature.randomness)) = some encoding := by
  rcases hevent.2.2 with hsame | hfresh
  · obtain ⟨request, signature, signedEncoding, forgedEncoding, hsignedDecode,
      hforgedDecode, hreturned, hleafIndex, hbad⟩ := hsame
    rw [hleafIndex] at hforgedDecode
    exact ⟨forgedEncoding, hforgedDecode⟩
  · obtain ⟨forgedEncoding, hvalid, hfreshLeafIndex, hforgedDecode, hbad⟩ := hfresh
    exact ⟨forgedEncoding, hforgedDecode⟩

end XmssSecurity
