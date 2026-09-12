import SphincsSecurity.Proof.Base.Prelude
import SphincsSecurity.Proof.Fts.SigningProposalRecord
namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal
open FtsProbeSimulation (MessageHashInput messageAnswers)
attribute [local instance] Classical.propDecidable
attribute [local irreducible] signDigestLoop signAttempt

noncomputable def messageOnlyCache (parameter : PublicParameter) (cache : QueryCache HashSpec) : QueryCache HashSpec :=
  fun input => if MessageHashInput parameter input then cache input else none

theorem messageOnlyCache_apply (parameter : PublicParameter) (cache : QueryCache HashSpec) (input : HashInput)
    (hinput : MessageHashInput parameter input) : messageOnlyCache parameter cache input = cache input :=
  if_pos hinput

theorem messageOnlyCache_payload (parameter : PublicParameter) (cache : QueryCache HashSpec) (payload : HashInput) :
    messageOnlyCache parameter cache (tweakableHashInput parameter .message payload) =
      cache (tweakableHashInput parameter .message payload) :=
  messageOnlyCache_apply parameter cache _ ⟨payload, rfl⟩

theorem messageAnswers_messageOnlyCache (parameter : PublicParameter) (cache : QueryCache HashSpec) :
    messageAnswers parameter (messageOnlyCache parameter cache) = messageAnswers parameter cache := by
  funext payload
  exact messageOnlyCache_payload parameter cache payload

theorem messageOnlyCache_eq_of_messageAnswers_eq (parameter : PublicParameter) (left right : QueryCache HashSpec)
    (hcache : messageAnswers parameter left = messageAnswers parameter right) :
    messageOnlyCache parameter left = messageOnlyCache parameter right := by
  funext input
  by_cases hmessage : MessageHashInput parameter input
  · obtain ⟨payload, rfl⟩ := hmessage
    rw [messageOnlyCache_payload, messageOnlyCache_payload]
    exact congrFun hcache payload
  · simp only [messageOnlyCache, if_neg hmessage]

theorem cachedMessageInputSet_messageOnlyCache (parameter : PublicParameter) (root : Digest) (message : Message)
    (cache : QueryCache HashSpec) :
    cachedMessageInputSet (messageOnlyCache parameter cache) parameter root message =
      cachedMessageInputSet cache parameter root message := by
  ext ⟨input, output⟩
  constructor <;> rintro ⟨hcached, randomness, hinput⟩
  · refine ⟨?_, randomness, hinput⟩
    change input = tweakableHashInput parameter .message (messageDigestPayload root message randomness) at hinput
    subst input
    simpa only [QueryCache.mem_toSet, messageOnlyCache_payload] using hcached
  · refine ⟨?_, randomness, hinput⟩
    change input = tweakableHashInput parameter .message (messageDigestPayload root message randomness) at hinput
    subst input
    simpa only [QueryCache.mem_toSet, messageOnlyCache_payload] using hcached

theorem cachedMessageEntryCount_messageOnlyCache (parameter : PublicParameter) (root : Digest) (message : Message)
    (cache : QueryCache HashSpec) :
    cachedMessageEntryCount (messageOnlyCache parameter cache) parameter root message =
      cachedMessageEntryCount cache parameter root message := by
  rw [cachedMessageEntryCount, cachedMessageEntryCount, cachedMessageInputSet_messageOnlyCache]

theorem cachedMessageEntryCountWhere_messageOnlyCache (parameter : PublicParameter) (root : Digest) (message : Message)
    (cache : QueryCache HashSpec) (P : FewTimeView → Prop) :
    cachedMessageEntryCountWhere (messageOnlyCache parameter cache) parameter root message P =
      cachedMessageEntryCountWhere cache parameter root message P := by
  simp only [cachedMessageEntryCountWhere, cachedMessageInputSetWhere, cachedMessageInputSet_messageOnlyCache]

theorem cacheMessageWeight_messageOnlyCache (parameter : PublicParameter) (cache : QueryCache HashSpec)
    (weight : HashInput → FewTimeView → ENNReal) :
    cacheMessageWeight parameter weight (messageOnlyCache parameter cache) = cacheMessageWeight parameter weight cache := by
  apply tsum_congr
  intro input
  by_cases hmessage : MessageHashInput parameter input
  · simp only [cacheMessageEntryWeight, messageOnlyCache_apply parameter cache input hmessage]
  · simp only [cacheMessageEntryWeight, messageOnlyCache, if_neg hmessage]
    cases cache input <;> simp only [hmessage, false_and, if_false]

end SphincsSecurity.Concrete
