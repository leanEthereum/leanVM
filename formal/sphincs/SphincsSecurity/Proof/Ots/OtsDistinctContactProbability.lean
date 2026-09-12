import SphincsSecurity.Proof.Ots.OtsContactProbability
namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
attribute [local irreducible] canonicalGraphInputs canonicalEncodingInputs canonicalGraphGameInputs OtsContactTrace.contacts Finset.univ

def ContactResult.TwoContacts (parameter : PublicParameter) (words : OtsReferenceWords) (result : ContactResult) : Prop :=
  2 ≤ (OtsContactTrace.contacts parameter words result.frontier (result.before * result.after)).card

theorem contactObserver_two_contacts (parameter : PublicParameter) (words : OtsReferenceWords) (frontier : OtsFrontierValues)
    (computation : OracleComp OracleWorld (Bool × SigningBoundaryTrace)) (result : ContactResult)
    (hresult : result ∈ support (contactObserver parameter words frontier computation))
    (htwo : result.TwoContacts parameter words) : ∃ address, result.NewContact parameter words address := by
  rw [contactObserver, support_map] at hresult
  obtain ⟨split, hsplit, rfl⟩ := hresult
  obtain ⟨hmarked, address, hbefore, hafter⟩ := OtsContactTrace.splitRun_two_contacts parameter words frontier computation split hsplit htwo
  refine ⟨address, ⟨hmarked, hbefore⟩, ?_⟩
  rw [OtsContactTrace.contacts_mul]
  exact Finset.mem_union_right _ hafter

theorem referenceContactGame_two_contacts (inputs : Finset HashInput)
    (hencoding : ∀ parameter, canonicalEncodingInputs parameter ⊆ inputs) (dummy : OtsReferenceWords) (adversary : Adversary)
    (result : InstrumentedResult ContactResult) (hresult : result ∈ support (referenceContactGame inputs hencoding dummy adversary))
    (htwo : result.2.2.TwoContacts result.1 (referenceFamilyWords result.2.1 dummy)) :
    ∃ address, result.2.2.NewContact result.1 (referenceFamilyWords result.2.1 dummy) address := by
  simp only [referenceContactGame, referenceInstrumentedGame, mem_support_bind_iff] at hresult
  obtain ⟨parameter, _, otsSecret, _, ftsSecret, _, reference, _, output, houtput, hresult⟩ := hresult
  rw [mem_support_pure_iff] at hresult
  subst result
  have hsyntax := (mem_support_iff_of_evalDist_eq (mx := referenceInstrumentedRest contactObserver _ _ _ _ dummy adversary)
    (mx' := 𝒟[referenceInstrumentedRest contactObserver _ _ _ _ dummy adversary]) rfl output).mpr houtput
  exact contactObserver_two_contacts _ _ _ _ output (QueryCap.simulate_oracle_mem_support _ _ output hsyntax) htwo

theorem referenceContactGame_twoContacts_le_sum (inputs : Finset HashInput)
    (hencoding : ∀ parameter, canonicalEncodingInputs parameter ⊆ inputs) (dummy : OtsReferenceWords) (adversary : Adversary) :
    let law := referenceContactGame inputs hencoding dummy adversary
    Pr[fun result => result.2.2.TwoContacts result.1 (referenceFamilyWords result.2.1 dummy) | law] ≤
      ∑ address : OtsPrefix.ChainAddress,
        Pr[fun result => result.2.2.NewContact result.1 (referenceFamilyWords result.2.1 dummy) address | law] := by
  dsimp only
  let law := referenceContactGame inputs hencoding dummy adversary
  let event := fun address : OtsPrefix.ChainAddress => fun result : InstrumentedResult ContactResult =>
    result.2.2.NewContact result.1 (referenceFamilyWords result.2.1 dummy) address
  refine (_root_.probEvent_mono (mx := law) (q := fun result => ∃ address ∈ (Finset.univ : Finset OtsPrefix.ChainAddress), event address result) ?_).trans
    (probEvent_exists_finset_le_sum Finset.univ law event)
  intro result hr ht
  obtain ⟨address, ha⟩ := referenceContactGame_two_contacts inputs hencoding dummy adversary result hr ht
  refine ⟨address, ?_, ha⟩
  exact Finset.mem_univ address

theorem referenceContactGame_distinct_restart_le (dummy : OtsReferenceWords) (adversary : Adversary) (budget : Nat)
    (hbound : HasHashQueryBound scheme adversary budget) (hsmall : budget < Fintype.card Digest) :
    let law := referenceContactGame (canonicalGraphGameInputs adversary) (canonicalEncodingInputs_subset_gameInputs adversary) dummy adversary
    ((1 - (budget : ENNReal) / Fintype.card Digest) * (Fintype.card Digest : ENNReal)) *
      Pr[fun result => result.2.2.TwoContacts result.1 (referenceFamilyWords result.2.1 dummy) | law] ≤
      ((2 * budget : Nat) : ENNReal) * Pr[fun result => result.2.2.Marked result.1 (referenceFamilyWords result.2.1 dummy) | law] := by
  dsimp only
  have hsum := Finset.sum_le_sum (s := (Finset.univ : Finset OtsPrefix.ChainAddress))
    fun address _ => referenceContactGame_newContact_le address dummy adversary budget hbound hsmall
  rw [← Finset.mul_sum] at hsum
  exact (mul_le_mul' le_rfl (referenceContactGame_twoContacts_le_sum _ _ dummy adversary)).trans
    (hsum.trans (referenceContactGame_restart_allocation dummy adversary budget hbound))

end SphincsSecurity.Concrete
