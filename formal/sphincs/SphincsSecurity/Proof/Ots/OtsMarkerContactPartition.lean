import SphincsSecurity.Proof.Ots.OtsMarkerContactSource
import SphincsSecurity.Proof.Ots.OtsContactMarkerTrace
namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
attribute [local irreducible] OtsContactTrace.contacts canonicalEncodingInputs Finset.univ

namespace OtsEncodingMarker

theorem ContactBeforeMarker.mul_right {parameter : PublicParameter} {words : OtsReferenceWords}
    {frontier : OtsFrontierValues} {trace : OtsContactTrace.Trace}
    (h : ContactBeforeMarker parameter words frontier trace) (tail : OtsContactTrace.Trace) :
    ContactBeforeMarker parameter words frontier (trace * tail) := by
  obtain ⟨before, entry, after, he, hm⟩ := h
  refine ⟨before, entry, after ++ tail.toList, ?_, hm⟩
  simp only [FreeMonoid.toList_mul, he, List.append_assoc, List.cons_append]

theorem contactBeforeMarker_of_newMarker (parameter : PublicParameter) (words : OtsReferenceWords) (frontier : OtsFrontierValues)
    (history : OtsContactTrace.Trace) (address : OtsPrefix.ChainAddress) (entry : HashInput × HashOutput)
    (hc : address ∈ OtsContactTrace.contacts parameter words frontier history) (hm : NewMarker parameter words history address entry) :
    ContactBeforeMarker parameter words frontier (history * FreeMonoid.of entry) := by
  refine ⟨history.toList, entry, [], ?_, ?_⟩
  · simp only [FreeMonoid.toList_mul, FreeMonoid.toList_of]
  · exact ⟨address, hc, hm⟩

theorem markerPause_contact_first {Result : Type} (parameter : PublicParameter) (words : OtsReferenceWords)
    (frontier : OtsFrontierValues) (address : OtsPrefix.ChainAddress) (computation : OracleComp OracleWorld Result)
    (result : OtsContactTrace.Trace × OracleComp OracleWorld Result)
    (hr : result ∈ support (QueryPause.run (stopAt address parameter words frontier)
      (fun input answer history => history * hashObservationTrace input answer) computation 1))
    (hm : Seen parameter words address result.1) (hc : address ∈ OtsContactTrace.contacts parameter words frontier result.1) :
    ContactBeforeMarker parameter words frontier result.1 := by
  have h := QueryPause.run_invariant (stopAt address parameter words frontier)
    (fun input answer history => history * hashObservationTrace input answer)
    (fun history => Seen parameter words address history → address ∈ OtsContactTrace.contacts parameter words frontier history →
      ContactBeforeMarker parameter words frontier history) ?_ computation 1 ?_ result hr
  · exact h hm hc
  · intro history _ hn input answer hm hc
    cases input with
    | inl input =>
        simp only [hashObservationTrace, mul_one] at hm
        exact False.elim (hn hm)
    | inr input =>
        have he : EntryMarker parameter words address (input, answer) :=
          (seen_of _ _ _ _).mp (((seen_mul _ _ _ _ _).mp hm).resolve_left hn)
        rw [hashObservationTrace, OtsContactTrace.contacts_mul, Finset.mem_union] at hc
        rcases hc with hc | hc
        · exact contactBeforeMarker_of_newMarker parameter words frontier history address (input, answer) hc ⟨he, hn⟩
        · exact False.elim (entryMarker_not_contact parameter words address address _ (input, answer) he
            ((OtsContactTrace.seen_of _ _ _).mp ((OtsContactTrace.mem_contacts _ _ _ _ _).mp hc)))
  · exact fun hm _ => False.elim (seen_one parameter words address hm)

theorem markerSplitRun_partition {Result : Type} (parameter : PublicParameter) (words : OtsReferenceWords)
    (frontier : OtsFrontierValues) (address : OtsPrefix.ChainAddress) (computation : OracleComp OracleWorld Result)
    (result : OtsContactTrace.Trace × (Result × OtsContactTrace.Trace))
    (hr : result ∈ support (checkpointSplitRun (stopAt address) parameter words frontier computation))
    (hm : Seen parameter words address (result.1 * result.2.2))
    (hn : ¬ContactBeforeMarker parameter words frontier (result.1 * result.2.2)) :
    Seen parameter words address result.1 ∧ address ∉ OtsContactTrace.contacts parameter words frontier result.1 := by
  simp only [checkpointSplitRun, mem_support_bind_iff, mem_support_pure_iff] at hr
  obtain ⟨middle, hmiddle, tail, htail, rfl⟩ := hr
  have hbefore : Seen parameter words address middle.1 := by
    rcases QueryPause.run_stopped_or_finished (stopAt address parameter words frontier)
      (fun input answer history => history * hashObservationTrace input answer) computation 1 middle hmiddle with hs | ⟨value, hv⟩
    · exact hs
    · rw [hv, QueryPause.traced_pure, mem_support_pure_iff] at htail
      subst tail
      simpa only [mul_one] using hm
  refine ⟨hbefore, fun hc => hn ?_⟩
  exact (markerPause_contact_first parameter words frontier address computation middle hmiddle hbefore hc).mul_right tail.2

end OtsEncodingMarker

def ContactResult.MarkerContact (parameter : PublicParameter) (words : OtsReferenceWords) (result : ContactResult) : Prop :=
  ∃ address, OtsEncodingMarker.Seen parameter words address (result.before * result.after) ∧
    address ∈ OtsContactTrace.contacts parameter words result.frontier (result.before * result.after)

theorem markerObserver_partition (parameter : PublicParameter) (words : OtsReferenceWords) (frontier : OtsFrontierValues)
    (address : OtsPrefix.ChainAddress) (computation : OracleComp OracleWorld (Bool × SigningBoundaryTrace))
    (result : ContactResult) (hr : result ∈ support (checkpointObserver (OtsEncodingMarker.stopAt address) parameter words frontier computation))
    (hm : OtsEncodingMarker.Seen parameter words address (result.before * result.after))
    (hc : address ∈ OtsContactTrace.contacts parameter words result.frontier (result.before * result.after))
    (hn : ¬OtsEncodingMarker.ContactBeforeMarker parameter words result.frontier (result.before * result.after)) :
    result.ContactAfterStop (OtsEncodingMarker.stopAt address) parameter words address := by
  rw [checkpointObserver, support_map] at hr
  obtain ⟨split, hs, rfl⟩ := hr
  exact ⟨OtsEncodingMarker.markerSplitRun_partition parameter words frontier address computation split hs hm hn, hc⟩

theorem markerCheckpointGame_partition (inputs : Finset HashInput)
    (hencoding : ∀ parameter, canonicalEncodingInputs parameter ⊆ inputs) (address : OtsPrefix.ChainAddress)
    (dummy : OtsReferenceWords) (adversary : Adversary) (result : InstrumentedResult ContactResult)
    (hr : result ∈ support (markerCheckpointGame address inputs hencoding dummy adversary))
    (hm : OtsEncodingMarker.Seen result.1 (referenceFamilyWords result.2.1 dummy) address (result.2.2.before * result.2.2.after))
    (hc : address ∈ OtsContactTrace.contacts result.1 (referenceFamilyWords result.2.1 dummy) result.2.2.frontier (result.2.2.before * result.2.2.after))
    (hn : ¬OtsEncodingMarker.ContactBeforeMarker result.1 (referenceFamilyWords result.2.1 dummy) result.2.2.frontier
      (result.2.2.before * result.2.2.after)) :
    result.2.2.ContactAfterStop (OtsEncodingMarker.stopAt address) result.1 (referenceFamilyWords result.2.1 dummy) address := by
  simp only [markerCheckpointGame, referenceInstrumentedGame, mem_support_bind_iff] at hr
  obtain ⟨parameter, _, otsSecret, _, ftsSecret, _, reference, _, output, houtput, hr⟩ := hr
  rw [mem_support_pure_iff] at hr
  subst result
  have hsyntax := (mem_support_iff_of_evalDist_eq
    (mx := referenceInstrumentedRest (checkpointObserver (OtsEncodingMarker.stopAt address)) _ _ _ _ dummy adversary)
    (mx' := 𝒟[referenceInstrumentedRest (checkpointObserver (OtsEncodingMarker.stopAt address)) _ _ _ _ dummy adversary]) rfl output).mpr houtput
  exact markerObserver_partition _ _ _ address _ output (QueryCap.simulate_oracle_mem_support _ _ output hsyntax) hm hc hn

end SphincsSecurity.Concrete
