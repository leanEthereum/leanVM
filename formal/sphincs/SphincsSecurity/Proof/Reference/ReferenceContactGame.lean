import SphincsSecurity.Proof.Ots.OtsContactSplit
import SphincsSecurity.Proof.Reference.ReferenceInstrumentedGame
namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
attribute [local irreducible] canonicalGraphInputs canonicalEncodingInputs canonicalGraphGameInputs OtsContactTrace.contacts

structure ContactResult where
  frontier : OtsFrontierValues
  before : OtsContactTrace.Trace
  output : Bool × SigningBoundaryTrace
  after : OtsContactTrace.Trace

noncomputable def contactObserver : FrontierObserver ContactResult := fun parameter words frontier computation =>
  (fun result => ⟨frontier, result.1, result.2.1, result.2.2⟩) <$> OtsContactTrace.splitRun parameter words frontier computation

theorem contactObserver_frontier_trace (parameter : PublicParameter) (words : OtsReferenceWords) (frontier : OtsFrontierValues)
    (computation : OracleComp OracleWorld (Bool × SigningBoundaryTrace)) :
    (fun result : ContactResult => (result.frontier, result.output, result.before * result.after)) <$>
      contactObserver parameter words frontier computation =
        (fun result => (frontier, result)) <$> QueryPause.traced hashObservationTrace computation := by
  simpa only [contactObserver, Functor.map_map] using
    congrArg (Functor.map (fun result => (frontier, result))) (OtsContactTrace.splitRun_trace parameter words frontier computation)

theorem contactObserver_forget (parameter : PublicParameter) (words : OtsReferenceWords) (frontier : OtsFrontierValues)
    (computation : OracleComp OracleWorld (Bool × SigningBoundaryTrace)) :
    ContactResult.output <$> contactObserver parameter words frontier computation = computation := by
  simpa only [contactObserver, Functor.map_map] using OtsContactTrace.splitRun_forget parameter words frontier computation

noncomputable abbrev referenceContactGame (inputs : Finset HashInput)
    (hencoding : ∀ parameter, canonicalEncodingInputs parameter ⊆ inputs) (dummy : OtsReferenceWords) (adversary : Adversary) :=
  referenceInstrumentedGame contactObserver inputs hencoding dummy adversary

theorem referenceContactGame_erased (inputs : Finset HashInput)
    (hencoding : ∀ parameter, canonicalEncodingInputs parameter ⊆ inputs) (dummy : OtsReferenceWords) (adversary : Adversary) :
    (fun result => (result.2.1, result.2.2.output)) <$> referenceContactGame inputs hencoding dummy adversary =
      referenceFamilyGame inputs hencoding dummy adversary :=
  referenceInstrumentedGame_erased contactObserver ContactResult.output contactObserver_forget inputs hencoding dummy adversary

theorem forgeAdvantage_eq_referenceContact (dummy : OtsReferenceWords) (adversary : Adversary) :
    forgeAdvantage scheme adversary = Pr[fun result => result.2.2.output.1 = true |
      referenceContactGame (canonicalGraphGameInputs adversary) (canonicalEncodingInputs_subset_gameInputs adversary) dummy adversary] := by
  rw [forgeAdvantage_eq_referenceFamily dummy adversary, ← referenceContactGame_erased, probEvent_map]
  rfl

theorem referenceContactGame_hashCalls_le (dummy : OtsReferenceWords) (adversary : Adversary) (budget : Nat)
    (hbound : HasHashQueryBound scheme adversary budget) (result : InstrumentedResult ContactResult)
    (hresult : result ∈ support (referenceContactGame (canonicalGraphGameInputs adversary)
      (canonicalEncodingInputs_subset_gameInputs adversary) dummy adversary)) : result.2.2.output.2.hashCalls ≤ budget := by
  apply referenceFamilyGame_hashCalls_le dummy adversary budget hbound (result.2.1, result.2.2.output)
  rw [← referenceContactGame_erased, support_map]
  exact ⟨result, hresult, rfl⟩

theorem contactObserver_cost (parameter : PublicParameter) (external : QueryImpl HashSpec Id)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (words : OtsReferenceWords) (frontier : OtsFrontierValues)
    (adversary : Adversary) (result : ContactResult)
    (hresult : result ∈ support (contactObserver parameter words frontier
      (CausalFrontierProgram.game parameter external ftsSecret words frontier adversary))) :
    (result.before * result.after).toList.length ≤ result.output.2.hashCalls := by
  rw [contactObserver, support_map] at hresult
  obtain ⟨split, hsplit, rfl⟩ := hresult
  exact OtsContactTrace.splitRun_game_cost parameter words frontier external ftsSecret adversary split hsplit

theorem referenceContactGame_cost (inputs : Finset HashInput)
    (hencoding : ∀ parameter, canonicalEncodingInputs parameter ⊆ inputs) (dummy : OtsReferenceWords) (adversary : Adversary)
    (result : InstrumentedResult ContactResult) (hresult : result ∈ support (referenceContactGame inputs hencoding dummy adversary)) :
    (result.2.2.before * result.2.2.after).toList.length ≤ result.2.2.output.2.hashCalls := by
  simp only [referenceContactGame, referenceInstrumentedGame, mem_support_bind_iff] at hresult
  obtain ⟨parameter, _, otsSecret, _, ftsSecret, _, reference, _, output, houtput, hresult⟩ := hresult
  rw [mem_support_pure_iff] at hresult
  subst result
  have hsyntax := (mem_support_iff_of_evalDist_eq (mx := referenceInstrumentedRest contactObserver _ _ _ _ dummy adversary)
    (mx' := 𝒟[referenceInstrumentedRest contactObserver _ _ _ _ dummy adversary]) rfl output).mpr houtput
  exact contactObserver_cost _ _ _ _ _ adversary output (QueryCap.simulate_oracle_mem_support _ _ output hsyntax)

def ContactResult.Marked (parameter : PublicParameter) (words : OtsReferenceWords) (result : ContactResult) : Prop :=
  OtsContactTrace.Stopped parameter words result.frontier result.before

noncomputable def ContactResult.restartCharge (parameter : PublicParameter) (words : OtsReferenceWords)
    (address : OtsPrefix.ChainAddress) (result : ContactResult) : Nat :=
  if result.Marked parameter words ∧ address ∉ OtsContactTrace.contacts parameter words result.frontier result.before then
    OtsContactTrace.prefixCalls (OtsPrefix.atAddress parameter words address) result.before +
      2 * OtsContactTrace.prefixCalls (OtsPrefix.atAddress parameter words address) result.after
  else 0

theorem ContactResult.restartCharge_sum_le (parameter : PublicParameter) (words : OtsReferenceWords)
    (result : ContactResult) (budget : Nat) (hbudget : (result.before * result.after).toList.length ≤ budget) :
    (∑ address : OtsPrefix.ChainAddress, result.restartCharge parameter words address) ≤
      if result.Marked parameter words then 2 * budget else 0 := by
  by_cases hm : result.Marked parameter words
  · simp only [ContactResult.restartCharge, hm, true_and, if_true]
    rw [← Finset.sum_filter]
    exact OtsContactTrace.restartCharge_le_budget parameter words _ result.before result.after budget hbudget
  · simp only [ContactResult.restartCharge, hm, false_and, if_false, Finset.sum_const_zero, le_refl]

end SphincsSecurity.Concrete
