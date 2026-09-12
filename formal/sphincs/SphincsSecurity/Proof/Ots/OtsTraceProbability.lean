import SphincsSecurity.Proof.Ots.OtsTraceEvents
import SphincsSecurity.Proof.Ots.OtsPrefixInstrumentedSource
import SphincsSecurity.Proof.Ots.OtsPrefixObservedBudget
namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
attribute [local irreducible] canonicalGraphLabels canonicalEncodingInputs canonicalGraphInputs instFintypePosition

private theorem scaled_probability_bind_le {Value Left Right : Type} (law : SPMF Value)
    (left : Value → SPMF Left) (right : Value → SPMF Right) (eventLeft : Left → Prop) (eventRight : Right → Prop)
    (a b : ENNReal) (h : ∀ value ∈ support law, a * Pr[eventLeft | left value] ≤ b * Pr[eventRight | right value]) :
    a * Pr[eventLeft | law >>= left] ≤ b * Pr[eventRight | law >>= right] := by
  rw [probEvent_bind_eq_tsum, probEvent_bind_eq_tsum, ← ENNReal.tsum_mul_left, ← ENNReal.tsum_mul_left]
  apply ENNReal.tsum_le_tsum
  intro value
  by_cases hv : value ∈ support law
  · simpa only [mul_left_comm] using mul_le_mul' (le_refl (Pr[= value | law])) (h value hv)
  · simp only [probOutput_eq_zero_of_not_mem_support hv, zero_mul, mul_zero, le_refl]

private theorem probComp_mem_of_evalDist {Result : Type} (computation : ProbComp Result) (result : Result)
    (hresult : result ∈ support 𝒟[computation]) : result ∈ support computation :=
  (mem_support_iff_of_evalDist_eq (mx := computation) (mx' := 𝒟[computation]) rfl result).mpr hresult

private theorem pmf_mem_of_evalDist {Result : Type} (law : PMF Result) (result : Result)
    (hresult : result ∈ support 𝒟[law]) : result ∈ law.support := by
  change result ∈ (𝒟[law]).support at hresult
  simpa only [PMF.evalDist_eq, SPMF.support_liftM] using hresult

theorem referenceCheckpointGame_newContact_le_mark (stop : FrontierStop)
    [∀ parameter words frontier, DecidablePred (stop parameter words frontier)]
    (address : OtsPrefix.ChainAddress) (dummy : OtsReferenceWords) (adversary : Adversary) (budget : Nat)
    (hbound : HasHashQueryBound scheme adversary budget) (hsmall : budget < Fintype.card Digest) :
    let law := referenceInstrumentedGame (checkpointObserver stop) (canonicalGraphGameInputs adversary)
      (canonicalEncodingInputs_subset_gameInputs adversary) dummy adversary
    ((1 - (budget : ENNReal) / Fintype.card Digest) * (Fintype.card Digest : ENNReal)) *
      Pr[fun result => result.2.2.ContactAfterStop stop result.1 (referenceFamilyWords result.2.1 dummy) address | law] ≤
      (2 * budget : Nat) * Pr[fun result => stop result.1 (referenceFamilyWords result.2.1 dummy) result.2.2.frontier result.2.2.before | law] := by
  dsimp only
  rw [← prefixInstrumentedObservedGame_original (checkpointObserver stop) _ _ (canonicalGraphInputs_subset_gameInputs adversary) address]
  unfold prefixInstrumentedObservedGame
  apply scaled_probability_bind_le
  intro parameter hparameter
  apply scaled_probability_bind_le
  intro ftsSecret _
  apply scaled_probability_bind_le
  intro selections hselections
  apply scaled_probability_bind_le
  intro other _
  apply scaled_probability_bind_le
  intro auxiliary hauxiliary
  let words := referenceFamilyWords selections dummy
  let segment := OtsPrefix.atAddress parameter words address
  let inputs := canonicalGraphGameInputs adversary
  let hencoding := canonicalEncodingInputs_subset_gameInputs adversary parameter
  let hgraph := canonicalGraphInputs_subset_gameInputs adversary parameter
  have hreal : ∀ result ∈ (PartialChainEndpoint.realRun (fun _ => OtsPrefix.uniformImpl)
      (fun endpoint => segment.seedGame inputs hencoding hgraph auxiliary other.val ftsSecret words endpoint adversary) (fun _ _ => none)).support,
      result.2.1.2.hashCalls ≤ budget :=
    prefixObservedRun_hashCalls_le parameter (probComp_mem_of_evalDist _ parameter hparameter) ftsSecret
      address.1 address.2.1 address.2.2.1 address.2.2.2 dummy adversary selections (pmf_mem_of_evalDist _ selections hselections)
      budget hbound other auxiliary (pmf_mem_of_evalDist _ auxiliary hauxiliary)
  have hseed := checkpointSeed_newContact_le_mark stop parameter words address inputs hencoding hgraph auxiliary other.val ftsSecret adversary budget hreal hsmall
  simpa only [bind_pure_comp, ← PMF.monad_map_eq_map, evalDist_map, probEvent_map, Function.comp_def,
    PMF.evalDist_eq, SPMF.probEvent_liftM, mul_assoc] using hseed

end SphincsSecurity.Concrete
