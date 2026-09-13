import SphincsSecurity.Proof.Ots.OtsTraceCheckpointBudget
import SphincsSecurity.Proof.Chains.AdaptiveChainCheckpointContact
import SphincsSecurity.Proof.Ots.OtsTraceCheckpointObservation
namespace SphincsSecurity.Concrete.OtsPrefix

open _root_.OracleComp OracleSpec PartialChainEndpoint
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
attribute [local irreducible] canonicalGraphLabels canonicalEncodingInputs canonicalGraphInputs instFintypePosition

variable (segment : OtsPrefix) (stop : FrontierStop)
  [∀ parameter words frontier, DecidablePred (stop parameter words frontier)] (inputs : Finset HashInput)
  (hencoding : canonicalEncodingInputs segment.parameter ⊆ inputs) (hgraph : canonicalGraphInputs segment.parameter ⊆ inputs)
  (auxiliary : segment.ReferenceAuxSeed inputs hencoding hgraph) (secrets : OtsFrontierValues)
  (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (words : OtsReferenceWords) (adversary : Adversary)

theorem traceCheckpointRun_newContact_probability :
    Pr[fun result => (stop segment.parameter words result.2.1.frontier result.2.1.before ∧
        ¬OtsContactTrace.Seen segment result.1 result.2.1.before) ∧
      OtsContactTrace.Seen segment result.1 (result.2.1.before * result.2.1.after) |
      realRun (fun _ => uniformImpl)
        (fun endpoint => segment.instrumentedSeedGame (checkpointObserver stop) inputs hencoding hgraph auxiliary secrets ftsSecret words endpoint adversary)
        (fun _ _ => none)] =
      Pr[fun result => (stop segment.parameter words
          (segment.seedFrontier inputs hencoding hgraph auxiliary secrets words result.1) result.2.1.1.1.1 ∧
          ¬Contact result.2.1.2 result.1) ∧ Contact result.2.2.2 result.1 |
        segment.traceCheckpointRun stop inputs hencoding hgraph auxiliary secrets ftsSecret words adversary] := by
  rw [← segment.traceCheckpointRun_project stop inputs hencoding hgraph auxiliary secrets ftsSecret words adversary,
    ← PMF.monad_map_eq_map, probEvent_map]
  simp only [Function.comp_def, probEvent_eq_tsum_ite, PMF.probOutput_eq_apply]
  apply tsum_congr
  intro result
  by_cases hr : result ∈ (segment.traceCheckpointRun stop inputs hencoding hgraph auxiliary secrets ftsSecret words adversary).support
  · have hs := segment.traceCheckpointRun_observation stop inputs hencoding hgraph auxiliary secrets ftsSecret words adversary result hr
    simp only [hs.1, hs.2.1]
  · have hz : segment.traceCheckpointRun stop inputs hencoding hgraph auxiliary secrets ftsSecret words adversary result = 0 := not_not.mp hr
    simp only [hz, ite_self]

theorem instrumentedCheckpoint_newContact_le (budget : Nat)
    (hreal : ∀ result ∈ (realRun (fun _ => uniformImpl)
      (fun endpoint => segment.seedGame inputs hencoding hgraph auxiliary secrets ftsSecret words endpoint adversary) (fun _ _ => none)).support,
      result.2.1.2.hashCalls ≤ budget)
    (hsmall : budget < Fintype.card Digest) :
    let law := realRun (fun _ => uniformImpl)
      (fun endpoint => segment.instrumentedSeedGame (checkpointObserver stop) inputs hencoding hgraph auxiliary secrets ftsSecret words endpoint adversary)
      (fun _ _ => none)
    (1 - (budget : ENNReal) / Fintype.card Digest) * ((Fintype.card Digest : ENNReal) *
      Pr[fun result => (stop segment.parameter words result.2.1.frontier result.2.1.before ∧ ¬OtsContactTrace.Seen segment result.1 result.2.1.before) ∧
        OtsContactTrace.Seen segment result.1 (result.2.1.before * result.2.1.after) | law]) ≤
    ∑' result, law result *
      (((OtsContactTrace.prefixCalls segment result.2.1.before + 2 * OtsContactTrace.prefixCalls segment result.2.1.after : Nat) : ENNReal) *
        if stop segment.parameter words result.2.1.frontier result.2.1.before ∧ ¬OtsContactTrace.Seen segment result.1 result.2.1.before then 1 else 0) := by
  dsimp only
  let checkpoint := segment.traceCheckpointRun stop inputs hencoding hgraph auxiliary secrets ftsSecret words adversary
  let marked := fun endpoint (middle : ((OtsContactTrace.Trace × OracleComp segment.VisibleWorld (Bool × SigningBoundaryTrace)) × Nat) ×
      (Fin segment.digit.val → Digest → Option Digest)) =>
    stop segment.parameter words (segment.seedFrontier inputs hencoding hgraph auxiliary secrets words endpoint) middle.1.1.1 ∧
      ¬Contact middle.2 endpoint
  have hkernel := realCheckpointRun_contact_charge
    (fun endpoint => extendAux uniformImpl (segment.seedOracle inputs hencoding hgraph auxiliary secrets ftsSecret words endpoint))
    (segment.traceCheckpointBefore stop inputs hencoding hgraph auxiliary secrets ftsSecret words adversary)
    (fun _ middle => QueryPause.traced (segment.visibleObservationTrace auxiliary.high) middle.1.1.2) (fun _ _ => none)
    marked budget (fun _ _ h => h.2)
    (fun endpoint middle hmiddle _ result hresult =>
      (segment.traceCheckpoint_budget stop inputs hencoding hgraph auxiliary secrets ftsSecret words adversary budget hreal hsmall
        endpoint middle hmiddle result hresult).2)
  rw [segment.traceCheckpointRun_newContact_probability stop inputs hencoding hgraph auxiliary secrets ftsSecret words adversary]
  apply hkernel.trans
  rw [← segment.traceCheckpointRun_project stop inputs hencoding hgraph auxiliary secrets ftsSecret words adversary, expectation_map]
  apply ENNReal.tsum_le_tsum
  intro result
  by_cases hr : result ∈ checkpoint.support
  · have hs := segment.traceCheckpointRun_observation stop inputs hencoding hgraph auxiliary secrets ftsSecret words adversary result hr
    apply mul_le_mul' le_rfl
    by_cases hm : marked result.1 result.2.1
    · have hm' : stop segment.parameter words
          (segment.seedFrontier inputs hencoding hgraph auxiliary secrets words result.1) result.2.1.1.1.1 ∧
          ¬OtsContactTrace.Seen segment result.1 result.2.1.1.1.1 := ⟨hm.1, fun hc => hm.2 (hs.1.mp hc)⟩
      simp only [if_pos hm, if_pos hm', mul_one]
      exact_mod_cast (Nat.add_le_add hs.2.2.1 (Nat.mul_le_mul_left 2 hs.2.2.2))
    · have hm' : ¬(stop segment.parameter words
          (segment.seedFrontier inputs hencoding hgraph auxiliary secrets words result.1) result.2.1.1.1.1 ∧
          ¬OtsContactTrace.Seen segment result.1 result.2.1.1.1.1) := by
        intro h
        exact hm ⟨h.1, fun hc => h.2 (hs.1.mpr hc)⟩
      simp only [if_neg hm, if_neg hm', mul_zero, le_refl]
  · have hz : checkpoint result = 0 := not_not.mp hr
    simp only [checkpoint, traceCheckpointRun] at hz
    simp only [hz, zero_mul, zero_le]

theorem instrumentedCheckpoint_newContact_le_mark (budget : Nat)
    (hreal : ∀ result ∈ (realRun (fun _ => uniformImpl)
      (fun endpoint => segment.seedGame inputs hencoding hgraph auxiliary secrets ftsSecret words endpoint adversary) (fun _ _ => none)).support,
      result.2.1.2.hashCalls ≤ budget)
    (hsmall : budget < Fintype.card Digest) :
    let law := realRun (fun _ => uniformImpl)
      (fun endpoint => segment.instrumentedSeedGame (checkpointObserver stop) inputs hencoding hgraph auxiliary secrets ftsSecret words endpoint adversary)
      (fun _ _ => none)
    (1 - (budget : ENNReal) / Fintype.card Digest) * ((Fintype.card Digest : ENNReal) *
      Pr[fun result => (stop segment.parameter words result.2.1.frontier result.2.1.before ∧ ¬OtsContactTrace.Seen segment result.1 result.2.1.before) ∧
        OtsContactTrace.Seen segment result.1 (result.2.1.before * result.2.1.after) | law]) ≤
      (2 * budget : Nat) * Pr[fun result => stop segment.parameter words result.2.1.frontier result.2.1.before | law] := by
  dsimp only
  let aux := fun endpoint => extendAux uniformImpl (segment.seedOracle inputs hencoding hgraph auxiliary secrets ftsSecret words endpoint)
  let before := segment.traceCheckpointBefore stop inputs hencoding hgraph auxiliary secrets ftsSecret words adversary
  let after := fun (_ : Digest) (middle : ((OtsContactTrace.Trace × OracleComp segment.VisibleWorld (Bool × SigningBoundaryTrace)) × Nat) ×
      (Fin segment.digit.val → Digest → Option Digest)) =>
    QueryPause.traced (segment.visibleObservationTrace auxiliary.high) middle.1.1.2
  let marked := fun endpoint (middle : ((OtsContactTrace.Trace × OracleComp segment.VisibleWorld (Bool × SigningBoundaryTrace)) × Nat) ×
      (Fin segment.digit.val → Digest → Option Digest)) =>
    stop segment.parameter words (segment.seedFrontier inputs hencoding hgraph auxiliary secrets words endpoint) middle.1.1.1 ∧
      ¬Contact middle.2 endpoint
  have hkernel := realCheckpointRun_contact_le_mark aux before after (fun _ _ => none) marked budget (fun _ _ h => h.2)
    (fun endpoint middle hmiddle _ result hresult =>
      (segment.traceCheckpoint_budget stop inputs hencoding hgraph auxiliary secrets ftsSecret words adversary budget hreal hsmall
        endpoint middle hmiddle result hresult).2)
    (fun result hresult _ => by
      have hs := realCheckpointRun_support aux before after (fun _ _ => none) result hresult
      exact (segment.traceCheckpoint_budget stop inputs hencoding hgraph auxiliary secrets ftsSecret words adversary budget hreal hsmall
        result.1 result.2.1 hs.1 result.2.2 hs.2).1)
  rw [segment.traceCheckpointRun_newContact_probability stop inputs hencoding hgraph auxiliary secrets ftsSecret words adversary]
  rw [← realCheckpointRun_mark_probability aux before after (fun _ _ => none) marked] at hkernel
  apply hkernel.trans
  apply mul_le_mul' le_rfl
  rw [← segment.traceCheckpointRun_project stop inputs hencoding hgraph auxiliary secrets ftsSecret words adversary,
    ← PMF.monad_map_eq_map, probEvent_map]
  simp only [Function.comp_def, probEvent_eq_tsum_ite, marked]
  apply ENNReal.tsum_le_tsum
  intro result
  by_cases hm : stop segment.parameter words
      (segment.seedFrontier inputs hencoding hgraph auxiliary secrets words result.1) result.2.1.1.1.1
  · simp only [hm, true_and, if_true]
    split
    · exact le_rfl
    · exact bot_le
  · simp only [hm, false_and, if_false, le_refl]

end SphincsSecurity.Concrete.OtsPrefix
