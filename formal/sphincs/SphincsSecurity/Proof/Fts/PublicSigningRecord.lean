import SphincsSecurity.Proof.Base.Prelude
import SphincsSecurity.Proof.Hypertree.FrontierSigningOracleCongruence
import SphincsSecurity.Proof.Hypertree.PublicGraphSigner
import SphincsSecurity.Proof.Residual.RetainedObservation
namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec CanonicalProbeRouting
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] instFintypePosition boundaryEval publicDigestLoop

abbrev PublicSigningRecord := (Option PublicSigningPlan × Option FewTimeView) × SigningBoundaryTrace

def completePublicSigningRecord (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (record : PublicSigningRecord) : (Option Signature × Option FewTimeView) × SigningBoundaryTrace :=
  match record.1.2 with
  | none => ((none, none), record.2)
  | some view => ((record.1.1.map (fun plan => plan.finish (fun tree => ftsSecret view.1 tree (view.2 tree))), some view), record.2)

noncomputable def publicSigningRecord (parameter : PublicParameter) (root : Digest) (outside : QueryImpl HashSpec Id)
    (known : Labels) (words : OtsReferenceWords) (selections : ReferenceFamily) (message : Message) :
    ProbComp PublicSigningRecord := do
  let selected ← fixedBoundaryRun parameter outside (publicDigestLoop parameter root message digestAttemptLimit)
  match selected.1 with
  | none => pure ((none, none), selected.2)
  | some (randomness, index, leaves) =>
      let plan := publicSignPlan known words selections randomness index leaves
      pure ((plan.1, some (selectedFewTimeView index leaves)), selected.2 * (FreeMonoid.of none) ^ plan.2)

theorem boundaryEval_publicSignAttempt_eq_of_message (parameter : PublicParameter) (root : Digest) (message : Message)
    (f g : QueryImpl HashSpec Id) (randomness : Randomness)
    (hmessage : f (tweakableHashInput parameter .message (messageDigestPayload root message randomness)) =
      g (tweakableHashInput parameter .message (messageDigestPayload root message randomness))) :
    boundaryEval parameter f (publicSignAttempt parameter root message randomness) =
      boundaryEval parameter g (publicSignAttempt parameter root message randomness) := by
  simp [publicSignAttempt, messageDigest, oracleHash, boundaryEval, QueryImpl.withTrace_apply, hmessage]

theorem fixedBoundaryRun_publicDigestLoop_eq_of_message (parameter : PublicParameter) (root : Digest) (message : Message)
    (f g : QueryImpl HashSpec Id)
    (hmessage : ∀ randomness, f (tweakableHashInput parameter .message (messageDigestPayload root message randomness)) =
      g (tweakableHashInput parameter .message (messageDigestPayload root message randomness))) (attempts : Nat) :
    fixedBoundaryRun parameter f (publicDigestLoop parameter root message attempts) =
      fixedBoundaryRun parameter g (publicDigestLoop parameter root message attempts) := by
  induction attempts with
  | zero => simp only [publicDigestLoop, fixedBoundaryRun_pure]
  | succ attempts ih =>
      rw [publicDigestLoop]
      apply fixedBoundaryRun_bind_congr
      · exact fixedBoundaryRun_lift_prob_eq parameter f g sampleRandomness
      · intro randomness
        apply fixedBoundaryRun_bind_congr
        · rw [fixedBoundaryRun_lift_hash, fixedBoundaryRun_lift_hash,
            boundaryEval_publicSignAttempt_eq_of_message parameter root message f g randomness (hmessage randomness)]
        · intro attempt
          cases attempt with
          | none => exact ih
          | some selected => rfl

theorem frontierSigningRecord_eq_public (key : SecretKey) (root : Digest) (f g : QueryImpl HashSpec Id)
    (words : OtsReferenceWords) (disclosed : Index → FtsTree → FtsLeaf → Prop) (known : Labels)
    (hagrees : PublicAgreement words disclosed known
      (CanonicalCoordinate.value key.otsSecret key.ftsSecret (canonicalGraphLabels key.parameter key.otsSecret key.ftsSecret f)))
    (message : Message)
    (hmessage : ∀ randomness, f (tweakableHashInput key.parameter .message (messageDigestPayload root message randomness)) =
      g (tweakableHashInput key.parameter .message (messageDigestPayload root message randomness))) :
    frontierSigningRecord key.parameter root f key.ftsSecret words
        (canonicalGraphFrontier key.otsSecret (canonicalGraphLabels key.parameter key.otsSecret key.ftsSecret f) words) message =
      completePublicSigningRecord key.ftsSecret <$>
        publicSigningRecord key.parameter root g known words (referenceTableSelection key f) message := by
  rw [frontierSigningRecord, publicSigningRecord, map_bind,
    fixedBoundaryRun_publicDigestLoop_eq_of_message key.parameter root message f g hmessage]
  apply bind_congr
  rintro ⟨selected, trace⟩
  cases selected with
  | none => rfl
  | some selected =>
      obtain ⟨randomness, index, leaves⟩ := selected
      dsimp only
      rw [map_pure, frontierSignAfterDigest_eq_publicPlan key f words disclosed known hagrees]
      rfl

theorem completePublicSigningRecord_trace (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (record : PublicSigningRecord) :
    (completePublicSigningRecord ftsSecret record).2 = record.2 := by
  cases hview : record.1.2 <;> simp only [completePublicSigningRecord, hview]

end SphincsSecurity.Concrete
