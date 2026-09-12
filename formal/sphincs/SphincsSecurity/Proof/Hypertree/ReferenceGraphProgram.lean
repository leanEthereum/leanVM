import SphincsSecurity.Proof.Hypertree.PublicGraphSigner
import SphincsSecurity.Proof.Ots.ReferenceEncodingProgram
namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec CanonicalProbeRouting
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] canonicalGraphInputs canonicalEncodingInputs frontierSigningRun frontierRoot boundaryEval publicDigestLoop

theorem publicDigestLoop_eq_of_message (parameter : PublicParameter) (f g : QueryImpl HashSpec Id)
    (hmessage : ∀ root message randomness,
      f (tweakableHashInput parameter .message (messageDigestPayload root message randomness)) =
        g (tweakableHashInput parameter .message (messageDigestPayload root message randomness)))
    (root : Digest) (message : Message) (attempts : Nat) :
    fixedBoundaryRun parameter f (publicDigestLoop parameter root message attempts) =
      fixedBoundaryRun parameter g (publicDigestLoop parameter root message attempts) := by
  have hattempt (randomness : Randomness) :
      boundaryEval parameter f (publicSignAttempt parameter root message randomness) =
        boundaryEval parameter g (publicSignAttempt parameter root message randomness) := by
    simp [publicSignAttempt, messageDigest, oracleHash, boundaryEval, QueryImpl.withTrace_apply, hmessage]
  induction attempts with
  | zero => simp only [publicDigestLoop, fixedBoundaryRun_pure]
  | succ attempts ih =>
      rw [publicDigestLoop]
      apply fixedBoundaryRun_bind_congr
      · exact fixedBoundaryRun_lift_prob_eq parameter f g sampleRandomness
      · intro randomness
        apply fixedBoundaryRun_bind_congr
        · rw [fixedBoundaryRun_lift_hash, fixedBoundaryRun_lift_hash, hattempt]
        · intro attempt
          cases attempt with
          | none => exact ih
          | some selected => rfl

theorem frontierSignAfterDigest_eq_of_graph (key : SecretKey) (f g : QueryImpl HashSpec Id)
    (labels : CanonicalGraphLabels) (words : OtsReferenceWords)
    (hf : canonicalGraphLabels key.parameter key.otsSecret key.ftsSecret f = labels)
    (hg : canonicalGraphLabels key.parameter key.otsSecret key.ftsSecret g = labels)
    (hselected : referenceTableSelection key f = referenceTableSelection key g)
    (randomness : Randomness) (index : Index) (leaves : IndexGroup → FtsLeaf) :
    frontierSignAfterDigest key.parameter f key.ftsSecret words (canonicalGraphFrontier key.otsSecret labels words)
        randomness index leaves =
      frontierSignAfterDigest key.parameter g key.ftsSecret words (canonicalGraphFrontier key.otsSecret labels words)
        randomness index leaves := by
  let known := CanonicalCoordinate.value key.otsSecret key.ftsSecret labels
  have haf : PublicAgreement words (fun _ _ _ => False) known
      (CanonicalCoordinate.value key.otsSecret key.ftsSecret (canonicalGraphLabels key.parameter key.otsSecret key.ftsSecret f)) := by
    rw [hf]
    intro coordinate _
    rfl
  have hag : PublicAgreement words (fun _ _ _ => False) known
      (CanonicalCoordinate.value key.otsSecret key.ftsSecret (canonicalGraphLabels key.parameter key.otsSecret key.ftsSecret g)) := by
    rw [hg]
    intro coordinate _
    rfl
  have hleft := frontierSignAfterDigest_eq_publicPlan key f words _ known haf randomness index leaves
  have hright := frontierSignAfterDigest_eq_publicPlan key g words _ known hag randomness index leaves
  rw [hf, hselected] at hleft
  rw [hg] at hright
  exact hleft.trans hright.symm

theorem frontierRoot_of_graph (key : SecretKey) (f : QueryImpl HashSpec Id) (labels : CanonicalGraphLabels)
    (words : OtsReferenceWords) (hlabels : canonicalGraphLabels key.parameter key.otsSecret key.ftsSecret f = labels) :
    frontierRoot key.parameter f words (canonicalGraphFrontier key.otsSecret labels words) = canonicalGraphRoot labels := by
  have hfrontier : IsSigningFrontier key f words (canonicalGraphFrontier key.otsSecret labels words) := by
    rw [← hlabels, canonicalGraphLabels_frontier key.parameter key.otsSecret key.ftsSecret f words key.root]
    exact isSigningFrontier_canonical key f words
  rw [frontierRoot_eq key f words _ hfrontier, ← canonicalGraphLabels_root key.parameter key.otsSecret key.ftsSecret f, hlabels]

theorem frontierSigningRun_eq_of_graph (key : SecretKey) (f g : QueryImpl HashSpec Id)
    (labels : CanonicalGraphLabels) (words : OtsReferenceWords)
    (hf : canonicalGraphLabels key.parameter key.otsSecret key.ftsSecret f = labels)
    (hg : canonicalGraphLabels key.parameter key.otsSecret key.ftsSecret g = labels)
    (hselected : referenceTableSelection key f = referenceTableSelection key g)
    (hmessage : ∀ root message randomness,
      f (tweakableHashInput key.parameter .message (messageDigestPayload root message randomness)) =
        g (tweakableHashInput key.parameter .message (messageDigestPayload root message randomness)))
    (root : Digest) (message : Message) :
    frontierSigningRun key.parameter root f key.ftsSecret words (canonicalGraphFrontier key.otsSecret labels words) message =
      frontierSigningRun key.parameter root g key.ftsSecret words (canonicalGraphFrontier key.otsSecret labels words) message := by
  simp only [frontierSigningRun, frontierSigningRecord, publicDigestLoop_eq_of_message key.parameter f g hmessage,
    frontierSignAfterDigest_eq_of_graph key f g labels words hf hg hselected]

theorem CausalFrontierProgram.game_eq_of_graph (key : SecretKey) (f g : QueryImpl HashSpec Id)
    (labels : CanonicalGraphLabels) (words : OtsReferenceWords)
    (hf : canonicalGraphLabels key.parameter key.otsSecret key.ftsSecret f = labels)
    (hg : canonicalGraphLabels key.parameter key.otsSecret key.ftsSecret g = labels)
    (hselected : referenceTableSelection key f = referenceTableSelection key g)
    (hmessage : ∀ root message randomness,
      f (tweakableHashInput key.parameter .message (messageDigestPayload root message randomness)) =
        g (tweakableHashInput key.parameter .message (messageDigestPayload root message randomness)))
    (adversary : Adversary) :
    CausalFrontierProgram.game key.parameter f key.ftsSecret words (canonicalGraphFrontier key.otsSecret labels words) adversary =
      CausalFrontierProgram.game key.parameter g key.ftsSecret words (canonicalGraphFrontier key.otsSecret labels words) adversary := by
  let frontier := canonicalGraphFrontier key.otsSecret labels words
  have hsign (root : Digest) (message : Message) :
      frontierSigningRun key.parameter root (maskOtsPrefixes key.parameter words f) key.ftsSecret words frontier message =
        frontierSigningRun key.parameter root (maskOtsPrefixes key.parameter words g) key.ftsSecret words frontier message := by
    rw [← frontierSigningRun_eq_of_agree key.parameter words f _ (maskOtsPrefixes_agrees key.parameter words f),
      ← frontierSigningRun_eq_of_agree key.parameter words g _ (maskOtsPrefixes_agrees key.parameter words g)]
    exact frontierSigningRun_eq_of_graph key f g labels words hf hg hselected hmessage root message
  have himpl (root : Digest) : CausalFrontierProgram.adversaryImpl key.parameter root f key.ftsSecret words frontier =
      CausalFrontierProgram.adversaryImpl key.parameter root g key.ftsSecret words frontier := by
    funext input
    cases input with
    | inl input => rfl
    | inr message => simp only [CausalFrontierProgram.adversaryImpl_signing, hsign]
  dsimp only [frontier] at himpl
  rw [CausalFrontierProgram.game, CausalFrontierProgram.game,
    ← frontierRoot_eq_of_agree key.parameter words f _ (maskOtsPrefixes_agrees key.parameter words f),
    ← frontierRoot_eq_of_agree key.parameter words g _ (maskOtsPrefixes_agrees key.parameter words g),
    frontierRoot_of_graph key f labels words hf, frontierRoot_of_graph key g labels words hg]
  simp only [CausalFrontierProgram.gameRest, CausalFrontierProgram.adversaryRun, himpl]

end SphincsSecurity.Concrete
