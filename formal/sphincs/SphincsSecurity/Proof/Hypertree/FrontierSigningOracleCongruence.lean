import SphincsSecurity.Proof.Base.Prelude
import SphincsSecurity.Proof.Hypertree.FrontierOracleCongruence
namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] boundaryEval publicDigestLoop

theorem fixedBoundaryRun_bind_congr {α β : Type} (parameter : PublicParameter)
    (f g : QueryImpl HashSpec Id) (first : OracleComp OracleWorld α) (next : α → OracleComp OracleWorld β)
    (hfirst : fixedBoundaryRun parameter f first = fixedBoundaryRun parameter g first)
    (hnext : ∀ value, fixedBoundaryRun parameter f (next value) = fixedBoundaryRun parameter g (next value)) :
    fixedBoundaryRun parameter f (first >>= next) = fixedBoundaryRun parameter g (first >>= next) := by
  simp only [fixedBoundaryRun_bind, hfirst, hnext]

theorem fixedBoundaryRun_lift_prob_eq {α : Type} (parameter : PublicParameter)
    (f g : QueryImpl HashSpec Id) (computation : ProbComp α) :
    fixedBoundaryRun parameter f (liftM computation) = fixedBoundaryRun parameter g (liftM computation) := by
  induction computation using OracleComp.inductionOn with
  | pure value => simp only [liftM_pure, fixedBoundaryRun_pure]
  | query_bind input next ih =>
      rw [liftM_bind]
      apply fixedBoundaryRun_bind_congr
      · change (simulateQ ((fixedHashWorld f).withTrace (signingBoundaryTrace parameter))
            (liftM (OracleWorld.query (.inl input)))).run =
          (simulateQ ((fixedHashWorld g).withTrace (signingBoundaryTrace parameter))
            (liftM (OracleWorld.query (.inl input)))).run
        rw [simulateQ_spec_query, simulateQ_spec_query]
        rfl
      · exact ih

variable (parameter : PublicParameter) (words : OtsReferenceWords)
  (f g : QueryImpl HashSpec Id) (h : AgreeOutsideOtsPrefixes parameter words f g)

include h

theorem boundaryEval_publicSignAttempt_eq_of_agree (root : Digest) (message : Message) (randomness : Randomness) :
    boundaryEval parameter f (publicSignAttempt parameter root message randomness) =
      boundaryEval parameter g (publicSignAttempt parameter root message randomness) := by
  have hinput := h.other .message (by decide) (messageDigestPayload root message randomness)
  simp [publicSignAttempt, messageDigest, oracleHash, boundaryEval, QueryImpl.withTrace_apply, hinput]

theorem fixedBoundaryRun_publicDigestLoop_eq_of_agree (root : Digest) (message : Message) (attempts : Nat) :
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
            boundaryEval_publicSignAttempt_eq_of_agree parameter words f g h]
        · intro attempt
          cases attempt with
          | none => exact ih
          | some selected => rfl

theorem frontierSigningRecord_eq_of_agree (root : Digest) (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (frontier : OtsFrontierValues) (message : Message) :
    frontierSigningRecord parameter root f ftsSecret words frontier message =
      frontierSigningRecord parameter root g ftsSecret words frontier message := by
  simp only [frontierSigningRecord, fixedBoundaryRun_publicDigestLoop_eq_of_agree parameter words f g h,
    frontierSignAfterDigest_eq_of_agree parameter words f g h]

theorem frontierSigningRun_eq_of_agree (root : Digest) (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (frontier : OtsFrontierValues) (message : Message) :
    frontierSigningRun parameter root f ftsSecret words frontier message =
      frontierSigningRun parameter root g ftsSecret words frontier message := by
  rw [frontierSigningRun, frontierSigningRun, frontierSigningRecord_eq_of_agree parameter words f g h]

end SphincsSecurity.Concrete
