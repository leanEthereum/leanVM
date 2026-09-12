import SphincsSecurity.Proof.Base.Prelude
import SphincsSecurity.Proof.Hypertree.FrontierSigningOracleCongruence
namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] boundaryEval

noncomputable def causalFrontierAdversaryImpl (parameter : PublicParameter) (root : Digest)
    (external : QueryImpl HashSpec Id) (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (words : OtsReferenceWords) (frontier : OtsFrontierValues) :
    QueryImpl (OracleWorld + SigningSpec) (WriterT SigningBoundaryTrace ProbComp)
  | .inl input => (fixedHashWorld external).withTrace (signingBoundaryTrace parameter) input
  | .inr message => WriterT.mk
      (frontierSigningRun parameter root (maskOtsPrefixes parameter words external) ftsSecret words frontier message)

theorem causalFrontierAdversaryImpl_eq (parameter : PublicParameter) (root : Digest)
    (f : QueryImpl HashSpec Id) (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (words : OtsReferenceWords) (frontier : OtsFrontierValues) :
    causalFrontierAdversaryImpl parameter root f ftsSecret words frontier =
      frontierAdversaryImpl parameter root f ftsSecret words frontier := by
  funext input
  cases input with
  | inl input => rfl
  | inr message =>
      change (WriterT.mk
        (frontierSigningRun parameter root (maskOtsPrefixes parameter words f) ftsSecret words frontier message) :
          WriterT SigningBoundaryTrace ProbComp (Option Signature)) =
        WriterT.mk (frontierSigningRun parameter root f ftsSecret words frontier message)
      rw [← frontierSigningRun_eq_of_agree parameter words f (maskOtsPrefixes parameter words f)
        (maskOtsPrefixes_agrees parameter words f)]

noncomputable def causalFrontierAdversaryRun {α : Type} (parameter : PublicParameter) (root : Digest)
    (external : QueryImpl HashSpec Id) (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (words : OtsReferenceWords) (frontier : OtsFrontierValues)
    (computation : OracleComp (OracleWorld + SigningSpec) α) :
    ProbComp ((α × QueryLog SigningSpec) × SigningBoundaryTrace) :=
  ((simulateQ ((causalFrontierAdversaryImpl parameter root external ftsSecret words frontier).withTraceAppend signingLogFragment)
    computation).run).run

theorem causalFrontierAdversaryRun_eq {α : Type} (parameter : PublicParameter) (root : Digest)
    (f : QueryImpl HashSpec Id) (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (words : OtsReferenceWords) (frontier : OtsFrontierValues)
    (computation : OracleComp (OracleWorld + SigningSpec) α) :
    causalFrontierAdversaryRun parameter root f ftsSecret words frontier computation =
      frontierAdversaryRun parameter root f ftsSecret words frontier computation := by
  rw [causalFrontierAdversaryRun, frontierAdversaryRun, causalFrontierAdversaryImpl_eq]

noncomputable def causalFrontierGameRest (parameter : PublicParameter) (root : Digest)
    (external : QueryImpl HashSpec Id) (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (words : OtsReferenceWords) (frontier : OtsFrontierValues) (adversary : Adversary) :
    ProbComp (Bool × SigningBoundaryTrace) := do
  let result ← causalFrontierAdversaryRun parameter root external ftsSecret words frontier
    (adversary.main ⟨root, parameter⟩)
  let checked := boundaryEval parameter external (verify ⟨root, parameter⟩ result.1.1.message result.1.1.signature)
  pure (decide (SigningTranscript.Valid result.1.2 ∧ ¬SigningTranscript.Contains result.1.2 result.1.1) && checked.1,
    result.2 * checked.2)

theorem causalFrontierGameRest_eq (parameter : PublicParameter) (root : Digest)
    (f : QueryImpl HashSpec Id) (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (words : OtsReferenceWords) (frontier : OtsFrontierValues) (adversary : Adversary) :
    causalFrontierGameRest parameter root f ftsSecret words frontier adversary =
      frontierGameRest parameter root f ftsSecret words frontier adversary := by
  rw [causalFrontierGameRest, frontierGameRest, causalFrontierAdversaryRun_eq]

noncomputable def causalFrontierGame (parameter : PublicParameter) (external : QueryImpl HashSpec Id)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (words : OtsReferenceWords)
    (frontier : OtsFrontierValues) (adversary : Adversary) : ProbComp (Bool × SigningBoundaryTrace) :=
  (fun result => (result.1, (FreeMonoid.of none) ^ 1212415 * result.2)) <$>
    causalFrontierGameRest parameter (frontierRoot parameter (maskOtsPrefixes parameter words external) words frontier)
      external ftsSecret words frontier adversary

theorem causalFrontierGame_eq (parameter : PublicParameter) (f : QueryImpl HashSpec Id)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (words : OtsReferenceWords)
    (frontier : OtsFrontierValues) (adversary : Adversary) :
    causalFrontierGame parameter f ftsSecret words frontier adversary =
      frontierGame parameter f ftsSecret words frontier adversary := by
  rw [causalFrontierGame, frontierGame, causalFrontierGameRest_eq,
    ← frontierRoot_eq_of_agree parameter words f (maskOtsPrefixes parameter words f)
      (maskOtsPrefixes_agrees parameter words f)]

end SphincsSecurity.Concrete
