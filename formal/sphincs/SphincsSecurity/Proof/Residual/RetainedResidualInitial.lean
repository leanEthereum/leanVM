import SphincsSecurity.Proof.Base.Prelude
import SphincsSecurity.Proof.Residual.RetainedResidualBudget
namespace SphincsSecurity.Concrete.RetainedResidual

open _root_.OracleComp OracleSpec CanonicalProbeRouting UniformTableCompletion
open AdaptiveResidualLabels hiding World State Environment
attribute [local instance] Classical.propDecidable
attribute [local irreducible] hashInputs sourceInputs canonicalEncodingInputs canonicalGraphInputs instFintypePosition
set_option backward.isDefEq.respectTransparency false

noncomputable def initialMemory (words : OtsReferenceWords) (exposedValues : InitialPublicLabels words) : Memory :=
  ⟨⟨fun _ => none, 1212415, 0⟩, ⟨fun _ _ _ => False, initialKnown words exposedValues⟩, [], [], []⟩

noncomputable def initialState (inputs : Finset HashInput) (words : OtsReferenceWords)
    (exposedValues : InitialPublicLabels words) : State inputs :=
  ⟨initialAllowed words exposedValues, fun _ => none, initialMemory words exposedValues⟩

noncomputable def initialContext (parameter : PublicParameter) (inputs : Finset HashInput)
    (hencoding : canonicalEncodingInputs parameter ⊆ inputs) (auxiliary : ReferenceAuxiliary inputs)
    (hauxiliary : auxiliary ∈ (referenceAuxiliarySample inputs).support) (dummy : OtsReferenceWords)
    (exposedValues : InitialPublicLabels (referenceFamilyWords auxiliary.selections dummy))
    (high : CanonicalGraphHighHalves) (labels : Labels) : Context inputs where
  key := ⟨parameter, knownRoot (initialKnown (referenceFamilyWords auxiliary.selections dummy) exposedValues),
    coordinateOtsSecrets labels, coordinateFtsSecrets labels⟩
  graph := coordinateGraphLabels labels high
  auxiliary := auxiliary
  encoding := hencoding
  auxiliary_valid := hauxiliary
  dummy := dummy
  publicReplies := coordinateGraphLabels (initialKnown (referenceFamilyWords auxiliary.selections dummy) exposedValues) high

theorem initialState_rowsCovered (inputs : Finset HashInput) (words : OtsReferenceWords)
    (exposedValues : InitialPublicLabels words) : ResidualByteFrontend.RowsCovered inputs (project (initialState inputs words exposedValues)) := by
  intro input answer hanswer
  cases hanswer

theorem Context.keygen_record {inputs : Finset HashInput} (context : Context inputs)
    (hroot : context.key.root = canonicalGraphRoot context.graph) :
    fixedBoundaryRun context.key.parameter context.oracle
      (liftM (treeRoot context.key.parameter topLayer rootTree (context.key.otsSecret topLayer rootTree) : OracleComp HashSpec Digest)) =
        pure (context.key.root, (FreeMonoid.of none) ^ 1212415) := by
  have hcomputed : context.key.root = evalWithAnswerFn context.oracle
      (treeRoot context.key.parameter topLayer rootTree (context.key.otsSecret topLayer rootTree)) := by
    rw [hroot, ← canonicalGraphLabels_root context.key.parameter context.key.otsSecret context.key.ftsSecret context.oracle]
    congr 1
    exact (canonicalGraphLabels_programmedHash context.key.parameter context.key.otsSecret context.key.ftsSecret context.graph _).symm
  rw [fixedBoundaryRun_lift_hash]
  have htree : boundaryEval context.key.parameter context.oracle
      (treeRoot context.key.parameter topLayer rootTree (context.key.otsSecret topLayer rootTree)) =
      (evalWithAnswerFn context.oracle (treeRoot context.key.parameter topLayer rootTree (context.key.otsSecret topLayer rootTree)),
        (FreeMonoid.of none) ^ 1212415) :=
    boundaryEval_treeNode context.key.parameter context.oracle topLayer rootTree (context.key.otsSecret topLayer rootTree) _ _
  rw [htree, ← hcomputed]

theorem Context.rest_queryBound {inputs : Finset HashInput} (context : Context inputs)
    (hroot : context.key.root = canonicalGraphRoot context.graph)
    (hparameter : context.key.parameter ∈ support sampleParameter) (adversary : Adversary) (q : Nat)
    (hq : HasHashQueryBound scheme adversary q) :
    1212415 ≤ q ∧ FixedHashQueryBound context.oracle
      (gameRest scheme adversary ⟨context.key.root, context.key.parameter⟩ context.key) (q - 1212415) := by
  have hots : context.key.otsSecret ∈ support sampleOtsSecrets := by
    unfold sampleOtsSecrets
    exact otsSecretsSampleableType.mem_support_selectElem _
  have hfts : context.key.ftsSecret ∈ support sampleFtsSecrets := by
    unfold sampleFtsSecrets
    exact ftsSecretsSampleableType.mem_support_selectElem _
  have hbound := hashQueryBound_fixed context.oracle _ q
    (hashQueryBound_gameAfterSecrets adversary q hq hparameter hots hfts)
  rw [gameAfterSecrets] at hbound
  have hresult : 𝒟[fixedBoundaryRun context.key.parameter context.oracle
      (liftM (treeRoot context.key.parameter topLayer rootTree (context.key.otsSecret topLayer rootTree) : OracleComp HashSpec Digest))]
        (context.key.root, (FreeMonoid.of none) ^ 1212415) ≠ 0 := by
    rw [context.keygen_record hroot, evalDist_pure, SPMF.pure_apply_self]
    exact one_ne_zero
  have h := fixedBoundaryRun_bind_query_bound context.key.parameter context.oracle _ _ q hbound _ hresult
  have hkey : (⟨context.key.parameter, context.key.root, context.key.otsSecret, context.key.ftsSecret⟩ : SecretKey) = context.key := by
    cases context.key
    rfl
  simp only [SigningBoundaryTrace.hashCalls_pow_none, hkey] at h
  exact h

end SphincsSecurity.Concrete.RetainedResidual
