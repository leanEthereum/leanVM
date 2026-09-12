import SphincsSecurity.Proof.Base.Prelude
import SphincsSecurity.Proof.Hypertree.FrontierSignerErasure
namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec
attribute [local instance] Classical.propDecidable
attribute [local irreducible] referenceEncodingSearch chainWalk boundaryEval
set_option backward.isDefEq.respectTransparency false

noncomputable def referenceIndex (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex) : Index :=
  if h : ∃ index, treeIndexAt index lay = tree ∧ leafIndexAt index lay = leaf then Classical.choose h else 0

theorem referenceIndex_position (index : Index) (lay : Layer) :
    treeIndexAt (referenceIndex lay (treeIndexAt index lay) (leafIndexAt index lay)) lay = treeIndexAt index lay ∧
      leafIndexAt (referenceIndex lay (treeIndexAt index lay) (leafIndexAt index lay)) lay = leafIndexAt index lay := by
  have h : ∃ source, treeIndexAt source lay = treeIndexAt index lay ∧
      leafIndexAt source lay = leafIndexAt index lay := ⟨index, rfl, rfl⟩
  rw [referenceIndex, dif_pos h]
  exact Classical.choose_spec h

theorem layerMessage_referenceIndex (key : SecretKey) (index : Index) (lay : Layer) :
    layerMessage (m := OracleComp HashSpec) key
        (referenceIndex lay (treeIndexAt index lay) (leafIndexAt index lay)) lay =
      layerMessage key index lay :=
  layerMessage_eq_of_position_eq key _ index lay (referenceIndex_position index lay).1
    (referenceIndex_position index lay).2

noncomputable def canonicalEncodingSearch (key : SecretKey) (f : QueryImpl HashSpec Id)
    (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex) : Option (Counter × Encoding) × Nat :=
  referenceEncodingSearch key.parameter f lay tree leaf
    (evalWithAnswerFn f (layerMessage key (referenceIndex lay tree leaf) lay)) encodingAttemptLimit 0

theorem canonicalEncodingSearch_at (key : SecretKey) (f : QueryImpl HashSpec Id) (index : Index) (lay : Layer) :
    canonicalEncodingSearch key f lay (treeIndexAt index lay) (leafIndexAt index lay) =
      referenceEncodingSearch key.parameter f lay (treeIndexAt index lay) (leafIndexAt index lay)
        (evalWithAnswerFn f (layerMessage key index lay)) encodingAttemptLimit 0 := by
  rw [canonicalEncodingSearch, layerMessage_referenceIndex]

noncomputable def canonicalReferenceWords (key : SecretKey) (f : QueryImpl HashSpec Id)
    (dummy : OtsReferenceWords) : OtsReferenceWords :=
  fun lay tree leaf => ((canonicalEncodingSearch key f lay tree leaf).1.map Prod.snd).getD (dummy lay tree leaf)

noncomputable def canonicalFrontierValues (key : SecretKey) (f : QueryImpl HashSpec Id)
    (words : OtsReferenceWords) : OtsFrontierValues :=
  fun lay tree leaf chainIdx => evalWithAnswerFn f
    (chainWalk key.parameter lay tree leaf chainIdx 0 (words lay tree leaf chainIdx).val
      (key.otsSecret lay tree leaf chainIdx))

theorem isSigningFrontier_canonical (key : SecretKey) (f : QueryImpl HashSpec Id) (words : OtsReferenceWords) :
    IsSigningFrontier key f words (canonicalFrontierValues key f words) := fun _ _ _ _ => rfl

theorem frontierReferenceWord_canonical (key : SecretKey) (f : QueryImpl HashSpec Id)
    (dummy : OtsReferenceWords) (index : Index) (lay : Layer) :
    FrontierReferenceWord key.parameter f key.ftsSecret (canonicalReferenceWords key f dummy)
      (canonicalFrontierValues key f (canonicalReferenceWords key f dummy)) index lay := by
  intro counter word hword
  rw [frontierLayerSearch, eval_frontierLayerMessage key f _ _ (isSigningFrontier_canonical key f _) index lay,
    ← canonicalEncodingSearch_at] at hword
  simp only [canonicalReferenceWords, hword, Option.map_some, Option.getD_some]

theorem referenceEncodingSearch_valid (parameter : PublicParameter) (f : QueryImpl HashSpec Id)
    (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex) (message : Digest)
    (attempts start : Nat) (counter : Counter) (word : Encoding)
    (hword : (referenceEncodingSearch parameter f lay tree leaf message attempts start).1 = some (counter, word)) :
    TargetSum.Valid word := by
  induction attempts generalizing start with
  | zero => simp [referenceEncodingSearch] at hword
  | succ attempts ih =>
      cases hencode : evalWithAnswerFn f
          (encode parameter lay tree leaf message (BitVec.ofNat counterBits start)) with
      | none =>
          apply ih (start + 1)
          simpa only [referenceEncodingSearch, hencode] using hword
      | some selected =>
          simp only [referenceEncodingSearch, hencode, Option.some.injEq, Prod.mk.injEq] at hword
          apply TargetSum.valid_of_decodeDigest_eq_some
          simpa only [encode, evalWithAnswerFn_bind, evalWithAnswerFn_pure, hword.2] using hencode

theorem canonicalReferenceWords_valid (key : SecretKey) (f : QueryImpl HashSpec Id)
    (dummy : OtsReferenceWords) (hdummy : ∀ lay tree leaf, TargetSum.Valid (dummy lay tree leaf)) :
    ∀ lay tree leaf, TargetSum.Valid (canonicalReferenceWords key f dummy lay tree leaf) := by
  intro lay tree leaf
  cases hsearch : (canonicalEncodingSearch key f lay tree leaf).1 with
  | none => simpa only [canonicalReferenceWords, hsearch, Option.map_none, Option.getD_none] using hdummy lay tree leaf
  | some selected =>
      obtain ⟨counter, word⟩ := selected
      simp only [canonicalReferenceWords, hsearch, Option.map_some, Option.getD_some]
      exact referenceEncodingSearch_valid _ _ _ _ _ _ _ _ _ _ hsearch

theorem boundaryEval_signAfterDigest_canonical (key : SecretKey) (f : QueryImpl HashSpec Id)
    (dummy : OtsReferenceWords) (randomness : Randomness) (index : Index) (leaves : IndexGroup → FtsLeaf) :
    let words := canonicalReferenceWords key f dummy
    let frontier := canonicalFrontierValues key f words
    let projected := frontierSignAfterDigest key.parameter f key.ftsSecret words frontier randomness index leaves
    boundaryEval key.parameter f (signAfterDigest key randomness index leaves) =
      (projected.1, (FreeMonoid.of none) ^ projected.2) :=
  boundaryEval_signAfterDigest_frontier key f _ _ (isSigningFrontier_canonical key f _) randomness index leaves
    (frontierReferenceWord_canonical key f dummy index)

end SphincsSecurity.Concrete
