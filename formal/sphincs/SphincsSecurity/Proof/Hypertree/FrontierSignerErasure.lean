import SphincsSecurity.Proof.Base.Prelude
import SphincsSecurity.Proof.Hypertree.FrontierSigningEvaluation
import SphincsSecurity.Proof.Hypertree.FrontierTreeEvaluation
namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] boundaryEval sequenceFin chainWalk referenceEncodingSearch signLayer

abbrev OtsReferenceWords := Layer → TreeIndex → LeafIndex → Encoding
abbrev OtsFrontierValues := Layer → TreeIndex → LeafIndex → ChainIndex → Digest

def IsSigningFrontier (key : SecretKey) (f : QueryImpl HashSpec Id)
    (words : OtsReferenceWords) (frontier : OtsFrontierValues) : Prop :=
  ∀ lay tree, IsOtsFrontier key.parameter f lay tree (key.otsSecret lay tree) (words lay tree) (frontier lay tree)

def frontierLayerMessage (parameter : PublicParameter) (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (words : OtsReferenceWords) (frontier : OtsFrontierValues) (index : Index) (lay : Layer) :
    OracleComp HashSpec Digest :=
  if hbelow : lay.val + 1 < numLayers then
    let below : Layer := ⟨lay.val + 1, hbelow⟩
    frontierTreeNode parameter below (treeIndexAt index below)
      (words below (treeIndexAt index below)) (frontier below (treeIndexAt index below)) (layerHeight below) 0
  else ftsKey parameter index (ftsSecret index)

def frontierLayerSearch (parameter : PublicParameter) (f : QueryImpl HashSpec Id)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (words : OtsReferenceWords)
    (frontier : OtsFrontierValues) (index : Index) (lay : Layer) : Option (Counter × Encoding) × Nat :=
  referenceEncodingSearch parameter f lay (treeIndexAt index lay) (leafIndexAt index lay)
    (evalWithAnswerFn f (frontierLayerMessage parameter ftsSecret words frontier index lay)) encodingAttemptLimit 0

def FrontierReferenceWord (parameter : PublicParameter) (f : QueryImpl HashSpec Id)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (words : OtsReferenceWords)
    (frontier : OtsFrontierValues) (index : Index) (lay : Layer) : Prop :=
  ∀ counter word, (frontierLayerSearch parameter f ftsSecret words frontier index lay).1 = some (counter, word) →
    word = words lay (treeIndexAt index lay) (leafIndexAt index lay)

def frontierSignLayer (parameter : PublicParameter) (f : QueryImpl HashSpec Id)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (words : OtsReferenceWords)
    (frontier : OtsFrontierValues) (index : Index) (lay : Layer) : Option LayerPart × Nat :=
  let search := frontierLayerSearch parameter f ftsSecret words frontier index lay
  let cost := layerMessageHashCost lay + search.2
  match search.1 with
  | none => (none, cost)
  | some (counter, _) =>
      (some (counter, frontier lay (treeIndexAt index lay) (leafIndexAt index lay),
        evalWithAnswerFn f (frontierTreePath parameter lay (treeIndexAt index lay)
          (words lay (treeIndexAt index lay)) (frontier lay (treeIndexAt index lay)) (leafIndexAt index lay))),
        cost + 191 + authenticationHashCost lay)

theorem eval_frontierLayerMessage (key : SecretKey) (f : QueryImpl HashSpec Id)
    (words : OtsReferenceWords) (frontier : OtsFrontierValues)
    (hfrontier : IsSigningFrontier key f words frontier) (index : Index) (lay : Layer) :
    evalWithAnswerFn f (frontierLayerMessage key.parameter key.ftsSecret words frontier index lay) =
      evalWithAnswerFn f (layerMessage key index lay) := by
  unfold frontierLayerMessage layerMessage
  split_ifs
  · rw [treeRoot]
    exact eval_frontierTreeNode _ _ _ _ _ _ _ (hfrontier _ _) _ _
  · rfl

theorem boundaryEval_signLayer_frontier (key : SecretKey) (f : QueryImpl HashSpec Id)
    (words : OtsReferenceWords) (frontier : OtsFrontierValues)
    (hfrontier : IsSigningFrontier key f words frontier) (index : Index) (lay : Layer)
    (hword : FrontierReferenceWord key.parameter f key.ftsSecret words frontier index lay) :
    boundaryEval key.parameter f (signLayer key index lay) =
      ((frontierSignLayer key.parameter f key.ftsSecret words frontier index lay).1,
        (FreeMonoid.of none) ^ (frontierSignLayer key.parameter f key.ftsSecret words frontier index lay).2) := by
  let search := frontierLayerSearch key.parameter f key.ftsSecret words frontier index lay
  let values := frontier lay (treeIndexAt index lay) (leafIndexAt index lay)
  let message := evalWithAnswerFn f (frontierLayerMessage key.parameter key.ftsSecret words frontier index lay)
  have hm : evalWithAnswerFn f (layerMessage key index lay) = message :=
    (eval_frontierLayerMessage key f words frontier hfrontier index lay).symm
  have hots : boundaryEval key.parameter f
      (otsSign key.parameter lay (treeIndexAt index lay) (leafIndexAt index lay)
        (key.otsSecret lay (treeIndexAt index lay) (leafIndexAt index lay)) message) =
      (search.1.map (fun selected => (selected.1, values)),
        (FreeMonoid.of none) ^ (search.2 + if search.1.isSome then 191 else 0)) := by
    apply boundaryEval_otsSignFrom_frontier
    intro counter word hw chainIdx
    rw [hword counter word hw]
    exact hfrontier _ _ _ _
  have hotsValue := congrArg Prod.fst hots
  rw [boundaryEval_fst] at hotsValue
  have hpath := (eval_frontierTreePath key.parameter f lay (treeIndexAt index lay)
    (key.otsSecret lay (treeIndexAt index lay)) (words lay (treeIndexAt index lay))
    (frontier lay (treeIndexAt index lay)) (hfrontier _ _) (leafIndexAt index lay)).symm
  simp only [signLayer, boundaryEval_bind, boundaryEval_layerMessage, hm, hots, hotsValue]
  change _ = ((match search.1 with
    | none => (none, layerMessageHashCost lay + search.2)
    | some (counter, _) => (some (counter, values,
        evalWithAnswerFn f (frontierTreePath key.parameter lay (treeIndexAt index lay)
          (words lay (treeIndexAt index lay)) (frontier lay (treeIndexAt index lay)) (leafIndexAt index lay))),
        layerMessageHashCost lay + search.2 + 191 + authenticationHashCost lay)).1,
      (FreeMonoid.of none) ^ (frontierSignLayer key.parameter f key.ftsSecret words frontier index lay).2)
  cases hs : search.1 with
  | none =>
      change (frontierLayerSearch key.parameter f key.ftsSecret words frontier index lay).1 = none at hs
      simp only [Option.map_none, Option.isSome_none, Bool.false_eq_true, ↓reduceIte, Nat.add_zero,
        boundaryEval_pure, frontierSignLayer, search, hs, mul_one, pow_add]
  | some selected =>
      obtain ⟨counter, word⟩ := selected
      change (frontierLayerSearch key.parameter f key.ftsSecret words frontier index lay).1 = some (counter, word) at hs
      simp only [Option.map_some, Option.isSome_some, ↓reduceIte, boundaryEval_bind,
        boundaryEval_treePath, boundaryEval_pure, hpath, mul_one, frontierSignLayer,
        search, hs, pow_add, mul_assoc]

def frontierSignAfterDigest (parameter : PublicParameter) (f : QueryImpl HashSpec Id)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (words : OtsReferenceWords)
    (frontier : OtsFrontierValues) (randomness : Randomness) (index : Index) (leaves : IndexGroup → FtsLeaf) :
    Option Signature × Nat :=
  let layers := fun lay => frontierSignLayer parameter f ftsSecret words frontier index lay
  let paths := evalWithAnswerFn f (ftsOpen parameter index leaves (ftsSecret index))
  ((sequenceFin (m := Option) (fun lay => (layers lay).1)).map (fun parts =>
      { randomness := randomness
        ftsSecret := fun tree => ftsSecret index tree (leaves (ftsIndexOf tree))
        ftsPath := paths
        counter := fun lay => (parts lay).1
        chainValue := fun lay => (parts lay).2.1
        authPath := flattenPaths fun lay => (parts lay).2.2 }),
    28504 + sequenceLayersHashCost layers +
      if (sequenceFin (m := Option) (fun lay => (layers lay).1)).isSome then 1212415 else 0)

theorem boundaryEval_signAfterDigest_frontier (key : SecretKey) (f : QueryImpl HashSpec Id)
    (words : OtsReferenceWords) (frontier : OtsFrontierValues)
    (hfrontier : IsSigningFrontier key f words frontier) (randomness : Randomness) (index : Index)
    (leaves : IndexGroup → FtsLeaf)
    (hwords : ∀ lay, FrontierReferenceWord key.parameter f key.ftsSecret words frontier index lay) :
    boundaryEval key.parameter f (signAfterDigest key randomness index leaves) =
      ((frontierSignAfterDigest key.parameter f key.ftsSecret words frontier randomness index leaves).1,
        (FreeMonoid.of none) ^
          (frontierSignAfterDigest key.parameter f key.ftsSecret words frontier randomness index leaves).2) := by
  have hparts : (fun lay => evalWithAnswerFn f (signLayer key index lay)) =
      (fun lay => (frontierSignLayer key.parameter f key.ftsSecret words frontier index lay).1) := by
    funext lay
    rw [← boundaryEval_fst key.parameter f]
    exact congrArg Prod.fst (boundaryEval_signLayer_frontier key f words frontier hfrontier index lay (hwords lay))
  have hlayers := boundaryEval_sequenceLayers key.parameter f (fun lay => signLayer key index lay)
    (fun lay => frontierSignLayer key.parameter f key.ftsSecret words frontier index lay)
    (fun lay => boundaryEval_signLayer_frontier key f words frontier hfrontier index lay (hwords lay))
  have hlayersValue : evalWithAnswerFn f (sequenceLayers (fun lay => signLayer key index lay)) =
      sequenceFin (m := Option) (fun lay => (frontierSignLayer key.parameter f key.ftsSecret words frontier index lay).1) := by
    rw [evalWithAnswerFn_sequenceLayers, hparts]
  simp only [signAfterDigest, frontierSignAfterDigest, boundaryEval_bind, boundaryEval_ftsOpen,
    hlayers, hlayersValue]
  cases hc : sequenceFin (m := Option) (fun lay =>
      (frontierSignLayer key.parameter f key.ftsSecret words frontier index lay).1) with
  | none => simp only [boundaryEval_pure, Option.map_none, Option.isSome_none, Bool.false_eq_true,
      ↓reduceIte, Nat.add_zero, mul_one, pow_add]
  | some parts =>
      simp only [boundaryEval_bind, treeRoot, boundaryEval_treeNode, boundaryEval_pure,
        Option.map_some, Option.isSome_some, ↓reduceIte, mul_one, pow_add,
        show 296 * 2 ^ layerHeight topLayer - 1 = 1212415 from rfl, mul_assoc]

end SphincsSecurity.Concrete
