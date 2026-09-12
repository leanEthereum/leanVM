import SphincsSecurity.Proof.Base.Prelude
import SphincsSecurity.Proof.Hypertree.Extract
import SphincsSecurity.Proof.Ots.OneTime
namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec
set_option backward.isDefEq.respectTransparency false

def frontierOneTimePublicKey (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex)
    (leaf : LeafIndex) (digits : Encoding) (frontier : ChainIndex → Digest) :
    OracleComp HashSpec (ChainIndex → Digest) :=
  sequenceFin fun chainIdx => recoverChain parameter lay tree leaf chainIdx (digits chainIdx) (frontier chainIdx)

def frontierTreeNode (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex)
    (digits : LeafIndex → Encoding) (frontier : LeafIndex → ChainIndex → Digest) :
    Nat → Nat → OracleComp HashSpec Digest
  | 0, nodeIdx => do
      let leaf := leafOfNat nodeIdx
      let endpoints ← frontierOneTimePublicKey parameter lay tree leaf (digits leaf) (frontier leaf)
      leafHash parameter lay tree leaf endpoints
  | level + 1, nodeIdx => do
      let left ← frontierTreeNode parameter lay tree digits frontier level (2 * nodeIdx)
      let right ← frontierTreeNode parameter lay tree digits frontier level (2 * nodeIdx + 1)
      tweakableHash parameter (.node lay tree (level + 1) nodeIdx) (nodePayload left right)

def frontierTreePath (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex)
    (digits : LeafIndex → Encoding) (frontier : LeafIndex → ChainIndex → Digest) (leaf : LeafIndex) :
    OracleComp HashSpec (Fin maxLayerHeight → Digest) :=
  sequenceFin fun level =>
    if level.val < layerHeight lay then
      frontierTreeNode parameter lay tree digits frontier level.val (Nat.xor (leaf.val / 2 ^ level.val) 1)
    else pure 0

def IsOtsFrontier (parameter : PublicParameter) (f : QueryImpl HashSpec Id)
    (lay : Layer) (tree : TreeIndex) (secret : LeafIndex → ChainIndex → Digest)
    (digits : LeafIndex → Encoding) (frontier : LeafIndex → ChainIndex → Digest) : Prop :=
  ∀ leaf chainIdx, evalWithAnswerFn f
    (chainWalk parameter lay tree leaf chainIdx 0 (digits leaf chainIdx).val (secret leaf chainIdx)) =
      frontier leaf chainIdx

theorem eval_frontierOneTimePublicKey (parameter : PublicParameter) (f : QueryImpl HashSpec Id)
    (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex) (secret frontier : ChainIndex → Digest)
    (digits : Encoding)
    (hfrontier : ∀ chainIdx, evalWithAnswerFn f
      (chainWalk parameter lay tree leaf chainIdx 0 (digits chainIdx).val (secret chainIdx)) = frontier chainIdx) :
    evalWithAnswerFn f (frontierOneTimePublicKey parameter lay tree leaf digits frontier) =
      evalWithAnswerFn f (oneTimePublicKey parameter lay tree leaf secret) := by
  simp only [frontierOneTimePublicKey, evalWithAnswerFn_sequenceFin, eval_oneTimePublicKey]
  funext chainIdx
  rw [← hfrontier chainIdx, eval_recoverChain]

theorem eval_frontierTreeNode (parameter : PublicParameter) (f : QueryImpl HashSpec Id)
    (lay : Layer) (tree : TreeIndex) (secret : LeafIndex → ChainIndex → Digest)
    (digits : LeafIndex → Encoding) (frontier : LeafIndex → ChainIndex → Digest)
    (hfrontier : IsOtsFrontier parameter f lay tree secret digits frontier) (level nodeIdx : Nat) :
    evalWithAnswerFn f (frontierTreeNode parameter lay tree digits frontier level nodeIdx) =
      evalWithAnswerFn f (treeNode parameter lay tree secret level nodeIdx) := by
  induction level generalizing nodeIdx with
  | zero =>
      rw [frontierTreeNode, treeNode_zero_eq, evalWithAnswerFn_bind, evalWithAnswerFn_bind,
        eval_frontierOneTimePublicKey _ _ _ _ _ _ _ _ (hfrontier _)]
  | succ level ih =>
      simp only [frontierTreeNode, treeNode_succ_eq, evalWithAnswerFn_bind, ih]

theorem eval_frontierTreePath (parameter : PublicParameter) (f : QueryImpl HashSpec Id)
    (lay : Layer) (tree : TreeIndex) (secret : LeafIndex → ChainIndex → Digest)
    (digits : LeafIndex → Encoding) (frontier : LeafIndex → ChainIndex → Digest)
    (hfrontier : IsOtsFrontier parameter f lay tree secret digits frontier) (leaf : LeafIndex) :
    evalWithAnswerFn f (frontierTreePath parameter lay tree digits frontier leaf) =
      evalWithAnswerFn f (treePath parameter lay tree secret leaf) := by
  simp only [frontierTreePath, treePath, evalWithAnswerFn_sequenceFin]
  funext level
  split_ifs
  · exact eval_frontierTreeNode _ _ _ _ _ _ _ hfrontier _ _
  · rfl

theorem eval_chainWalk_congr_tail (parameter : PublicParameter) (f g : QueryImpl HashSpec Id)
    (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex) (chainIdx : ChainIndex)
    (start steps : Nat) (value : Digest) (hsteps : start + steps ≤ chainLength - 1)
    (hhash : ∀ (step : Fin (chainLength - 1)), start ≤ step.val → ∀ input : Digest,
      truncateHash (f (tweakableHashInput parameter (.chain lay tree leaf chainIdx step) (digestBytes input))) =
        truncateHash (g (tweakableHashInput parameter (.chain lay tree leaf chainIdx step) (digestBytes input)))) :
    evalWithAnswerFn f (chainWalk parameter lay tree leaf chainIdx start steps value) =
      evalWithAnswerFn g (chainWalk parameter lay tree leaf chainIdx start steps value) := by
  induction steps with
  | zero => rfl
  | succ steps ih =>
      have hstep : start + steps < chainLength - 1 := by omega
      simp only [chainWalk, evalWithAnswerFn_bind, dif_pos hstep, eval_tweakableHash]
      rw [ih (by omega)]
      exact hhash ⟨start + steps, hstep⟩ (Nat.le_add_right start steps) _

theorem eval_frontierTreeNode_congr (parameter : PublicParameter) (f g : QueryImpl HashSpec Id)
    (lay : Layer) (tree : TreeIndex) (digits : LeafIndex → Encoding)
    (frontier : LeafIndex → ChainIndex → Digest)
    (hchain : ∀ (leaf : LeafIndex) (chainIdx : ChainIndex) (step : Fin (chainLength - 1)),
      (digits leaf chainIdx).val ≤ step.val → ∀ input : Digest,
      truncateHash (f (tweakableHashInput parameter (.chain lay tree leaf chainIdx step) (digestBytes input))) =
        truncateHash (g (tweakableHashInput parameter (.chain lay tree leaf chainIdx step) (digestBytes input))))
    (hleaf : ∀ (leaf : LeafIndex) (payload : HashInput),
      truncateHash (f (tweakableHashInput parameter (.leaf lay tree leaf) payload)) =
        truncateHash (g (tweakableHashInput parameter (.leaf lay tree leaf) payload)))
    (hnode : ∀ (level nodeIdx : Nat) (payload : HashInput),
      truncateHash (f (tweakableHashInput parameter (.node lay tree level nodeIdx) payload)) =
        truncateHash (g (tweakableHashInput parameter (.node lay tree level nodeIdx) payload)))
    (level nodeIdx : Nat) :
    evalWithAnswerFn f (frontierTreeNode parameter lay tree digits frontier level nodeIdx) =
      evalWithAnswerFn g (frontierTreeNode parameter lay tree digits frontier level nodeIdx) := by
  have hkey : ∀ leaf, evalWithAnswerFn f
      (frontierOneTimePublicKey parameter lay tree leaf (digits leaf) (frontier leaf)) =
        evalWithAnswerFn g (frontierOneTimePublicKey parameter lay tree leaf (digits leaf) (frontier leaf)) := by
    intro leaf
    simp only [frontierOneTimePublicKey, evalWithAnswerFn_sequenceFin]
    funext chainIdx
    apply eval_chainWalk_congr_tail _ _ _ _ _ _ _ _ _ _ _ (hchain leaf chainIdx)
    have hdigit := (digits leaf chainIdx).isLt
    simp only [chainLength, winternitzBits] at hdigit ⊢
    omega
  induction level generalizing nodeIdx with
  | zero =>
      simp only [frontierTreeNode, evalWithAnswerFn_bind, leafHash, eval_tweakableHash]
      rw [hkey]
      exact hleaf _ _
  | succ level ih =>
      simp only [frontierTreeNode, evalWithAnswerFn_bind, eval_tweakableHash, ih]
      exact hnode _ _ _

end SphincsSecurity.Concrete
