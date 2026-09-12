import SphincsSecurity.Proof.Base.Prelude
import SphincsSecurity.Statement

/-!
# Facts about the statement

`Statement.lean` seals the two tree recursions against accidental unfolding, which also stops Lean from generating their equational theorems. Unsealing them locally makes the equations hold by `rfl`, so this module states them once as ordinary theorems and the rest of the development rewrites with those instead of unfolding anything. It also checks the arithmetic the concrete parameters fix: the layer heights, the index decomposition and the authentication path offsets.
-/

namespace SphincsSecurity.Concrete

theorem _root_.SphincsSecurity.layerHeight_le (lay : Layer) : layerHeight lay ≤ maxLayerHeight := by
  unfold layerHeight maxLayerHeight
  split <;> omega

attribute [local semireducible] treeNode ftsNode verify sign sampleRandomness

noncomputable local instance instSampleableTypeRandomness_1 : SampleableType Randomness :=
  SampleableType.ofFintype Randomness

variable {m : Type → Type} [Monad m] [HasQuery HashSpec m]

@[simp]
theorem treeNode_zero_eq (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex)
    (secret : LeafIndex → ChainIndex → Digest) (nodeIdx : Nat) :
    treeNode (m := m) parameter lay tree secret 0 nodeIdx
      = (do
          let endpoints ← oneTimePublicKey parameter lay tree (leafOfNat nodeIdx)
            (secret (leafOfNat nodeIdx))
          leafHash parameter lay tree (leafOfNat nodeIdx) endpoints) := rfl

theorem treeNode_succ_eq (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex)
    (secret : LeafIndex → ChainIndex → Digest) (level nodeIdx : Nat) :
    treeNode (m := m) parameter lay tree secret (level + 1) nodeIdx
      = (do
          let left ← treeNode parameter lay tree secret level (2 * nodeIdx)
          let right ← treeNode parameter lay tree secret level (2 * nodeIdx + 1)
          tweakableHash parameter (.node lay tree (level + 1) nodeIdx) (nodePayload left right)) := rfl

@[simp]
theorem ftsNode_zero_eq (parameter : PublicParameter) (index : Index) (tree : FtsTree)
    (secret : FtsLeaf → Digest) (nodeIdx : Nat) :
    ftsNode (m := m) parameter index tree secret 0 nodeIdx
      = ftsLeafHash parameter index tree (ftsLeafOfNat nodeIdx) (secret (ftsLeafOfNat nodeIdx)) := rfl

theorem ftsNode_succ_eq (parameter : PublicParameter) (index : Index) (tree : FtsTree)
    (secret : FtsLeaf → Digest) (level nodeIdx : Nat) :
    ftsNode (m := m) parameter index tree secret (level + 1) nodeIdx
      = (do
          let left ← ftsNode parameter index tree secret level (2 * nodeIdx)
          let right ← ftsNode parameter index tree secret level (2 * nodeIdx + 1)
          tweakableHash parameter (.ftsNode index tree (level + 1) nodeIdx)
            (nodePayload left right)) := rfl

@[simp]
theorem treeFold_zero_eq (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex)
    (leaf : LeafIndex) (path : Nat → Digest) (value : Digest) :
    treeFold (m := m) parameter lay tree leaf path 0 value = pure value := rfl

theorem treeFold_succ_eq (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex)
    (leaf : LeafIndex) (path : Nat → Digest) (levels : Nat) (value : Digest) :
    treeFold (m := m) parameter lay tree leaf path (levels + 1) value
      = (do
          let current ← treeFold parameter lay tree leaf path levels value
          if leaf.val.testBit levels then
            tweakableHash parameter (.node lay tree (levels + 1) (leaf.val / 2 ^ (levels + 1)))
              (nodePayload (path levels) current)
          else
            tweakableHash parameter (.node lay tree (levels + 1) (leaf.val / 2 ^ (levels + 1)))
              (nodePayload current (path levels))) := rfl

@[simp]
theorem ftsFold_zero_eq (parameter : PublicParameter) (index : Index) (tree : FtsTree)
    (leaf : FtsLeaf) (path : Fin ftsTreeHeight → Digest) (value : Digest) :
    ftsFold (m := m) parameter index tree leaf path 0 value = pure value := rfl

theorem ftsFold_succ_eq (parameter : PublicParameter) (index : Index) (tree : FtsTree)
    (leaf : FtsLeaf) (path : Fin ftsTreeHeight → Digest) (levels : Nat) (value : Digest) :
    ftsFold (m := m) parameter index tree leaf path (levels + 1) value
      = (do
          let current ← ftsFold parameter index tree leaf path levels value
          let sibling := if hlevel : levels < ftsTreeHeight then path ⟨levels, hlevel⟩ else 0
          if leaf.val.testBit levels then
            tweakableHash parameter (.ftsNode index tree (levels + 1) (leaf.val / 2 ^ (levels + 1)))
              (nodePayload sibling current)
          else
            tweakableHash parameter (.ftsNode index tree (levels + 1) (leaf.val / 2 ^ (levels + 1)))
              (nodePayload current sibling)) := rfl

@[simp]
theorem verifyLayers_zero_eq (parameter : PublicParameter) (index : Index) (signature : Signature)
    (message : Digest) :
    verifyLayers (m := m) parameter index signature 0 message = pure (some message) := rfl

theorem verifyLayers_succ_eq (parameter : PublicParameter) (index : Index) (signature : Signature)
    (remaining : Nat) (message : Digest) :
    verifyLayers (m := m) parameter index signature (remaining + 1) message
      = (if hlayer : remaining < numLayers then
          (do
            match ← otsLeaf parameter ⟨remaining, hlayer⟩ (treeIndexAt index ⟨remaining, hlayer⟩)
                (leafIndexAt index ⟨remaining, hlayer⟩) message
                (signature.counter ⟨remaining, hlayer⟩)
                (signature.chainValue ⟨remaining, hlayer⟩) with
            | none => pure none
            | some value => do
                let root ← treeFold parameter ⟨remaining, hlayer⟩
                  (treeIndexAt index ⟨remaining, hlayer⟩) (leafIndexAt index ⟨remaining, hlayer⟩)
                  (signaturePath signature ⟨remaining, hlayer⟩) (layerHeight ⟨remaining, hlayer⟩)
                  value
                verifyLayers parameter index signature remaining root)
        else pure none) := rfl

theorem verify_eq (publicKey : PublicKey) (message : Message) (signature : Signature) :
    verify (m := m) publicKey message signature
      = (do
          let digest ← messageDigest publicKey.parameter publicKey.root message signature.randomness
          if ¬ Admissible digest then
            return false
          else
            let ftsPublicKey ← ftsRecover publicKey.parameter (digestIndex digest)
              (digestLeaves digest) signature.ftsSecret signature.ftsPath
            match ← verifyLayers publicKey.parameter (digestIndex digest) signature numLayers
                ftsPublicKey with
            | none => return false
            | some root => return decide (root = publicKey.root)) := rfl

theorem sign_eq (secretKey : SecretKey) (message : Message) :
    sign secretKey message
      = (do
          match ← signDigestLoop digestAttemptLimit secretKey message with
          | none => return none
          | some (randomness, index, leaves) => do
              let ftsPath ← liftM
                (ftsOpen secretKey.parameter index leaves (secretKey.ftsSecret index) :
                  OracleComp HashSpec (FtsTree → Fin ftsTreeHeight → Digest))
              let layers ← liftM
                (sequenceLayers (fun lay => signLayer secretKey index lay) :
                  OracleComp HashSpec
                    (Option (Layer → Counter × (ChainIndex → Digest) × (Fin maxLayerHeight → Digest))))
              match layers with
              | none => return none
              | some parts => do
                  let _ ← liftM
                    (treeRoot secretKey.parameter topLayer rootTree (secretKey.otsSecret topLayer rootTree) :
                      OracleComp HashSpec Digest)
                  return some
                    { randomness := randomness
                      ftsSecret := fun tree =>
                        secretKey.ftsSecret index tree (leaves (ftsIndexOf tree))
                      ftsPath := ftsPath
                      counter := fun lay => (parts lay).1
                      chainValue := fun lay => (parts lay).2.1
                      authPath := flattenPaths fun lay => (parts lay).2.2 }) := rfl

theorem sampleRandomness_eq :
    sampleRandomness = ($ᵗ Randomness : ProbComp Randomness) := rfl

example : ∀ failure : Fin 4,
    let result := (sequenceLayers (m := WriterT (List Nat) Id) fun lay =>
      WriterT.mk (pure (if lay.val = failure.val then none else some lay.val, [lay.val]))).run
    (result.2, result.1.map List.ofFn) =
      ![([2, 1, 0], none), ([2, 1], none), ([2], none), ([2, 1, 0], some [0, 1, 2])] failure := by
  decide

/-! ## Parameter arithmetic -/

example : ∑ lay : Layer, layerHeight lay = totalHeight := by decide

example : (layerHeight topLayer, layerHeight middleLayer, layerHeight bottomLayer) = (12, 7, 7) := by
  decide

example : (heightAbove topLayer, heightAbove middleLayer, heightAbove bottomLayer) = (0, 12, 19) := by
  decide

example : (heightBelow topLayer, heightBelow middleLayer, heightBelow bottomLayer) = (14, 7, 0) := by
  decide

/-- The digest is `h + k * a = 176` bits and has to fit in one oracle output. -/
example : messageDigestBits = 176 ∧ messageDigestBits ≤ hashOutputBits := by decide

theorem treeIndexAt_val (index : Index) (lay : Layer) :
    (treeIndexAt index lay).val = index.val / 2 ^ (totalHeight - heightAbove lay) := rfl

theorem leafIndexAt_val (index : Index) (lay : Layer) :
    (leafIndexAt index lay).val = index.val / 2 ^ heightBelow lay % 2 ^ layerHeight lay := rfl

/-- Layer `0` holds a single tree, the public key's. -/
theorem treeIndexAt_topLayer (index : Index) : (treeIndexAt index topLayer).val = 0 := by
  have hlt : index.val < 2 ^ 26 := index.isLt
  have h0 : totalHeight - heightAbove topLayer = 26 := by decide
  simp only [treeIndexAt_val, h0]
  omega

/-- The layers link: the tree used on a layer is the one whose root sits at leaf `e_(lay-1)` of the
tree used on the layer above. -/
theorem layers_link_top (index : Index) :
    (treeIndexAt index middleLayer).val
      = (treeIndexAt index topLayer).val * 2 ^ layerHeight topLayer
        + (leafIndexAt index topLayer).val := by
  have hlt : index.val < 2 ^ 26 := index.isLt
  have h0 : totalHeight - heightAbove topLayer = 26 := by decide
  have h1 : totalHeight - heightAbove middleLayer = 14 := by decide
  have hb : heightBelow topLayer = 14 := by decide
  have hh : layerHeight topLayer = 12 := by decide
  simp only [treeIndexAt_val, leafIndexAt_val, h0, h1, hb, hh]
  omega

theorem layers_link_middle (index : Index) :
    (treeIndexAt index bottomLayer).val
      = (treeIndexAt index middleLayer).val * 2 ^ layerHeight middleLayer
        + (leafIndexAt index middleLayer).val := by
  have h1 : totalHeight - heightAbove middleLayer = 14 := by decide
  have h2 : totalHeight - heightAbove bottomLayer = 7 := by decide
  have hb : heightBelow middleLayer = 7 := by decide
  have hh : layerHeight middleLayer = 7 := by decide
  simp only [treeIndexAt_val, leafIndexAt_val, h1, h2, hb, hh]
  omega

/-- The bottom layer's leaves are the `2^h` indices themselves. -/
theorem leafIndexAt_bottomLayer (index : Index) :
    (leafIndexAt index bottomLayer).val = index.val % 2 ^ layerHeight bottomLayer := by
  have hb : heightBelow bottomLayer = 0 := by decide
  simp [leafIndexAt_val, hb]

/-- An entry at a layer's own offset belongs to that layer. -/
theorem layerOfPath_eq (lay : Layer) (level : Fin maxLayerHeight) (hlevel : level.val < layerHeight lay) :
    layerOfPath (heightAbove lay + level.val) = lay := by
  revert hlevel
  revert level
  revert lay
  decide

theorem flattenPaths_apply (paths : Layer → Fin maxLayerHeight → Digest) (lay : Layer)
    (level : Fin maxLayerHeight) (hlevel : level.val < layerHeight lay) (position : PathIndex)
    (hposition : position.val = heightAbove lay + level.val) :
    flattenPaths paths position = paths lay level := by
  simp only [flattenPaths, hposition, layerOfPath_eq lay level hlevel, Nat.add_sub_cancel_left,
    dif_pos level.isLt, Fin.eta]

/-- Every one of the `h` entries is read by some layer: the offsets partition `0..h-1` into the `d` layers, so the path carries no entry verification skips and none twice. This is arithmetic about the offsets, not a statement about `verifyLayers`. -/
theorem authPath_exhausted (position : PathIndex) : ∃ lay : Layer, ∃ level : Fin maxLayerHeight,
    level.val < layerHeight lay ∧ heightAbove lay + level.val = position.val := by
  revert position
  decide

end SphincsSecurity.Concrete
