import SphincsFors.SecurityPrefixExecution

/-! The public one-time keys, tree nodes and authentication paths reconstructed from one selected
chain frontier, and the secrets derived from the seed. The reconstructed functions never read the
selected coordinate of the secret table; their oracle is the outside oracle. -/

open OracleComp OracleSpec

namespace SphincsFors.Security.Prefix
open Concrete

attribute [local instance] Classical.propDecidable
attribute [local irreducible] Seeded.treeNode

def derivedSecrets (f : QueryImpl HashSpec Id) (parameter : PublicParameter) (seed : MasterSeed) : Secrets :=
  fun (lay, tree, leaf, chain) =>
    evalWithAnswerFn f (deriveKey parameter (.ots lay tree leaf chain) seed : OracleComp HashSpec Digest)

noncomputable def publicEndpoints (segment : Segment) (outside : QueryImpl HashSpec Id)
    (secrets : Secrets) (frontier : Digest) (lay : Layer) (tree : TreeIndex)
    (leaf : LeafIndex) : ChainIndex → Digest := fun chain =>
  if (lay, tree, leaf, chain) = address segment then
    evalWithAnswerFn outside (recoverChain segment.parameter lay tree leaf chain segment.digit frontier)
  else
    evalWithAnswerFn outside (chainWalk segment.parameter lay tree leaf chain 0 (chainLength - 1)
      (secrets (lay, tree, leaf, chain)) : OracleComp HashSpec Digest)

noncomputable def publicNode (segment : Segment) (outside : QueryImpl HashSpec Id)
    (secrets : Secrets) (frontier : Digest) (lay : Layer) (tree : TreeIndex) : Nat → Nat → Digest
  | 0, nodeIdx => evalWithAnswerFn outside (leafHash segment.parameter lay tree (leafOfNat nodeIdx)
      (publicEndpoints segment outside secrets frontier lay tree (leafOfNat nodeIdx)))
  | level + 1, nodeIdx => evalWithAnswerFn outside
      (tweakableHash segment.parameter (.node lay tree (level + 1) nodeIdx)
        (nodePayload (publicNode segment outside secrets frontier lay tree level (2 * nodeIdx))
          (publicNode segment outside secrets frontier lay tree level (2 * nodeIdx + 1))) :
        OracleComp HashSpec Digest)

variable [Params]

noncomputable def publicPath (segment : Segment) (outside : QueryImpl HashSpec Id)
    (secrets : Secrets) (frontier : Digest) (surrogates : Nat → Digest)
    (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex) : Fin (layerHeight lay) → Digest :=
  fun level => if level.val < subtreeHeight then
    publicNode segment outside secrets frontier lay tree level.val (Nat.xor (leaf.val / 2 ^ level.val) 1)
  else surrogates level.val

end SphincsFors.Security.Prefix
