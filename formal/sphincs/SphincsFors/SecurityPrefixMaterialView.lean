import SphincsFors.SecurityPrefixMaterialSampling

/-! Public agreement of two answer functions: they agree on every tweakable hash input and on the
FORS secret derivations. Then every reconstructed public computation (chains, encodings, FORS
nodes, keys and openings, digests, tree nodes and paths, layer signatures and the final assembly)
evaluates identically under both. -/

open OracleComp OracleSpec

namespace SphincsFors.Security.Prefix
open Concrete Completeness SeedModel

attribute [local irreducible] encodingAttemptLimit digestAttemptLimit Seeded.ftsNode
  Seeded.treeNode Seeded.spineNode chainWalk
set_option backward.isDefEq.respectTransparency false

structure PublicAgreement (parameter : PublicParameter) (seed : MasterSeed)
    (left right : QueryImpl HashSpec Id) : Prop where
  hash : ∀ domain payload, left (tweakableHashInput parameter domain payload) =
    right (tweakableHashInput parameter domain payload)
  fors : ∀ index tree leaf,
    evalWithAnswerFn left (deriveKey parameter (.fts index tree leaf) seed : OracleComp HashSpec Digest) =
    evalWithAnswerFn right (deriveKey parameter (.fts index tree leaf) seed : OracleComp HashSpec Digest)

namespace PublicAgreement

variable {parameter : PublicParameter} {seed : MasterSeed} {left right : QueryImpl HashSpec Id}
    (h : PublicAgreement parameter seed left right)

include h

theorem tweakable (domain : HashDomain) (payload : HashInput) :
    evalWithAnswerFn left (tweakableHash parameter domain payload : OracleComp HashSpec Digest) =
      evalWithAnswerFn right (tweakableHash parameter domain payload : OracleComp HashSpec Digest) := by
  simp only [eval_tweakableHash, h.hash]

theorem chain (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex) (index : ChainIndex)
    (start steps : Nat) (value : Digest) :
    evalWithAnswerFn left (chainWalk parameter lay tree leaf index start steps value : OracleComp HashSpec Digest) =
      evalWithAnswerFn right (chainWalk parameter lay tree leaf index start steps value : OracleComp HashSpec Digest) := by
  induction steps with
  | zero => simp only [chainWalk, evalWithAnswerFn_pure]
  | succ steps ih =>
      simp only [chainWalk, evalWithAnswerFn_bind, ih]
      split
      · exact h.tweakable _ _
      · rfl

theorem encoding (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex) (message : Digest) (counter : Counter) :
    evalWithAnswerFn left (encode parameter lay tree leaf message counter : OracleComp HashSpec (Option Encoding)) =
      evalWithAnswerFn right (encode parameter lay tree leaf message counter : OracleComp HashSpec (Option Encoding)) := by
  simp only [encode, evalWithAnswerFn_bind, h.tweakable, evalWithAnswerFn_pure]

theorem firstEncoding_eq (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex)
    (message : Digest) (attempts start : Nat) :
    firstEncoding left parameter lay tree leaf message attempts start =
      firstEncoding right parameter lay tree leaf message attempts start := by
  induction attempts generalizing start with
  | zero => rfl
  | succ attempts ih => simp only [firstEncoding, h.encoding, ih]

theorem forsNode (index : Index) (tree : FtsTree) (level nodeIdx : Nat) :
    evalWithAnswerFn left (Seeded.ftsNode parameter index tree seed level nodeIdx : OracleComp HashSpec Digest) =
      evalWithAnswerFn right (Seeded.ftsNode parameter index tree seed level nodeIdx : OracleComp HashSpec Digest) := by
  induction level generalizing nodeIdx with
  | zero => simp only [Seeded.ftsNode, evalWithAnswerFn_bind, h.fors, ftsLeafHash, h.tweakable]
  | succ level ih =>
      have hleft := ftsNodeValue_succ left parameter index tree seed level nodeIdx
      have hright := ftsNodeValue_succ right parameter index tree seed level nodeIdx
      simp only [ftsNodeValue] at hleft hright
      rw [hleft, hright, ih, ih, h.hash]

theorem forsKey (index : Index) :
    evalWithAnswerFn left (Seeded.ftsKey parameter index seed : OracleComp HashSpec Digest) =
      evalWithAnswerFn right (Seeded.ftsKey parameter index seed : OracleComp HashSpec Digest) := by
  simp only [Seeded.ftsKey, evalWithAnswerFn_bind, evalWithAnswerFn_pure, eval_sequenceFin,
    h.forsNode, h.tweakable]

theorem forsOpen (index : Index) (leaves : IndexGroup → FtsLeaf) :
    evalWithAnswerFn left (Seeded.ftsOpen parameter index leaves seed :
      OracleComp HashSpec (FtsTree → Fin ftsTreeHeight → Digest)) =
    evalWithAnswerFn right (Seeded.ftsOpen parameter index leaves seed :
      OracleComp HashSpec (FtsTree → Fin ftsTreeHeight → Digest)) := by
  simp only [Seeded.ftsOpen, eval_sequenceFin, h.forsNode]

theorem digestCall (root : Digest) (message : Message) (randomness : Randomness) (call : Fin 2) :
    evalWithAnswerFn left (messageDigestCall parameter root message randomness call : OracleComp HashSpec HashOutput) =
      evalWithAnswerFn right (messageDigestCall parameter root message randomness call : OracleComp HashSpec HashOutput) :=
  h.hash (.message call) (messageDigestPayload root message randomness)

theorem digest (root : Digest) (message : Message) (randomness : Randomness) :
    evalWithAnswerFn left (messageDigest parameter root message randomness : OracleComp HashSpec MessageDigest) =
      evalWithAnswerFn right (messageDigest parameter root message randomness : OracleComp HashSpec MessageDigest) := by
  simp only [messageDigest, evalWithAnswerFn_bind, h.digestCall, evalWithAnswerFn_pure]

variable (segment : Segment) (hparameter : parameter = segment.parameter)

include hparameter

theorem endpoints (secrets : Secrets) (frontier : Digest) (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex) :
    publicEndpoints segment left secrets frontier lay tree leaf =
      publicEndpoints segment right secrets frontier lay tree leaf := by
  subst parameter
  funext index
  simp only [publicEndpoints, recoverChain]
  split <;> exact h.chain _ _ _ _ _ _ _

theorem node (secrets : Secrets) (frontier : Digest) (lay : Layer) (tree : TreeIndex) (level index : Nat) :
    publicNode segment left secrets frontier lay tree level index =
      publicNode segment right secrets frontier lay tree level index := by
  subst parameter
  induction level generalizing index with
  | zero => simp only [publicNode, h.endpoints segment rfl, leafHash, h.tweakable]
  | succ level ih => simp only [publicNode, ih, h.tweakable]

theorem values (secrets : Secrets) (frontier : Digest) (lay : Layer) (tree : TreeIndex)
    (leaf : LeafIndex) (word : Encoding) :
    publicValues segment left secrets frontier lay tree leaf word =
      publicValues segment right secrets frontier lay tree leaf word := by
  subst parameter
  funext index
  simp only [publicValues]
  split <;> exact h.chain _ _ _ _ _ _ _

variable [Params]

theorem path (secrets : Secrets) (frontier : Digest) (surrogates : Nat → Digest)
    (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex) :
    publicPath segment left secrets frontier surrogates lay tree leaf =
      publicPath segment right secrets frontier surrogates lay tree leaf := by
  funext level
  simp only [publicPath, h.node segment hparameter]

theorem layer (secrets : Secrets) (frontier : Digest) (surrogates : Nat → Digest)
    (index : Index) (lay : Layer) (message : Digest) :
    publicLayer segment left secrets frontier surrogates index lay message =
      publicLayer segment right secrets frontier surrogates index lay message := by
  subst parameter
  simp only [publicLayer, h.firstEncoding_eq, h.values segment rfl, h.path segment rfl]

theorem finishSign (secrets : Secrets) (frontier : Digest) (surrogates : Nat → Digest)
    (root : Digest) (message : Message) (randomness : Randomness) :
    publicFinishSign segment left secrets frontier surrogates seed root message randomness =
      publicFinishSign segment right secrets frontier surrogates seed root message randomness := by
  subst parameter
  simp only [publicFinishSign, h.digest, h.fors, h.forsOpen, h.forsKey, h.layer segment rfl]

omit [Params] in
theorem cutoff : ReferenceCutoff segment left seed ↔ ReferenceCutoff segment right seed := by
  subst parameter
  simp only [ReferenceCutoff, h.forsKey, h.firstEncoding_eq]

end PublicAgreement

end SphincsFors.Security.Prefix
