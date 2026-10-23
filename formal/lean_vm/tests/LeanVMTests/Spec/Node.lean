import LeanVMTests.Spec.NodeVectors

/-!
# The deferring verifier and the node's statement: inhabitants and the conditions doing the work

* `Evaluations.claimed` answers with the claimed value at the claimed point and rejects
  elsewhere, and the deferring verifier's seed is the deployed verifier's.
* The deferring verifier rejects garbage, and so does the deployed one on the same proof.
* `DeferredClaim.Shaped` rejects a bytecode point one coordinate short, which the digest alone
  cannot tell apart (`statementDigest` carries no lengths).
* `batch` on no children is inhabited; `verifyAggregate`'s vector-digest condition rejects a
  digest other than the root's.
* The Rust vectors (`NodeVectors.lean`, written by `node_spec_vectors` in
  `crates/rec_aggregation/src/aggregation/node_vectors.rs`): every encoding of the statement and
  the DA commitment are the deployed ones. The batching of two children's true claims, the matrix
  values and the DA vector digests are slow in the interpreter, so `lake exe node-vectors`
  (`cli/NodeVectors.lean`) checks them compiled.
-/

namespace LeanVMTests.Spec.Node

open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Verifier LeanVM.Protocol.Compile
open LeanVM.Protocol.Blake2sHash LeanVM.Node

/-- A claim on the fixed polynomials. -/
def c : FixedClaims := ⟨[1, 0], 1, 0, 1, [], [], [], 0⟩

example (words : List K) :
    (Evaluations.claimed c).bytecode words c.bytecodePoint = .ret c.bytecodeValue := by
  simp [Evaluations.claimed, Prog.require]; rfl

-- Mutation: at another point the claimed evaluations reject.
example (words : List K) : (Evaluations.claimed c).bytecode words [0, 0] = .fail := by
  simp [Evaluations.claimed, Prog.require, c]; rfl

/-- The deferring verifier's seed is the deployed verifier's, from the deployed IV. -/
example (bytecode : List K) (publicInput : Digest) :
    seed bytecode publicInput =
      blake2sBytes (digestBytes (fiatShamirIv bytecode) ++ digestBytes publicInput) := rfl

/-- A bytecode of 32 words. -/
def bytecode : List K := (List.range 32).map K.ofBits

#guard verifyDeferred bytecode (fiatShamirIv bytecode) default c ⟨[], []⟩ = false
#guard verify bytecode default ⟨[], []⟩ = false

/-- A deferred claim of the bytecode's shape, at zero. -/
def zeroClaim : DeferredClaim :=
  ⟨List.replicate 5 0, 0, List.replicate (2 * blake2sR1csLogSize) 0, 0, 0⟩

example : zeroClaim.Shaped bytecode ∧ zeroClaim.AtZero bytecode := by
  simp [DeferredClaim.Shaped, DeferredClaim.AtZero, zeroClaim, bytecode]; decide

-- Mutation: a bytecode point one coordinate short has the same cells as one whose value moved
-- into the point, and `Shaped` is what rejects it.
example : ¬ ({ zeroClaim with bytecodePoint := List.replicate 4 0 }).Shaped bytecode := by
  simp [DeferredClaim.Shaped, zeroClaim, bytecode]; decide

#guard (batch [] ⟨[], [], 0, 0, 0⟩).isSome

/-- A root. -/
def root : Digest := blake2sBytes []

#guard LeanVM.Da.vectorDigestOf root != LeanVM.Da.toBytes root

/-! ## The Rust vectors -/

#guard r1csDigest == NodeVectors.r1csDigest
#guard xmssListDigest NodeVectors.xmss == NodeVectors.xmssListDigest
#guard sphincsListDigest NodeVectors.sphincs == NodeVectors.sphincsListDigest
#guard signersDigest NodeVectors.xmss NodeVectors.sphincs == NodeVectors.signersDigest

/-- The DA claims: each root with its vector digest. -/
def daClaims : List DaClaim := NodeVectors.daRoots.zip NodeVectors.daVectorDigests

#guard daListDigest daClaims == NodeVectors.daListDigest

/-- The matrix of the first DA root, three rows of the Rust test's `da_symbol`. -/
def daMatrix : List (List K) :=
  (List.range 3).map fun i ↦ (List.range (2 ^ LeanDa.logM)).map fun j ↦
    K.ofBits ((i * 2 ^ LeanDa.logM + j + 1) * 0x9e3779b97f4a7c15)

#guard [LeanDa.commitCodewords LeanVM.Da.blake2s daMatrix] ==
  (NodeVectors.daRoots.take 1).map LeanVM.Da.toBytes

/-- The statement of these claims, deferring the batching's claim. -/
def statement : NodeStatement :=
  ⟨⟨NodeVectors.xmss, NodeVectors.sphincs, daClaims⟩, NodeVectors.batched⟩

#guard statementDigest NodeVectors.seed statement == NodeVectors.statementDigest

end LeanVMTests.Spec.Node
