/-
  LeanVM.Facts.MerkleLeaf

  A Merkle leaf's digest and an opening's climb, over the deployed Keccak.
-/

module

public import Statement.LeanVmGuestCompleteness

@[expose] public section

namespace LeanVM.Protocol.KeccakHash

open LeanVM.Parameters LeanVM.Protocol.Compile

/-- The digest of a Merkle leaf over Keccak-f[1600]: the statement's `merkleLeafDigestWith`
(`merkleLeafDigest_eq`). -/
def merkleLeafDigest (words : List K) : Digest :=
  keccak256 (words.flatMap K.toBytes)

theorem merkleLeafDigest_eq (words : List K) :
    merkleLeafDigest words =
      Id.run (merkleLeafDigestWith (m := Id) LeanVM.Semantics.keccakF1600 words) :=
  rfl

end LeanVM.Protocol.KeccakHash

namespace LeanVM.Guest.Limits

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Compile

/-- The digest an opening's climb reaches from `node` at `leafPosition` over `path`. -/
def climbTo (node : Digest) (leafPosition : ℕ) (path : List Digest) : Digest :=
  Id.run (climb (m := Id) keccakF1600 node leafPosition path)

end LeanVM.Guest.Limits

end
