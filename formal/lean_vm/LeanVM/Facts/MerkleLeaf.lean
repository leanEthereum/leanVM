/-
  LeanVM.Facts.MerkleLeaf

  A Merkle leaf's digest and an opening's climb, over the deployed Keccak.
-/

module

public import Statement.LeanVmGuestCompleteness

@[expose] public section

namespace LeanVM.Protocol.KeccakHash

open LeanVM.Parameters LeanVM.Protocol.Compile

/-- The digest of a Merkle leaf over Keccak-f[1600] (`merkleLeafDigestWith`). -/
def merkleLeafDigest (words : List K) : Digest :=
  keccak256 (words.flatMap K.toBytes)

end LeanVM.Protocol.KeccakHash

namespace LeanVM.Guest.Limits

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Compile

/-- The digest an opening's climb reaches from `node` at `leafPosition` over `path`. -/
def climbTo (node : Digest) (leafPosition : ℕ) (path : List Digest) : Digest :=
  Id.run (climb (m := Id) keccakF1600 node leafPosition path)

end LeanVM.Guest.Limits

end
