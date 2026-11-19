/-
  LeanVM.Guest.B1.Common.HashPair

  Two-to-one hashing of two-cell digests, as the guest's `keccak(l, r, out)` computes it.
-/

module

public import LeanVM.Guest.Value.KeccakLayout

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.KeccakHash

@[expose] public section

/-- A node's two cells hash its children's: the node's cells are the digest of their 64 bytes. -/
def HashesPair (l0 l1 r0 r1 p0 p1 : E) : Prop :=
  (p0, p1) = digestHalves (keccak256 (Value.Keccak.cellsBytes [l0, l1, r0, r1]))

end
end LeanVM.Guest.B1
