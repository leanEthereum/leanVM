/-
  LeanVM.Facts.ClaimBytes

  A claim's `64` bytes as its key's two `16`-byte halves and its message, for both schemes.
-/

module

public import Statement.LeanVmGuest

/-!
# A claim's bytes in halves

The statement hashes a claim as its key's bytes (`xmssPublicKeyBytes`: root, then parameter;
`Sphincs.PublicKey.toBytes`: `PK.seed`, then `PK.root`) and its message (`claimBytes`). The guest
holds either scheme's claim as four cells, the key's two halves then the message's two
(`claim_cells`, `aggregation/statement.rs`); `claimBytesOf a b m` is those bytes, and
`claimBytes_xmss`, `claimBytes_sphincs` restate the statement's at each scheme.
-/

namespace LeanVM.Node

@[expose] public section

/-- A claim's `64` bytes: two `16`-byte halves of its key, then its `32`-byte message. -/
def claimBytesOf (a b : BitVec 128) (message : BitVec 256) : List UInt8 :=
  HashSig.littleEndianBytes 16 a ++ HashSig.littleEndianBytes 16 b ++
    HashSig.littleEndianBytes 32 message

/-- A leanXMSS claim's bytes: its root, its parameter, its message. -/
theorem claimBytes_xmss (c : LeanXmssClaim) :
    claimBytes xmssPublicKeyBytes c = claimBytesOf c.1.root c.1.parameter c.2 := rfl

/-- A leanSPHINCS claim's bytes: `PK.seed`, `PK.root`, its message. -/
theorem claimBytes_sphincs (c : LeanSphincsClaim) :
    claimBytes Sphincs.PublicKey.toBytes c = claimBytesOf c.1.publicSeed c.1.root c.2 := rfl

theorem claimListPreimage_xmss (l : List LeanXmssClaim) :
    claimListPreimage xmssPublicKeyBytes l =
      l.flatMap fun c ↦ claimBytesOf c.1.root c.1.parameter c.2 := rfl

theorem claimListPreimage_sphincs (l : List LeanSphincsClaim) :
    claimListPreimage Sphincs.PublicKey.toBytes l =
      l.flatMap fun c ↦ claimBytesOf c.1.publicSeed c.1.root c.2 := rfl

end
end LeanVM.Node
