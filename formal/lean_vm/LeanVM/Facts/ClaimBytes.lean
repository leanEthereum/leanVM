/-
  LeanVM.Facts.ClaimBytes

  A claim's `64` bytes as its key's two `16`-byte halves and its message, for both schemes.
-/

module

public import Statement.LeanVmGuest
public import EthLib.Cryptography.Proofs.Hash.Keccak.Lanes

/-!
# A claim's bytes in halves

The statement hashes a claim as its key's bytes (`xmssPublicKeyBytes`: root, then parameter;
`Sphincs.PublicKey.toBytes`: `PK.seed`, then `PK.root`) and its message (`claimBytes`). The guest
holds either scheme's claim as four cells, the key's two halves then the message's two
(`claim_cells`, `crates/aggregation/src/statement.rs`); `claimBytesOf a b m` is those bytes, and
`claimBytes_xmss`, `claimBytes_sphincs` restate the statement's at each scheme. A leanXMSS key's
halves are EthLib's lanes, held as the `128`-bit numbers of their bytes (`xmssRoot`, `xmssParam`,
`bytes_eq_littleEndianBytes`).
-/

namespace LeanVM.Node

@[expose] public section

/-- A claim's `64` bytes: two `16`-byte halves of its key, then its `32`-byte message. -/
def claimBytesOf (a b : BitVec 128) (message : BitVec 256) : List UInt8 :=
  HashSig.littleEndianBytes 16 a ++ HashSig.littleEndianBytes 16 b ++
    HashSig.littleEndianBytes 32 message

/-- Two lanes' `16` bytes are the little-endian bytes of their number. -/
theorem bytes_eq_littleEndianBytes (w : EthLib.Cryptography.Hash.Keccak.Lanes2) :
    w.bytes.toList = HashSig.littleEndianBytes 16 (BitVec.ofNat 128 w.toNat) := by
  rw [EthLib.Cryptography.Hash.Keccak.Lanes2.bytes_eq_toLE]
  simp only [HashSig.littleEndianBytes, EthLib.Base.ByteOrder.toLE, Vector.toList_ofFn]
  refine congrArg List.ofFn (funext fun i => ?_)
  apply UInt8.toNat_inj.mp
  have hlt := w.toNat_lt
  simp only [UInt8.toNat_ofBitVec, BitVec.extractLsb'_toNat, BitVec.toNat_ofNat,
    Nat.shiftRight_eq_div_pow]
  rw [Nat.mod_eq_of_lt hlt, UInt8.toNat_ofNat']

/-- Two lanes are determined by their `128`-bit number. -/
theorem lanes_inj_of_ofNat {a b : EthLib.Cryptography.Hash.Keccak.Lanes2}
    (h : BitVec.ofNat 128 a.toNat = BitVec.ofNat 128 b.toNat) : a = b := by
  apply EthLib.Cryptography.Hash.Keccak.Lanes2.toNat_injective
  have := congrArg BitVec.toNat h
  simp only [BitVec.toNat_ofNat] at this
  rwa [Nat.mod_eq_of_lt a.toNat_lt, Nat.mod_eq_of_lt b.toNat_lt] at this

/-- A leanXMSS claim's root, as a `128`-bit number. -/
def xmssRoot (c : LeanXmssClaim) : BitVec 128 := BitVec.ofNat 128 c.1.root.toNat

/-- A leanXMSS claim's parameter, as a `128`-bit number. -/
def xmssParam (c : LeanXmssClaim) : BitVec 128 := BitVec.ofNat 128 c.1.publicParam.toNat

/-- A leanXMSS claim's bytes: its root, its parameter, its message. -/
theorem claimBytes_xmss (c : LeanXmssClaim) :
    claimBytes xmssPublicKeyBytes c = claimBytesOf (xmssRoot c) (xmssParam c) c.2 := by
  unfold claimBytes xmssPublicKeyBytes claimBytesOf xmssRoot xmssParam
  rw [bytes_eq_littleEndianBytes, bytes_eq_littleEndianBytes]

/-- A leanSPHINCS claim's bytes: `PK.seed`, `PK.root`, its message. -/
theorem claimBytes_sphincs (c : LeanSphincsClaim) :
    claimBytes Sphincs.PublicKey.toBytes c = claimBytesOf c.1.publicSeed c.1.root c.2 := rfl

theorem claimListPreimage_xmss (l : List LeanXmssClaim) :
    claimListPreimage xmssPublicKeyBytes l =
      l.flatMap fun c ↦ claimBytesOf (xmssRoot c) (xmssParam c) c.2 := by
  unfold claimListPreimage
  congr 1
  funext c
  exact claimBytes_xmss c

theorem claimListPreimage_sphincs (l : List LeanSphincsClaim) :
    claimListPreimage Sphincs.PublicKey.toBytes l =
      l.flatMap fun c ↦ claimBytesOf c.1.publicSeed c.1.root c.2 := rfl

end
end LeanVM.Node
