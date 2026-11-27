module

public import Statement.Keccak

@[expose] public section

/-!
# A digest as 32 bytes

The proofs' random oracle answers Keccak-256 as `32` bytes (`Common.DigestBytes`); the statement's
digest is four 64-bit words (`LeanVM.Protocol.Digest`), whose bytes `Digest.toBytes` lists, the
statement's `digestBytes` as a vector.
-/

namespace Common

/-- A 32-byte Keccak-256 digest. -/
abbrev DigestBytes := Vector UInt8 32

end Common

namespace LeanVM.Protocol

/-- The 32 bytes of a digest as a vector (`Common.DigestBytes`). -/
def Digest.toBytes (digest : Digest) : Vector UInt8 32 :=
  ⟨(KeccakHash.digestBytes digest).toArray, by
    obtain ⟨⟨l⟩, hl⟩ := digest
    match l, hl with
    | [_, _, _, _], _ => rfl⟩

end LeanVM.Protocol

end
