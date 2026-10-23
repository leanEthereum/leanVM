import LeanVM.Protocol.Blake2sHash

/-!
# BLAKE2s byte hasher tests

`blake2sBytes` against digests of CPython's `hashlib.blake2s`, which wraps the BLAKE2 authors'
reference implementation: the empty message, `"abc"` (RFC 7693 Appendix B), and the byte ramps
of lengths 64, 65 and 128, which sit on both sides of a block boundary and cover the one-block,
two-block and whole-blocks paths of the pinned `hash` (leanVM `127510d1`,
`crates/primitives/src/hash/mod.rs:190-204`). Then `hash_pair` and `hash_words` on known inputs,
the one-compression form of a 64-byte message, and the digest encoding: a round trip and the
rejection of a nonzero top limb.

The compiled checks are `#guard`; the `"abc"` vector is also decided in the kernel.
-/

namespace LeanVMTests.Protocol.Blake2sHash

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Blake2sHash

/-- The bytes `0, 1, …, n - 1`. -/
def ramp (n : ℕ) : List UInt8 := (List.range n).map Nat.toUInt8

/-- `BLAKE2s-256("abc")`, RFC 7693 Appendix B. -/
def abcDigest : Digest :=
  #v[0x8c5e8c50, 0xe2147c32, 0xa32ba7e1, 0x2f45eb4e, 0x208b4537, 0x293ad69e, 0x4c9b994d, 0x82596786]

/-! ## `hashlib.blake2s` digests -/

#guard blake2sBytes [] =
  #v[0x307a2169, 0x94809079, 0xd02111e1, 0x7c4a3542, 0x48b6551f, 0x1ea5a12c, 0xfd0d251b, 0xf9eed01e]

#guard blake2sBytes [0x61, 0x62, 0x63] = abcDigest

example : blake2sBytes [0x61, 0x62, 0x63] = abcDigest := by decide +kernel

#guard blake2sBytes (ramp 64) =
  #v[0x8b4ef356, 0x907e5596, 0x524bf2c1, 0x519dc8d0, 0x1bcf6a08, 0xcf34f600, 0x3392de1d, 0x3eaaeab8]

#guard blake2sBytes (ramp 65) =
  #v[0x94ee531b, 0x4b4ef3aa, 0xde489d15, 0x067f2c35, 0x0ea4d061, 0x0b5af9df, 0x09b43916, 0x7244970e]

#guard blake2sBytes (ramp 128) =
  #v[0xde77a81f, 0x199d2567, 0x342a3a86, 0x2a96c6bc, 0xbffc252b, 0x7ecdbe5c, 0xa31f8fde, 0x96a78866]

/- A 64-byte message is one compression at counter 64 with the last-block flag: the pinned
fast path (`hash/mod.rs:192-199`) and the streaming path agree. -/
#guard blake2sBytes (ramp 64) = compress paramIv (blockWords (ramp 64)) 64 lastBlock 0

/-! ## The Merkle hashes -/

/- `hash_pair` of the `"abc"` digest with itself, from `hashlib`. -/
#guard hashPair abcDigest abcDigest =
  #v[0xa59c72a9, 0xb98ae5a9, 0x557afeed, 0xa8bbbc29, 0x0301d1e3, 0x6cd798d9, 0xe6db79c3, 0x56eda653]

/- A node is one compression of its children's sixteen words. -/
#guard hashPair abcDigest abcDigest = compress paramIv (abcDigest ++ abcDigest) 64 lastBlock 0

/- `hash_words` of the words `1, 2`: the sixteen bytes `01 00 … 00 02 00 … 00`, from
`hashlib`. -/
#guard hashWords [K.ofBits 1, K.ofBits 2] =
  #v[0x6b8928f2, 0x12389f83, 0xe4753c2b, 0x44f83b7f, 0x926dae68, 0xa0cb51b5, 0x1828562e, 0x44a89c61]

/-! ## The digest encoding -/

/- The first half of the `"abc"` digest: bytes `0..8` and `8..16` as the two low limbs. -/
#guard (digestScalars abcDigest).1 =
  E.ofLimbs (K.ofBits 0xe2147c328c5e8c50) (K.ofBits 0x2f45eb4ea32ba7e1) 0

#guard (digestScalars abcDigest).2 =
  E.ofLimbs (K.ofBits 0x293ad69e208b4537) (K.ofBits 0x825967864c9b994d) 0

#guard digestOfScalars (digestScalars abcDigest) = some abcDigest

/- A nonzero top limb in either half is rejected (`Error::NonCanonicalEncoding`). -/
#guard digestOfScalars
  (E.ofLimbs (K.ofBits 0xe2147c328c5e8c50) (K.ofBits 0x2f45eb4ea32ba7e1) (K.ofBits 1),
    (digestScalars abcDigest).2) = none

#guard digestOfScalars
  ((digestScalars abcDigest).1,
    E.ofLimbs (K.ofBits 0x293ad69e208b4537) (K.ofBits 0x825967864c9b994d) (K.ofBits 1)) = none

end LeanVMTests.Protocol.Blake2sHash
