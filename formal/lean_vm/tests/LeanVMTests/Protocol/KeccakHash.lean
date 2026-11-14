import LeanVM.Protocol.KeccakHash
import Statement.Fast.Keccak
import Statement.LeanVmGuest
import LeanVM.Guest.AcceptableChild

/-!
# Keccak tests

`keccak256` against known answers: the empty message and `"abc"` (Ethereum's Keccak-256,
`c5d24601…` and `4e03657a…`), and the byte ramps of lengths 135, 136, 137, 272 and 300, which
sit on both sides of the 136-byte block boundary and cover the one-byte padding `0x81` (135
bytes), a padding block of its own (136, 272) and the multi-block path. The digests are the
verifier's `keccak_hash` at leanVM `4af2cdddd7cd41b9df2cc7e123e314a91b0b4462` (at the pin
`40f877dc`, `crates/verifier/src/hash.rs`), whose permutation is checked
independently: run with FIPS 202's padding `0x06` it gives `hashlib.sha3_256` on the same ramps
(script `vectors.py` of the port). Then `keccakF` on the zero state (Keccak-f[1600]'s
well-known `f1258f79…`) and on the lanes `0 … 24`; `hash_pair` and `hash_words` on known
inputs; a 64-byte message as one permutation of its padded block; the hash chain of
`crates/rec_aggregation/src/hash_chain.rs` (eight `compress` steps from the zero digest); and
the digest encoding's round trip.

`Statement.Fast.Keccak` compiles the hash here (`@[csimp]`); the `"abc"` vector and the zero
state's permutation are also decided in the kernel, on the definitions themselves.
-/

namespace LeanVMTests.Protocol.KeccakHash

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash

/-- The bytes `0, 1, …, n - 1`, modulo `256`. -/
def ramp (n : ℕ) : List UInt8 := (List.range n).map Nat.toUInt8

/-- Keccak-256 of `"abc"`. -/
def abcDigest : Digest :=
  #v[0x4fa945ea7a65034e, 0x67d6c826a87bd4c7, 0x36a0643ae3e6d1c0, 0x456c2da18ff544ec]

/-! ## Keccak-256 -/

#guard keccak256 [] =
  #v[0x3c23f7860146d2c5, 0xc003c7dcb27d7e92, 0x3b2782ca53b600e5, 0x70a4855d04d8fa7b]

#guard keccak256 [0x61, 0x62, 0x63] = abcDigest

example : keccak256 [0x61, 0x62, 0x63] = abcDigest := by decide +kernel

/- The digest's bytes are Ethereum's `4e03657a…6c45`. -/
#guard digestBytes abcDigest = [0x4e, 0x03, 0x65, 0x7a, 0xea, 0x45, 0xa9, 0x4f, 0xc7, 0xd4, 0x7b,
  0xa8, 0x26, 0xc8, 0xd6, 0x67, 0xc0, 0xd1, 0xe6, 0xe3, 0x3a, 0x64, 0xa0, 0x36, 0xec, 0x44, 0xf5,
  0x8f, 0xa1, 0x2d, 0x6c, 0x45]

#guard keccak256 (ramp 135) =
  #v[0x38adfae5ded9dfcb, 0xfd19a2956fb0d618, 0x2ea8f606170e0b29, 0x62cafae99c5b595a]

#guard keccak256 (ramp 136) =
  #v[0xe49c7fabf159e77c, 0x660a6bc270997137, 0xf87de1383efe11ff, 0x7e807f7d9cd2f59c]

#guard keccak256 (ramp 137) =
  #v[0x53848be6fad473ac, 0x95ce201a7c0064f7, 0x27320c1f86874199, 0xdbb1a3739ae9a8a3]

#guard keccak256 (ramp 272) =
  #v[0x0d9649e749ecf2fd, 0xd0f89a21a021853c, 0x16bd19bfb3e2303e, 0x6ed633f1eae00e15]

#guard keccak256 (ramp 300) =
  #v[0x0c30afa649e779a6, 0x8620d25522ffe736, 0xdccff982b327ab4e, 0xff36ba6335d1a45a]

-- Mutation: one byte changed.
#guard keccak256 [0x61, 0x62, 0x64] ≠ abcDigest

/-! ## Keccak-f[1600] -/

/-- The zero state's image. -/
def keccakFZero : KeccakState :=
  #v[0xf1258f7940e1dde7, 0x84d5ccf933c0478a, 0xd598261ea65aa9ee, 0xbd1547306f80494d,
    0x8b284e056253d057, 0xff97a42d7f8e6fd4, 0x90fee5a0a44647c4, 0x8c5bda0cd6192e76,
    0xad30a6f71b19059c, 0x30935ab7d08ffc64, 0xeb5aa93f2317d635, 0xa9a6e6260d712103,
    0x81a57c16dbcf555f, 0x43b831cd0347c826, 0x01f22f1a11a5569f, 0x05e5635a21d9ae61,
    0x64befef28cc970f2, 0x613670957bc46611, 0xb87c5a554fd00ecb, 0x8c3ee88a1ccf32c8,
    0x940c7922ae3a2614, 0x1841f924a2c509e4, 0x16f53526e70465c2, 0x75f644e97f30a13b,
    0xeaf1ff7b5ceca249]

#guard keccakF1600 (Vector.replicate 25 0) = keccakFZero

example : keccakF1600 (Vector.replicate 25 0) = keccakFZero := by decide +kernel

#guard keccakF1600 (Vector.ofFn fun i ↦ i.val.toUInt64) =
  #v[0x8374b05252ed8115, 0x1df7a676b6569400, 0xf765194b8a51797d, 0x20477b43d1760545,
    0xd15f8ba4f3f6606a, 0xa1d7144f7c8dd493, 0x30d193965138fd3f, 0x487e9472951be3be,
    0x0cf3a858cbda7a5a, 0x2fe54e389bb17f88, 0x0b7338de0d9f268f, 0x55efdff58b256d7f,
    0xc8353e94eb2c3e6a, 0x2e2af6948c901f11, 0xe873de0cca309da6, 0xf7afc26c944d31e2,
    0xa0f5ea808cc415d7, 0x53f531437e3ed8cf, 0x777f1f3b43a4d221, 0xfd0ca63cb499e985,
    0xd4c055c0c5d12330, 0xa72fe58aa6e0a7df, 0x421af5937c9948a3, 0x5e16103071340888,
    0xd153f43a297e4a33]

/-! ## The Merkle hashes -/

/- `hash_pair` of the `"abc"` digest with itself. -/
#guard hashPair abcDigest abcDigest =
  #v[0x636d75ec618368e1, 0xc26e8d4a118b3934, 0x2448b5435754c4d1, 0xa07b67492ed968c7]

/- A node is one permutation of its children's 64 bytes, padded, from the zero state. -/
#guard hashPair abcDigest abcDigest =
  let s := absorbBlock (Vector.replicate 25 0) (padBlock (digestBytes abcDigest ++ digestBytes abcDigest))
  #v[Keccak.lane s 0, Keccak.lane s 1, Keccak.lane s 2, Keccak.lane s 3]

/- `hash_words` of the words `1, 2`: the sixteen bytes `01 00 … 00 02 00 … 00`. -/
#guard merkleLeafDigest [K.ofBits 1, K.ofBits 2] =
  #v[0x7f99c7cdf41edaab, 0xfd627cf8bdca2ecd, 0x82f07915d8dc54b2, 0x3a8f3df9f4f1347b]

/- The hash chain of `hash_chain.rs`: `compress(d, d)` eight times from the zero digest. -/
#guard (List.range 8).foldl (fun d _ ↦ hashPair d d) (Vector.replicate 4 0) =
  #v[0x936b197f5fcc6798, 0x247420637ee2e1ba, 0x49273826f290d245, 0xaf56f739c5fe548b]

/-! ## The digest encoding -/

/- The first half of the `"abc"` digest: its words `0` and `1` as the two low limbs. -/
#guard (digestHalves abcDigest).1 =
  E.ofLimbs (K.ofBits 0x4fa945ea7a65034e) (K.ofBits 0x67d6c826a87bd4c7)

#guard (digestHalves abcDigest).2 =
  E.ofLimbs (K.ofBits 0x36a0643ae3e6d1c0) (K.ofBits 0x456c2da18ff544ec)

#guard digestFromHalves (digestHalves abcDigest) = abcDigest

end LeanVMTests.Protocol.KeccakHash
