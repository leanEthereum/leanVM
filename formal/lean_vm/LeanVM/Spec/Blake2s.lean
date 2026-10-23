/-
  LeanVM.Spec.Blake2s

  BLAKE2s: the compression function, which the ISA's `BLAKE2S` instruction computes, and
  BLAKE2s-256 over byte strings, the hash of the verifier's Fiat-Shamir chain and Merkle trees.
-/

module

public import LeanVM.Spec.Field

/-!
# BLAKE2s

RFC 7693: the constants (§2.6 to §2.7), the compression function `compress` with the last-node flag
of the BLAKE2 paper, and the unkeyed BLAKE2s-256 of a byte string `blake2sBytes` (§3.3), as the
pinned leanVM computes them (`crates/primitives/src/hash/mod.rs`,
`127510d14c98ade4e8a97646c44fa7f1ff5e752d`). Then the byte and field encodings the verifier
hashes: a `K` word as eight little-endian bytes, the Merkle leaf and node hashes, and a digest as
two field elements.
-/

namespace LeanVM.Parameters

@[expose] public section

/-- The BLAKE2s initialization vector, RFC 7693 §2.6: `IV[i] = ⌊2^32 · frac(√pᵢ₊₁)⌋` for the first
eight primes, the SHA-256 IV. -/
def iv : Vector UInt32 8 := #v[
  0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a,
  0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19]

/-- The BLAKE2s message schedule, RFC 7693 §2.7: `sigma[r]` is the permutation of the sixteen
message words consumed by round `r`. -/
def sigma : Vector (Vector (Fin 16) 16) 10 := #v[
  #v[ 0,  1,  2,  3,  4,  5,  6,  7,  8,  9, 10, 11, 12, 13, 14, 15],
  #v[14, 10,  4,  8,  9, 15, 13,  6,  1, 12,  0,  2, 11,  7,  5,  3],
  #v[11,  8, 12,  0,  5,  2, 15, 13, 10, 14,  3,  6,  7,  1,  9,  4],
  #v[ 7,  9,  3,  1, 13, 12, 11, 14,  2,  6,  5, 10,  4,  0, 15,  8],
  #v[ 9,  0,  5,  7,  2,  4, 10, 15, 14,  1, 11, 12,  6,  8,  3, 13],
  #v[ 2, 12,  6, 10,  0, 11,  8,  3,  4, 13,  7,  5, 15, 14,  1,  9],
  #v[12,  5,  1, 15, 14, 13,  4, 10,  0,  7,  6,  3,  9,  2,  8, 11],
  #v[13, 11,  7, 14, 12,  1,  3,  9,  5,  0, 15,  4,  8,  6,  2, 10],
  #v[ 6, 15, 14,  9, 11,  3,  0,  8, 12,  2, 13,  7,  1,  4, 10,  5],
  #v[10,  2,  8,  4,  7,  6,  1,  5, 15, 11,  9, 14,  3, 12, 13,  0]]

end
end LeanVM.Parameters

namespace LeanVM.Semantics

open LeanVM.Parameters

@[expose] public section

/-! ## The compression function -/

namespace Blake2s

/-- Rotate right by `n` bits. -/
def rotr (x : UInt32) (n : ℕ) : UInt32 := ⟨x.toBitVec.rotateRight n⟩

/-- The mixing function `G`. -/
def mix (v : Vector UInt32 16) (a b c d : Fin 16) (x y : UInt32) : Vector UInt32 16 :=
  let va := v[a] + v[b] + x
  let vd := rotr (v[d] ^^^ va) 16
  let vc := v[c] + vd
  let vb := rotr (v[b] ^^^ vc) 12
  let va := va + vb + y
  let vd := rotr (vd ^^^ va) 8
  let vc := vc + vd
  let vb := rotr (vb ^^^ vc) 7
  (((v.set a va).set b vb).set c vc).set d vd

/-- One round: four column and four diagonal mixes, message words chosen by `s`. -/
def round (v m : Vector UInt32 16) (s : Vector (Fin 16) 16) : Vector UInt32 16 :=
  let v := mix v 0 4 8 12 m[s[0]] m[s[1]]
  let v := mix v 1 5 9 13 m[s[2]] m[s[3]]
  let v := mix v 2 6 10 14 m[s[4]] m[s[5]]
  let v := mix v 3 7 11 15 m[s[6]] m[s[7]]
  let v := mix v 0 5 10 15 m[s[8]] m[s[9]]
  let v := mix v 1 6 11 12 m[s[10]] m[s[11]]
  let v := mix v 2 7 8 13 m[s[12]] m[s[13]]
  mix v 3 4 9 14 m[s[14]] m[s[15]]

/-- The initial state: `h`, then `iv` with the counter and the two flag words XORed in. -/
def initialState (h : Vector UInt32 8) (t : UInt64) (f0 f1 : UInt32) : Vector UInt32 16 :=
  let v : Vector UInt32 16 := h ++ iv
  let v := v.set 12 (v[12] ^^^ t.toUInt32)
  let v := v.set 13 (v[13] ^^^ (t >>> 32).toUInt32)
  let v := v.set 14 (v[14] ^^^ f0)
  v.set 15 (v[15] ^^^ f1)

end Blake2s

/-- The compression of the message `m` under the chaining value `h`, with counter `t`, last-block
flag word `f0` and last-node flag word `f1`: ten rounds, then `h[i] ^ v[i] ^ v[i + 8]`. -/
def compress (h : Vector UInt32 8) (m : Vector UInt32 16) (t : UInt64) (f0 f1 : UInt32) :
    Vector UInt32 8 :=
  let v := sigma.foldl (fun v s ↦ Blake2s.round v m s) (Blake2s.initialState h t f0 f1)
  #v[h[0] ^^^ v[0] ^^^ v[8], h[1] ^^^ v[1] ^^^ v[9], h[2] ^^^ v[2] ^^^ v[10],
     h[3] ^^^ v[3] ^^^ v[11], h[4] ^^^ v[4] ^^^ v[12], h[5] ^^^ v[5] ^^^ v[13],
     h[6] ^^^ v[6] ^^^ v[14], h[7] ^^^ v[7] ^^^ v[15]]

/-- The low 32 bits of a `K` element. -/
def lowWord (a : K) : UInt32 := ⟨a.toBitVec.extractLsb' 0 32⟩

/-- The high 32 bits of a `K` element. -/
def highWord (a : K) : UInt32 := ⟨a.toBitVec.extractLsb' 32 32⟩

/-- The `K` element with these low and high 32 bits. -/
def ofWords (lo hi : UInt32) : K := BF64.ofBitVec (hi.toBitVec ++ lo.toBitVec)

/-- The four 32-bit words of a memory word `a₀ + a₁·y`, little-endian. -/
def cellWords (x : E) : Vector UInt32 4 :=
  #v[lowWord (x.limb 0), highWord (x.limb 0), lowWord (x.limb 1), highWord (x.limb 1)]

/-- The memory word holding four 32-bit words. -/
def wordsCell (w : Vector UInt32 4) : E :=
  E.ofLimbs (ofWords w[0] w[1]) (ofWords w[2] w[3]) 0

end
end LeanVM.Semantics

namespace LeanVM.Protocol

open LeanVM.Parameters LeanVM.Semantics

@[expose] public section

/-- A BLAKE2s-256 digest, as the eight chaining words of its last compression. -/
abbrev Digest := Vector UInt32 8

/-- Digest equality decided on the word lists, usable from a module file, where core's
`DecidableEq` for `Vector` is not exposed. -/
def Digest.decEq : DecidableEq Digest := fun a b ↦
  decidable_of_iff (a.toList = b.toList) Vector.toList_inj

namespace Blake2sHash

/-! ## RFC 7693 §3.3 -/

/-- The last-block flag word. -/
def lastBlock : UInt32 := 0xFFFFFFFF

/-- The initial chaining value of an unkeyed BLAKE2s-256: `iv` with the parameter block
`0x01010020` (digest length 32, key length 0, fanout 1, depth 1; RFC 7693 §2.8) XORed into word 0
(`hash/mod.rs:75-83`, `PARAM_IV`; `init_state` is gone at this pin). -/
def paramIv : Vector UInt32 8 := iv.set 0 (iv[0] ^^^ 0x01010020)

/-- A little-endian word from four bytes. -/
def leWord (b0 b1 b2 b3 : UInt8) : UInt32 :=
  b0.toUInt32 ||| (b1.toUInt32 <<< 8) ||| (b2.toUInt32 <<< 16) ||| (b3.toUInt32 <<< 24)

/-- The sixteen little-endian words of a block of at most 64 bytes, zero-padded
(`hash/mod.rs:120-122`, `block_words`). -/
def blockWords (block : List UInt8) : Vector UInt32 16 :=
  let b := fun i ↦ block.getD i 0
  #v[leWord (b 0) (b 1) (b 2) (b 3), leWord (b 4) (b 5) (b 6) (b 7),
     leWord (b 8) (b 9) (b 10) (b 11), leWord (b 12) (b 13) (b 14) (b 15),
     leWord (b 16) (b 17) (b 18) (b 19), leWord (b 20) (b 21) (b 22) (b 23),
     leWord (b 24) (b 25) (b 26) (b 27), leWord (b 28) (b 29) (b 30) (b 31),
     leWord (b 32) (b 33) (b 34) (b 35), leWord (b 36) (b 37) (b 38) (b 39),
     leWord (b 40) (b 41) (b 42) (b 43), leWord (b 44) (b 45) (b 46) (b 47),
     leWord (b 48) (b 49) (b 50) (b 51), leWord (b 52) (b 53) (b 54) (b 55),
     leWord (b 56) (b 57) (b 58) (b 59), leWord (b 60) (b 61) (b 62) (b 63)]

/-- Absorb `data` into the chaining value `h` after `t` bytes: `blocks` more non-final blocks of
64 bytes, each compressed at the byte count including it with no flag, then the rest as the
final block, zero-padded, compressed at the total length with the last-block flag
(RFC 7693 §3.3; `hash/mod.rs:157-180`, `Hasher.update` and `finalize`). -/
def absorb (h : Vector UInt32 8) (t : ℕ) : (blocks : ℕ) → List UInt8 → Digest
  | 0, data => compress h (blockWords data) (t + data.length).toUInt64 lastBlock 0
  | blocks + 1, data =>
    absorb (compress h (blockWords (data.take 64)) (t + 64).toUInt64 0 0) (t + 64) blocks
      (data.drop 64)

/-- BLAKE2s-256 of a byte string (`hash/mod.rs:190-204`, `hash`): `⌈len/64⌉ - 1` non-final blocks,
then the final one; the empty string is one zero block at counter `0`. -/
def blake2sBytes (data : List UInt8) : Digest :=
  absorb paramIv 0 ((data.length - 1) / 64) data

/-! ## Bytes of words and digests -/

/-- The four little-endian bytes of a word. -/
def wordBytes (w : UInt32) : List UInt8 :=
  [w.toUInt8, (w >>> 8).toUInt8, (w >>> 16).toUInt8, (w >>> 24).toUInt8]

/-- The 32 bytes of a digest: its words, little-endian (`hash/mod.rs:126-132`,
`state_bytes`). -/
def digestBytes (d : Digest) : List UInt8 := d.toList.flatMap wordBytes

/-- The eight little-endian bytes of a `K` word (`crates/verifier/src/field.rs:60-63`,
`K::to_bytes`). -/
def kBytes (a : K) : List UInt8 := wordBytes (lowWord a) ++ wordBytes (highWord a)

/-! ## The Merkle hashes -/

/-- The digest of a leaf: BLAKE2s-256 of its words as bytes (`crates/verifier/src/merkle.rs:44-46`,
`hash_leaf`). -/
def hashWords (words : List K) : Digest := blake2sBytes (words.flatMap kBytes)

/-- The digest of a node: BLAKE2s-256 of the 64 bytes of its two children, left first
(`crates/verifier/src/merkle.rs:37-42`, `hash_pair`). -/
def hashPair (left right : Digest) : Digest :=
  blake2sBytes (digestBytes left ++ digestBytes right)

/-! ## The digest encoding (`fiat_shamir/src/merkle.rs:13-19`, `verifier/src/hash.rs:99-117`) -/

/-- A digest as the two field elements a transcript carries it in: bytes `0..16` and `16..32`,
each as a canonical 128-bit cell (`hash_to_scalars`). -/
def digestScalars (d : Digest) : E × E :=
  (wordsCell #v[d[0], d[1], d[2], d[3]], wordsCell #v[d[4], d[5], d[6], d[7]])

/-- The digest two field elements encode, or `none` if either has a nonzero top limb
(`Digest::from_halves`, `VerifierError::DigestHalf`). -/
def digestOfScalars (s : E × E) : Option Digest :=
  if IsCanonical128 s.1 ∧ IsCanonical128 s.2 then some (cellWords s.1 ++ cellWords s.2) else none

end Blake2sHash

end
end LeanVM.Protocol
