import EthCryptographySpecs.Xmss.TweakHash

/-!
# `Xmss.Encoding`

The target-sum encoding.

A fixed digit sum makes the verifier walk the same number of steps every time.

Most digests miss the sum, so the signer retries with a fresh randomizer.
-/

namespace EthCryptographySpecs.Xmss

open EthCryptographySpecs.Xmss.Constants

/-! ## Reading digits out of a digest

These expose the bit layout the proofs reason about. -/

namespace Internal

/-- One half of the digest, read as a little-endian 64-bit word. -/
def digestWord (d : Digest) (half : Fin 2) : UInt64 :=
  -- Half 0 covers bytes 0 to 7,
  -- Half 1 covers bytes 8 to 15.
  let byte := fun k : Fin 8 =>
    (d[8 * half.val + k.val]'(by simp only [DIGEST_LEN]; omega)).toUInt64
  -- Little-endian: byte k sits at bit 8k, so byte 0 is the least significant.
  byte 0 ||| (byte 1 <<< 8) ||| (byte 2 <<< 16) ||| (byte 3 <<< 24)
    ||| (byte 4 <<< 32) ||| (byte 5 <<< 40) ||| (byte 6 <<< 48)
    ||| (byte 7 <<< 56)

/-- Digit `r` of a word: the three bits starting at bit `3 * r`.

The remainder carries the `0..7` bound, so callers never recheck it. -/
def digit (word : UInt64) (r : Nat) : Fin CHAIN_LENGTH :=
  --   word    ... [ digit 2 ] [ digit 1 ] [ digit 0 ]
  --   bits    ...   8  7  6     5  4  3     2  1  0
  --
  -- Shifting by 3r brings digit r to the bottom,
  -- The remainder by 8 drops everything above it.
  ⟨(word >>> (3 * UInt64.ofNat r)).toNat % CHAIN_LENGTH,
    Nat.mod_lt _ (by decide)⟩

/-- The 42 digits a digest carries, admissible or not.

The first half of the digest holds digits 0 to 20, the second half the rest. -/
def digits (d : Digest) : Vector (Fin CHAIN_LENGTH) V :=
  --   digits  0 .. 20   come from half 0, at positions 0 .. 20
  --   digits 21 .. 41   come from half 1, at positions 0 .. 20
  Vector.ofFn fun i =>
    -- 21 digits per half, so the quotient names the half.
    let half : Fin 2 := ⟨i.val / (V / 2), by simp only [V]; omega⟩
    -- and the remainder names the position inside it.
    digit (digestWord d half) (i.val % (V / 2))

/-- Both spare bits are zero.

Bit 63 of each half belongs to no digit, so the signer grinds it to zero. -/
def padded (d : Digest) : Bool :=
  -- 21 digits of 3 bits fill bits 0 to 62, leaving bit 63 spare in each half.
  (digestWord d 0 >>> 63 == 0) && (digestWord d 1 >>> 63 == 0)

/-- The digits add up to the target. -/
def onTarget (x : Vector (Fin CHAIN_LENGTH) V) : Bool :=
  -- Digits are bounded by their type, so the sum runs over their values.
  x.foldl (fun sum d => sum + d.val) 0 == TARGET_SUM

end Internal

/-! ## The encoding -/

/-- The 64-byte string the encoding hashes.

The eight trailing zero bytes are padding, not data. -/
def encodingPayload (msg : Message) (rnd : Randomness) : ByteArray :=
  -- 32 + 24 + 8 = 64 bytes, and the tweak and parameter bring the hash
  -- input to 96, which is two BLAKE2s compressions.
  packBytes msg ++ packBytes rnd ++ ByteArray.mk (Array.replicate 8 0)

/-- Encode a message into 42 chain digits under one randomizer.

This is the WOTS+C encoding (https://eprint.iacr.org/2022/778).

Grinding the randomizer to a fixed digit sum replaces the checksum chains.

Returns nothing when the digest is inadmissible.

Admissible means both spare bits are zero and the digits sum to 195.

Without the spare-bit condition the digits stop determining the digest.

Two different digests could then share one codeword. -/
def wotsEncode (pp : PublicParam) (msg : Message) (rnd : Randomness)
    (epoch : Epoch) : Option (Vector (Fin CHAIN_LENGTH) V) :=
  -- One hash, under the encoding call site, of message and randomizer.
  let d := tweakHash pp .encoding 0 epoch (encodingPayload msg rnd)
  -- The digits always exist; the two checks decide whether they are usable.
  let x := Internal.digits d
  -- Both checks read the same digest, so it is hashed once.
  if Internal.padded d && Internal.onTarget x then some x else none

end EthCryptographySpecs.Xmss
