/-!
# `Xmss.Blake2s`

BLAKE2s-256 as specified by RFC 7693.

The implementation accepts an unkeyed byte string and returns 32 bytes.

RFC conformance requires the input length to be below `2^64` bytes.

Larger logical arrays are outside the standard because the byte counter wraps.

It is written as a direct transcription for reviewability.

It is not intended to be constant-time.
-/

namespace EthCryptographySpecs.Xmss.Blake2s

/-! ## Proof-facing definitions

These definitions expose the RFC's data layout and block accounting.

The compression machinery remains private to the executable specification.
-/

namespace Internal

/-- The ten message-word permutations from RFC 7693 Section 2.7. -/
def sigma : Array (Array Nat) := #[
  #[ 0,  1,  2,  3,  4,  5,  6,  7,  8,  9, 10, 11, 12, 13, 14, 15],
  #[14, 10,  4,  8,  9, 15, 13,  6,  1, 12,  0,  2, 11,  7,  5,  3],
  #[11,  8, 12,  0,  5,  2, 15, 13, 10, 14,  3,  6,  7,  1,  9,  4],
  #[ 7,  9,  3,  1, 13, 12, 11, 14,  2,  6,  5, 10,  4,  0, 15,  8],
  #[ 9,  0,  5,  7,  2,  4, 10, 15, 14,  1, 11, 12,  6,  8,  3, 13],
  #[ 2, 12,  6, 10,  0, 11,  8,  3,  4, 13,  7,  5, 15, 14,  1,  9],
  #[12,  5,  1, 15, 14, 13,  4, 10,  0,  7,  6,  3,  9,  2,  8, 11],
  #[13, 11,  7, 14, 12,  1,  3,  9,  5,  0, 15,  4,  8,  6,  2, 10],
  #[ 6, 15, 14,  9, 11,  3,  0,  8, 12,  2, 13,  7,  1,  4, 10,  5],
  #[10,  2,  8,  4,  7,  6,  1,  5, 15, 11,  9, 14,  3, 12, 13,  0]
]

/-- Read four bytes as one little-endian word.

Bytes beyond the input are read as zero.

That implements final-block padding without extending the message.
-/
@[inline] def little32 (input : ByteArray) (offset : Nat) : UInt32 :=
  -- Byte 0 occupies the least significant eight bits.
  (input.data.getD offset 0).toUInt32
  -- Byte 1 occupies bits 8 through 15.
  ||| ((input.data.getD (offset + 1) 0).toUInt32 <<< 8)
  -- Byte 2 occupies bits 16 through 23.
  ||| ((input.data.getD (offset + 2) 0).toUInt32 <<< 16)
  -- Byte 3 occupies the most significant eight bits.
  ||| ((input.data.getD (offset + 3) 0).toUInt32 <<< 24)

/-- Serialize one word as four little-endian bytes. -/
def wordBytes (word : UInt32) : Vector UInt8 4 :=
  -- Position zero receives the least significant byte.
  Vector.ofFn fun position => (word >>> UInt32.ofNat (8 * position.val)).toUInt8

/-- Number of 64-byte blocks needed by the unkeyed driver.

The lower bound of one implements the mandatory empty-message block.
-/
def blockCount (length : Nat) : Nat :=
  -- Adding 63 before division computes the ceiling for positive lengths.
  max 1 ((length + 63) / 64)

/-- Byte offset at which a numbered block begins. -/
def blockOffset (block : Nat) : Nat :=
  -- Every preceding block accounts for exactly 64 bytes.
  block * 64

/-- Number of message bytes carried by a numbered block. -/
def bytesInBlock (length block : Nat) : Nat :=
  -- Full blocks contribute 64 bytes.
  -- A final partial block contributes only the remaining bytes.
  min 64 (length - blockOffset block)

/-- Byte counter at the end of a numbered block. -/
def blockCounter (length block : Nat) : Nat :=
  -- RFC 7693 counts every preceding byte and the current block's real bytes.
  blockOffset block + bytesInBlock length block

/-- Low 32-bit word of the 64-bit byte counter. -/
def counterLow (counter : UInt64) : UInt32 :=
  -- Truncation retains bits 0 through 31.
  counter.toUInt32

/-- High 32-bit word of the 64-bit byte counter. -/
def counterHigh (counter : UInt64) : UInt32 :=
  -- Moving bits 32 through 63 down makes them the retained low word.
  (counter >>> 32).toUInt32

end Internal

/-! ## Parameters -/

/-- The SHA-256 initialization vector reused by BLAKE2s. -/
private def IV : Array UInt32 := #[
  0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a,
  0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19
]

/-! ## Word operations -/

/-- Rotate a 32-bit word right by a fixed distance. -/
@[inline] private def rotateRight (x : UInt32) (n : UInt32) : UInt32 :=
  -- The two disjoint shifts reconstruct the cyclic bit movement.
  (x >>> n) ||| (x <<< (32 - n))

/-- Apply one BLAKE2s mixing operation to four lanes.

The additions wrap modulo `2^32` because the lane type is a 32-bit word.
-/
@[inline] private def mix (state : Array UInt32) (a b c d : Nat)
    (x y : UInt32) : Array UInt32 := Id.run do
  -- First half: inject the first scheduled message word.
  let mut work := state
  work := work.set! a (work[a]! + work[b]! + x)
  work := work.set! d (rotateRight (work[d]! ^^^ work[a]!) 16)
  work := work.set! c (work[c]! + work[d]!)
  work := work.set! b (rotateRight (work[b]! ^^^ work[c]!) 12)
  -- Second half: inject the second scheduled message word.
  work := work.set! a (work[a]! + work[b]! + y)
  work := work.set! d (rotateRight (work[d]! ^^^ work[a]!) 8)
  work := work.set! c (work[c]! + work[d]!)
  work := work.set! b (rotateRight (work[b]! ^^^ work[c]!) 7)
  return work

/-! ## Compression -/

/-- Compress one 64-byte block into an eight-word chaining value.

The byte counter includes the current block.

The Boolean marks the final block and inverts working lane 14.
-/
private def compress (chaining message : Array UInt32) (counter : UInt64)
    (last : Bool) : Array UInt32 := Id.run do
  -- RFC 7693 Section 3.2 initializes the working vector from state and IV.
  let mut work := chaining ++ IV
  -- The full 64-bit byte counter is split across two 32-bit lanes.
  work := work.set! 12 (work[12]! ^^^ Internal.counterLow counter)
  work := work.set! 13 (work[13]! ^^^ Internal.counterHigh counter)
  -- Finalization complements one lane before the rounds begin.
  if last then
    work := work.set! 14 (~~~work[14]!)
  -- Each permutation selects the message words injected by eight mixes.
  for round in [:10] do
    let schedule := Internal.sigma[round]!
    -- Four column mixes operate on disjoint lane quartets.
    work := mix work 0 4 8 12 message[schedule[0]!]! message[schedule[1]!]!
    work := mix work 1 5 9 13 message[schedule[2]!]! message[schedule[3]!]!
    work := mix work 2 6 10 14 message[schedule[4]!]! message[schedule[5]!]!
    work := mix work 3 7 11 15 message[schedule[6]!]! message[schedule[7]!]!
    -- Four diagonal mixes spread each column's result across all columns.
    work := mix work 0 5 10 15 message[schedule[8]!]! message[schedule[9]!]!
    work := mix work 1 6 11 12 message[schedule[10]!]! message[schedule[11]!]!
    work := mix work 2 7 8 13 message[schedule[12]!]! message[schedule[13]!]!
    work := mix work 3 4 9 14 message[schedule[14]!]! message[schedule[15]!]!
  -- Feed both halves of the working vector back into the chaining value.
  return Array.ofFn fun i : Fin 8 =>
    chaining[i.val]! ^^^ work[i.val]! ^^^ work[i.val + 8]!

/-- Read one 64-byte block as sixteen little-endian words. -/
private def blockWords (input : ByteArray) (offset : Nat) : Array UInt32 :=
  -- Each word begins four bytes after the preceding word.
  Array.ofFn fun i : Fin 16 => Internal.little32 input (offset + 4 * i)

/-- Serialize an eight-word chaining value in little-endian order. -/
private def stateBytes (state : Array UInt32) : Vector UInt8 32 :=
  -- Each output byte selects one word and one of its four byte positions.
  Vector.ofFn fun i =>
    let word := state[i / 4]!
    let position : Fin 4 := ⟨i.val % 4, Nat.mod_lt _ (by decide)⟩
    (Internal.wordBytes word)[position]

/-! ## Hash driver -/

/-- Compute the 32-byte BLAKE2s digest of an unkeyed byte string.

RFC conformance requires fewer than `2^64` input bytes.

Larger logical arrays wrap the standard's 64-bit byte counter.

The empty string still compresses one zero block.

An exact multiple of 64 bytes marks its last data block as final.
-/
def hash (input : ByteArray) : Vector UInt8 32 := Id.run do
  -- Unkeyed 32-byte output uses fanout 1 and depth 1 in the parameter block.
  let mut chaining := IV.set! 0 (IV[0]! ^^^ 0x01010020)
  -- Ceiling division gives the data-block count.
  -- The lower bound of one implements RFC 7693's empty-message rule.
  let blocks := Internal.blockCount input.size
  for block in [:blocks] do
    let offset := Internal.blockOffset block
    -- Full non-final blocks contribute 64 bytes.
    -- The final block contributes only the bytes actually present.
    let counter := UInt64.ofNat (Internal.blockCounter input.size block)
    let last := block + 1 == blocks
    chaining := compress chaining (blockWords input offset) counter last
  -- RFC 7693 returns the little-endian byte encoding of the final state.
  return stateBytes chaining

end EthCryptographySpecs.Xmss.Blake2s
