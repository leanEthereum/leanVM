import EthCryptographySpecs.Xmss.Blake2s
import EthCryptographySpecs.Xmss.Types

/-!
# `Xmss.TweakHash`

The tweakable hash every other definition here is built from.

A single hash function across the network would expose a lot of targets:

```text
per key   2^32 epochs x 42 chains x 7 values   ~ 2^40
network   x 2^20 keys                          ~ 2^60
```

Finding one preimage among `M` targets costs `2^128 / M`.

At `M = 2^60` that is 68 bits instead of 128.

Giving each call site its own hash function removes the discount.
-/

namespace EthCryptographySpecs.Xmss

open EthCryptographySpecs.Xmss.Constants

/-! ## Call sites -/

/-- Which call site a hash belongs to: one call site, one hash function. -/
inductive TweakType where
  /-- Derive one chain's secret starting value from the master secret. -/
  | prf
  /-- Take one step along a hash chain. -/
  | chain
  /-- Hash the chain tips of one epoch into a Merkle leaf. -/
  | leaf
  /-- Combine two Merkle children into their parent. -/
  | merkle
  /-- Encode a message into chain digits. -/
  | encoding
  /-- Derive the public parameter from the master secret. -/
  | parameter
  /-- Stand in for a subtree the key's epoch range does not cover. -/
  | filler
  /-- Derive the randomizer of one grinding attempt. -/
  | randomizer
  deriving DecidableEq, Repr

/-- The byte each tweak type is assigned. -/
def TweakType.toByte : TweakType → UInt8
  | .prf        => 0
  | .chain      => 1
  | .leaf       => 2
  | .merkle     => 3
  | .encoding   => 4
  | .parameter  => 5
  | .filler     => 6
  | .randomizer => 7

/-- Byte prefixed to every tweak, separating this protocol from another. -/
def PROTOCOL_DOMAIN_SEP : UInt8 := 0

/-! ## Chain positions -/

/-- Where one chain step sits among all the chain steps of one epoch.

Chain `i` step `k` takes position `CHAIN_LENGTH * i + k`.

The argument types bound the domain, so no two steps of an epoch collide. -/
def chainPosition (chain : Fin V) (step : Fin CHAIN_LENGTH) : UInt32 :=
  -- One block of CHAIN_LENGTH positions per chain, the step indexing inside it.
  UInt32.ofNat (CHAIN_LENGTH * chain.val + step.val)

/-! ## The tweak -/

/-- The label naming one hash call.

Both numbers are little-endian, and the reserved bytes are zero:

```text
byte  0      protocol domain separator
byte  1      tweak type
bytes 2-3    zero
bytes 4-7    sub-position
bytes 8-11   zero
bytes 12-15  index
```

What the numbers count, per tweak type:

```text
                     sub-position       index
secret derivation    chain number       epoch
chain step           chain position     epoch
leaf                 0                  epoch
Merkle parent        tree level         node index
encoding             0                  epoch
public parameter     0                  0
filler node          tree level         node index
randomizer           attempt number     epoch
```

For `makeTweak .chain 3 5`: byte 1 is 1, byte 4 is 3, byte 12 is 5.

Every other byte is zero.
-/
def makeTweak (tweakType : TweakType) (subPosition index : UInt32) : Tweak :=
  -- Reuses the little-endian serializer BLAKE2s already defines.
  #v[PROTOCOL_DOMAIN_SEP, tweakType.toByte, 0, 0]
    ++ Blake2s.Internal.wordBytes subPosition
    ++ (#v[0, 0, 0, 0] : Vector UInt8 4)
    ++ Blake2s.Internal.wordBytes index

/-! ## The tweakable hash -/

/-- The bytes one call hashes: tweak, then parameter, then payload. -/
def tweakInput (pp : PublicParam) (tweakType : TweakType)
    (subPosition index : UInt32) (payload : ByteArray) : ByteArray :=
  -- Fixed-length prefixes, and BLAKE2s binds the length: this splits one way.
  packBytes (makeTweak tweakType subPosition index) ++ packBytes pp ++ payload

/-- Hash a payload under one call site of one key, keeping the whole digest.

Most callers keep a prefix: a digest, or a randomizer. -/
def tweakHashFull (pp : PublicParam) (tweakType : TweakType)
    (subPosition index : UInt32) (payload : ByteArray) : Vector UInt8 32 :=
  Blake2s.hash (tweakInput pp tweakType subPosition index payload)

/-- Hash a payload under one call site of one key.

The result is the first half of a BLAKE2s-256 digest.
-/
def tweakHash (pp : PublicParam) (tweakType : TweakType)
    (subPosition index : UInt32) (payload : ByteArray) : Digest :=
  (tweakHashFull pp tweakType subPosition index payload).take DIGEST_LEN

end EthCryptographySpecs.Xmss
