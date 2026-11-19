module

public import X86.Bytes
public import X86.Context
public import Statement.LeanXmss

/-!
# leanXMSS's input words

The input area of `X86.Context` holds the public key, the message and the signature as 309 words:
a 128-bit value as two words, low first (`digestLo`, `digestHi`); the message as four, low first;
the leaf index as one.

| words | hold |
|---|---|
| `0, 1` | the root |
| `2, 3` | the public parameter `P` |
| `4 .. 7` | the message |
| `8` | the leaf index |
| `9 + 150 l ..` | layer `l`'s signature: the randomizer (2 words), chain `i` at `2 + 2 i` (58 chains), the path's level `j` at `118 + 2 j` (16 levels) |
-/

@[expose] public section

namespace X86.XmssVerifier

open LeanXmss HashSig

/-- The input's words. -/
def inputWords : Nat := 309

/-- The words of a layer's signature. -/
def layerWords : Nat := 150

/-- Word `k` of a 128-bit value: `0` the low word, `1` the high. -/
def digestWord (d : BitVec 128) (k : Nat) : UInt64 := if k = 0 then digestLo d else digestHi d

/-- Word `k < 150` of a layer's signature. -/
def layerWord (ls : LayerSignature) (k : Nat) : UInt64 :=
  if k < 2 then digestWord ls.randomizer k
  else if h : k < 118 then digestWord (ls.chainValues ⟨(k - 2) / 2, by unfold chainCount; omega⟩) (k % 2)
  else if h : k < 150 then
    digestWord (ls.authenticationPath ⟨(k - 118) / 2, by unfold layerHeight; omega⟩) (k % 2)
  else 0

/-- Word `i` of the input. -/
def encode (pk : PublicKey) (message : Message) (sig : Signature) (i : Nat) : UInt64 :=
  if i < 2 then digestWord pk.root i
  else if i < 4 then digestWord pk.parameter (i - 2)
  else if i < 8 then word256 message (i - 4)
  else if i = 8 then sig.leafIndex.val.toUInt64
  else if h : i < 9 + 2 * layerWords then
    layerWord (sig.layers ⟨(i - 9) / layerWords, by unfold layerCount layerWords at *; omega⟩)
      ((i - 9) % layerWords)
  else 0

end X86.XmssVerifier
