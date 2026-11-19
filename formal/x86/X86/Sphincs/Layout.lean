module

public import X86.Bytes
public import X86.Context
public import Statement.LeanSphincs

/-!
# leanSPHINCS's input words

The input area of `X86.Context` holds the public key, the message and the signature as 977 words:
a 128-bit value as two words, low first (`digestLo`, `digestHi`); the message as four, low first;
a counter as one.

| words | hold |
|---|---|
| `0, 1` | `PK.seed` |
| `2, 3` | `PK.root` |
| `4 .. 7` | the message |
| `8, 9` | the randomizer `R` |
| `10 + 22 κ ..` | FORS tree `κ`'s opening: the secret (2 words), the path's height `z` at `2 + 2 z` (10 heights) |
| `538`, `683`, `828` | layer `0`, `1`, `2`'s signature: the counter (1 word), chain `i` at `1 + 2 i` (64 chains), the path's level `j` at `129 + 2 j` (8, 8, 10 levels) |
-/

@[expose] public section

namespace X86.SphincsVerifier

open _root_.Sphincs HashSig

/-- The input's words. -/
def inputWords : Nat := 977

/-- Where FORS tree `κ`'s opening starts. -/
def forsOff (κ : Nat) : Nat := 10 + 22 * κ

/-- Where layer `l`'s signature starts. -/
def layerOff (l : Nat) : Nat := 538 + 145 * l

/-- Word `k` of a 128-bit value: `0` the low word, `1` the high. -/
def digestWord (d : BitVec 128) (k : Nat) : UInt64 := if k = 0 then X86.digestLo d else X86.digestHi d

/-- Word `k < 22` of a FORS tree's opening. -/
def forsWord (o : ForsTreeOpening) (k : Nat) : UInt64 :=
  if k < 2 then digestWord o.secret k
  else if h : k < 22 then digestWord (o.path ⟨(k - 2) / 2, by unfold forsTreeHeight; omega⟩) (k % 2)
  else 0

/-- Word `k` of layer `l`'s signature. -/
def layerWord {l : Layer} (ls : LayerSignature l) (k : Nat) : UInt64 :=
  if k = 0 then ls.counter.toNat.toUInt64
  else if h : k < 129 then digestWord (ls.chainValues ⟨(k - 1) / 2, by unfold chainCount; omega⟩) ((k - 1) % 2)
  else if h : k < 129 + 2 * layerHeight l then
    digestWord (ls.authenticationPath ⟨(k - 129) / 2, by omega⟩) ((k - 129) % 2)
  else 0

/-- Word `i` of the input. -/
def encode (pk : _root_.Sphincs.PublicKey) (message : Message) (sig : Signature) (i : Nat) : UInt64 :=
  if i < 2 then digestWord pk.publicSeed i
  else if i < 4 then digestWord pk.root (i - 2)
  else if i < 8 then X86.word256 message (i - 4)
  else if i < 10 then digestWord sig.randomizer (i - 8)
  else if h : i < layerOff 0 then
    forsWord (sig.forsOpening ⟨(i - 10) / 22, by unfold forsTreeCount; unfold layerOff at h; omega⟩)
      ((i - 10) % 22)
  else if i < layerOff 1 then layerWord (sig.layers 0) (i - layerOff 0)
  else if i < layerOff 2 then layerWord (sig.layers 1) (i - layerOff 1)
  else if i < inputWords then layerWord (sig.layers 2) (i - layerOff 2)
  else 0

end X86.SphincsVerifier
