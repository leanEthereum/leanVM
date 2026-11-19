module

public import X86.Keccak.Words

/-!
# leanXMSS verification on words

The model `verifyW` of `XmssVerifier.body`: leanXMSS verification on the input's words
(`XmssVerifier.encode`), a digest as two words, low first (`W2`), every hash `keccak256` of words
(`hashW`). Its steps are the code's: the addresses as the code computes them (`tweakW`,
`nodeTweakW`), the digits as it shifts them out of the digest (`shiftW`), the chains, the leaf and
the path in the order it hashes them. `X86.Xmss.ModelSpec` proves it equal to
`LeanXmss.verifyWithKeccak`.
-/

@[expose] public section

namespace X86.XmssVerifier

open LeanVM.Protocol.KeccakHash Keccak

/-- A digest as two words, low first. -/
abbrev W2 := UInt64 × UInt64

/-- The first two lanes of `keccak256` of the words' bytes. -/
def hashW (ws : List UInt64) : W2 :=
  ((keccak256 (wordsBytes ws))[0], (keccak256 (wordsBytes ws))[1])

/-- The address word of layer `l`, key `e` and type byte `b`. -/
def tweakW (l e b : UInt64) : UInt64 := ((l <<< 55) ||| e) ||| (b <<< 56)

/-- The address word of a node of layer `l` at level `j`, index `k`. -/
def nodeTweakW (l j k : UInt64) : UInt64 :=
  ((((l <<< 23) + j) <<< 32) ||| k) ||| ((3 : UInt64) <<< 56)

/-- The step of chain `i` leaving position `t`. -/
def chainStepW (P : W2) (l e i : UInt64) (t : Nat) (v : W2) : W2 :=
  hashW [P.1, P.2, tweakW l e ((t.toUInt64 <<< 5) + 1), 0, v.1, v.2, i, 0]

/-- `k` steps from position `d`, the one leaving position `t` being `f t`. -/
def walkW (f : Nat → W2 → W2) (d : Nat) : Nat → W2 → W2
  | 0, v => v
  | k + 1, v => f (d + k) (walkW f d k v)

/-- The digest shifted right to digit `i`, in the word that holds it. -/
def shiftW (D : W2) (i : Nat) : UInt64 :=
  if i < 32 then D.1 >>> (2 * i).toUInt64 else D.2 >>> (2 * (i - 32)).toUInt64

/-- Digit `i` of a digest, base 4, little endian. -/
def digitW (D : W2) (i : Nat) : UInt64 := shiftW D i &&& 3

/-- The sum of the first `n` digits. -/
def digitSumW (D : W2) : Nat → UInt64
  | 0 => 0
  | i + 1 => digitSumW D i + digitW D i

/-- A codeword: the last six digits zero, the first 58 summing to `106`. -/
def codewordW (D : W2) : Bool := D.2 >>> 52 == 0 && digitSumW D 58 == 106

/-- The words of `n` digests. -/
def pairWords (n : Nat) (f : Nat → W2) : List UInt64 :=
  (List.range n).flatMap fun i ↦ [(f i).1, (f i).2]

/-- The node above level `j` of key `e`'s path, from the node `cur` at level `j`. -/
def nodeW (P : W2) (l e : UInt64) (path : Nat → W2) (j : Nat) (cur : W2) : W2 :=
  let k := e >>> j.toUInt64
  hashW ([P.1, P.2, nodeTweakW l (j + 1).toUInt64 (k >>> 1), 0] ++
    if k &&& 1 = 0 then [cur.1, cur.2, (path j).1, (path j).2]
    else [(path j).1, (path j).2, cur.1, cur.2])

/-- The node at level `j` of key `e`'s path, from its leaf. -/
def foldW (P : W2) (l e : UInt64) (path : Nat → W2) : Nat → W2 → W2
  | 0, v => v
  | j + 1, v => nodeW P l e path j (foldW P l e path j v)

/-- The message digest of the words `msg` under key `e` of layer `l`, randomizer `R`. -/
def msgDigestW (P : W2) (l e : UInt64) (msg : List UInt64) (R : W2) : W2 :=
  hashW ([P.1, P.2, tweakW l e 12, 0] ++ msg ++ [R.1, R.2])

/-- The end of chain `i` under the digest `D`, from the signature's value `v`. -/
def chainEndW (P : W2) (l e : UInt64) (D : W2) (i : Nat) (v : W2) : W2 :=
  walkW (chainStepW P l e i.toUInt64) (digitW D i).toNat (3 - (digitW D i).toNat) v

/-- The leaf of key `e`: the hash of its chain ends. -/
def leafW (P : W2) (l e : UInt64) (ends : Nat → W2) : W2 :=
  hashW ([P.1, P.2, tweakW l e 2, 0] ++ pairWords 58 ends)

/-- Layer `l`'s signature, its word `k` being `sw k`, by key `e` of the words `msg`: whether its
digest is a codeword, and the root it reaches. -/
def layerW (P : W2) (l e : UInt64) (msg : List UInt64) (sw : Nat → UInt64) : Bool × W2 :=
  let D := msgDigestW P l e msg (sw 0, sw 1)
  let ends := fun i ↦ chainEndW P l e D i (sw (2 + 2 * i), sw (3 + 2 * i))
  (codewordW D, foldW P l e (fun j ↦ (sw (118 + 2 * j), sw (119 + 2 * j))) 16 (leafW P l e ends))

/-- The first `n` layers of the input `inp`: whether every digest was a codeword, and the last
root. The bottom layer signs the message, the top layer the bottom root. -/
def afterLayers (inp : Nat → UInt64) : Nat → Bool × W2
  | 0 => (true, (0, 0))
  | n + 1 =>
    let prev := afterLayers inp n
    let r := layerW (inp 2, inp 3) n.toUInt64 (inp 8 >>> (16 * n).toUInt64)
      (if n = 0 then [inp 4, inp 5, inp 6, inp 7] else [prev.2.1, prev.2.2])
      (fun k ↦ inp (9 + 150 * n + k))
    (prev.1 && r.1, r.2)

/-- **leanXMSS verification on the input's words.** -/
def verifyW (inp : Nat → UInt64) : Bool :=
  (afterLayers inp 2).1 && (afterLayers inp 2).2 == (inp 0, inp 1)

end X86.XmssVerifier
