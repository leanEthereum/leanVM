module

public import Native.Sphincs.Words
public import Native.Bytes

/-!
# Hash word operations

Byte reversal and truncated Keccak hashes over words.
-/

@[expose] public section

namespace Native.SphincsVerifier

open Keccak LeanVM.Protocol.KeccakHash

/-- The four low bytes of `x` in reverse order. -/
def bs (x : UInt64) : UInt64 :=
  (x &&& 255) <<< 24 ||| ((x >>> 8) &&& 255) <<< 16 ||| ((x >>> 16) &&& 255) <<< 8 |||
    ((x >>> 24) &&& 255)

/-- `Trunc_16` of `keccak256` of the first `len` bytes of words. -/
def th (ws : List UInt64) (len : Nat) : BitVec 128 :=
  ofWords (keccak256 ((wordsBytes ws).take len))[0] (keccak256 ((wordsBytes ws).take len))[1]

end Native.SphincsVerifier
