module

public import Native.Keccak

/-!
# Words in memory and the bytes they hold

What `Keccak.hash`'s specification (`Native.Keccak.Spec`) speaks of: a run of words at an address
(`WordsAt`), the bytes it holds (`wordsBytes`, `HoldsBytes`) and the scratch area's words
(`scratchAddr`).
-/

@[expose] public section

namespace Native.Keccak

open LeanVM.Protocol.KeccakHash

/-- The little-endian bytes of words. -/
def wordsBytes (ws : List UInt64) : List UInt8 := ws.flatMap wordBytes

/-- The words hold `len` bytes: `⌈len / 8⌉` words, the bytes past `len` zero. -/
def HoldsBytes (ws : List UInt64) (len : Nat) : Prop :=
  ws.length = (len + 7) / 8 ∧ ∀ b ∈ (wordsBytes ws).drop len, b = 0

/-- The words `ws` at consecutive addresses from `a`. -/
def WordsAt (mem : UInt64 → Option UInt64) (a : UInt64) (ws : List UInt64) : Prop :=
  ∀ i (h : i < ws.length), mem (a + (8 * i).toUInt64) = some ws[i]

/-- The scratch area's word `k`. -/
def scratchAddr (base : UInt64) (k : Nat) : UInt64 := base + (8 * k).toUInt64

end Native.Keccak
