module

public import Statement.Keccak
public import Mathlib.Data.BitVec

/-!
# Words in memory and the bytes they hold

Words at an address (`WordsAt`), their bytes (`wordsBytes`, `HoldsBytes`) and word addresses
(`scratchAddr`).
-/

@[expose] public section

namespace Native.Keccak

open LeanVM.Protocol.KeccakHash

/-- The scratch area's words: `[rdi, rdi + 8 · scratchWords)`. -/
def scratchWords : Nat := 84

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
