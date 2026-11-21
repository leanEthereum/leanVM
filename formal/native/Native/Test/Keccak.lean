import Native.Test.Run
import Native.Keccak

/-!
# `Keccak.hash` against `keccak256`

The code's digest equals `keccak256` of the words' bytes at lengths around the block boundaries,
with and without a partial last word.
-/

namespace Native.Test.KeccakTest

open LeanVM.Protocol.KeccakHash

/-- `n` words of test data, the bytes past `len` zero. -/
def data (len : Nat) : List UInt64 :=
  (List.range ((len + 7) / 8)).map fun i ↦
    let w := (i * 0x9e3779b97f4a7c15 + 0x0123456789abcdef).toUInt64
    if 8 * (i + 1) ≤ len then w else w &&& ((1 <<< (8 * (len % 8)).toUInt64) - 1)

def base : UInt64 := 0x1000
def input : UInt64 := 0x100000

/-- The code's digest of the first `len` bytes of `data len`. -/
def run (len : Nat) : Option (List UInt64) := do
  let ws := data len
  let s := RState.ofWords base <|
    (List.range Keccak.scratchWords).map (fun k ↦ (base + (8 * k).toUInt64, 0)) ++
    (List.range ws.length).map (fun i ↦ (input + (8 * i).toUInt64, ws.getD i 0))
  let s := { s with regs := (s.regs.set! (regIdx .rsi) input).set! (regIdx .rbx) len.toUInt64 }
  match ← Native.Test.run 100000 Keccak.hash s with
  | (.ok s, _) => some ((List.range 4).map fun k ↦ s.word (base + (8 * k).toUInt64))
  | _ => none

def expected (len : Nat) : List UInt64 :=
  (keccak256 (((data len).flatMap wordBytes).take len)).toList

def agree (len : Nat) : Bool := run len == some (expected len)

#guard [0, 1, 7, 8, 64, 68, 84, 128, 135, 136, 137, 143, 144, 271, 272, 280, 960, 1072].all agree

end Native.Test.KeccakTest
