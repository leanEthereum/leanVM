module

public import Gf2.Blake2s
meta import Gf2.Blake2s

/-!
The BLAKE2s circuit against reference vectors, through Clean witness generation: the output bits
the circuit witnesses equal both the native `compress` and values computed by Rust's
`flock::hash::blake2s_compress(h, m, 64, 0xFFFFFFFF, 0)`, and every constraint holds. The block
also fits `2^14` rows and columns once the Rust side reserves whole 64-bit words for the constant
and the public bits.
-/

namespace Gf2.Blake2s.Check

/-- Columns the Rust side reserves for the constant, the public bits and zero padding. -/
def reserved : ℕ := 64 * ((nPublic + 1 + 63) / 64)

example : reserved + nPrivate ≤ 2 ^ 14 ∧ (rowsAt 0).1.size ≤ 2 ^ 14 := by
  native_decide

/-- Witness of one instance with inputs `h`, `m`. -/
def witness (h m : Array UInt32) : List (Operation F) × Array F :=
  (ops, witgen (inputHint (inputBits h m)) ops)

/-- The output words the circuit witnesses and the number of violated constraints. -/
def run (h m : Array UInt32) : Array UInt32 × ℕ :=
  let (ops, w) := witness h m
  (Array.ofFn (n := 8) fun i => readWord (fun j => w[j]?.getD 0) 768 i.val, countViolations ops w)

/-- Agreement of the circuit with the native reference and the Rust value, all constraints holding. -/
def check (h m expected : Array UInt32) : Bool :=
  run h m == (expected, 0) && compress h m T F0 F1 == expected

/-- RFC 7693's BLAKE2s-256("abc") chaining value and block, compressed with the pinned flags. -/
def abcH : Array UInt32 := #[IV[0]! ^^^ 0x01010020] ++ IV.extract 1 8
def abcM : Array UInt32 := #[0x00636261] ++ Array.replicate 15 0

example : check abcH abcM
    #[0xD3D47540, 0x6A89A11B, 0xB26DA2C8, 0x65FF8B4E, 0x08F6F761, 0xF13C699E, 0x42004921, 0xB9EAEE8A] := by
  native_decide

example : check
    #[0x01234567, 0x12345678, 0x23456789, 0x3456789A, 0x456789AB, 0x56789ABC, 0x6789ABCD, 0x789ABCDE]
    #[0xDEADBEEF, 0xDCAFBCED, 0xD6A5B6E7, 0xC6B5A6F7, 0x9EEDFEAF, 0x7E0D1E4F, 0x5F2C3F6E, 0x5D2E3D6C,
      0xD6A5B6E7, 0xCCBFACFD, 0xF68596C7, 0x86F5E6B7, 0x1E6D7E2F, 0x7F0C1F4E, 0x5D2E3D6C, 0x592A3968]
    #[0x7582F140, 0xCF82E2E1, 0xCA7D9BAE, 0x458CD3A6, 0xE7CFA8A6, 0x08326E63, 0x3B081964, 0x16BFAC05] := by
  native_decide

example : check (Array.replicate 8 0xFFFFFFFF) (Array.replicate 16 0xFFFFFFFF)
    #[0x69AE926E, 0x36554C19, 0x1B505179, 0x16AB8EAE, 0x313F498D, 0x228E9B99, 0x72E57B80, 0x92FCFB8C] := by
  native_decide

/-- Violations after flipping one output bit of a valid witness: its pin row alone should break. -/
def flippedOutputViolations : ℕ :=
  let (ops, w) := witness abcH abcM
  countViolations ops (w.modify 800 (· + 1))

example : flippedOutputViolations = 1 := by
  native_decide

end Gf2.Blake2s.Check
