import LeanVM.Spec.Fast.Hash

/-!
# Tests: BLAKE2s as the verifier compiles it

`LeanVM.Spec.Fast.Hash` compiles `blake2sBytes` as `blake2sBytesWords`, with the
rotation on `UInt32` and the block read from an array; the equalities are theorems. The compiled
checks run the restated hash on digests of CPython's `hashlib.blake2s` (the empty message,
`"abc"` of RFC 7693 Appendix B, and a 200-byte ramp, four blocks with a short last one), with
one mutated digest, and the word rotation on its edges: a zero amount, a full turn, an amount
past it, and a wrapped top bit. The kernel checks compare the word rotation and the array-read
block with the definitions they replace, independently of the compiler.
-/

namespace LeanVMTests.Protocol.Verifier.FastHash

open LeanVM.Semantics LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Verifier.Fast

/-- The bytes `0, 1, …, n - 1`, modulo `256`. -/
def ramp (n : ℕ) : List UInt8 := (List.range n).map Nat.toUInt8

/-! ## Digests -/

#guard (blake2sBytesWords []).toList =
  [0x307a2169, 0x94809079, 0xd02111e1, 0x7c4a3542, 0x48b6551f, 0x1ea5a12c, 0xfd0d251b, 0xf9eed01e]
#guard (blake2sBytesWords "abc".toUTF8.toList).toList =
  [0x8c5e8c50, 0xe2147c32, 0xa32ba7e1, 0x2f45eb4e, 0x208b4537, 0x293ad69e, 0x4c9b994d, 0x82596786]
#guard (blake2sBytesWords (ramp 200)).toList =
  [0x1a4e246d, 0xf54ece06, 0x630fdd78, 0x6793f0af, 0x19517306, 0x228d9cca, 0x14806cd8, 0x4197ab14]
-- Mutation: the last word off by one.
#guard (blake2sBytesWords (ramp 200)).toList ≠
  [0x1a4e246d, 0xf54ece06, 0x630fdd78, 0x6793f0af, 0x19517306, 0x228d9cca, 0x14806cd8, 0x4197ab15]

/-! ## The rotation and the block -/

#guard rotrWords 0x12345678 8 = 0x78123456
#guard rotrWords 0x12345678 7 = 0xf02468ac
#guard rotrWords 0x12345678 0 = 0x12345678
#guard rotrWords 0x12345678 32 = 0x12345678
#guard rotrWords 0x12345678 39 = 0xf02468ac
#guard rotrWords 0x80000001 1 = 0xc0000000

/-- The word rotation is `Blake2s.rotr` in the kernel, at BLAKE2s's four amounts and at zero. -/
example : [16, 12, 8, 7, 0].map (rotrWords 0x9b05688c) =
    [16, 12, 8, 7, 0].map (Blake2s.rotr 0x9b05688c) := by
  decide +kernel

/-- The array-read block is `blockWords` in the kernel, on a block shorter than `64` bytes. -/
example : (blockWordsArray (ramp 50)).toList = (blockWords (ramp 50)).toList := by
  decide +kernel

end LeanVMTests.Protocol.Verifier.FastHash
