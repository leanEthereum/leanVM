import Rv64mc.Model

/-!
# The mirrors on the Rust's test vectors

Executable checks of the mirrors against the vectors of `crates/verifier`'s own tests:
`field.rs`'s `K_VECTORS` and `E_VECTORS` (`(a, b, a * b, a * a, a^-1)`), `Scaled` against the
product, `hash.rs`'s `VECTORS` (Keccak-256 of `00 01 ..`), and `multilinear.rs`'s
`stack_offsets` sizes against the statement's `stackOffsets`. Evaluated by the interpreter.
-/

namespace Rv64mc.Model.Tests

open Rv64mc.Model

/-- `(a, b, a * b)` of `K_VECTORS`. -/
def kVectors : List (BitVec 64 × BitVec 64 × BitVec 64) := [
  (0x01090913877ed8ed#64, 0x66ab35ac2768468f#64, 0x50c4519dc383744a#64),
  (0xa7715ae18f12a3b5#64, 0x05743059f43fa4f5#64, 0xeb64cd9cd9cda6df#64),
  (0xbd3efb4705e79ddd#64, 0x3aff618604de4ae0#64, 0xc3d7a95fa9cb59bb#64)]

#guard kVectors.all fun (a, b, c) ↦ baseMul a b == c

#guard kVectors.all fun (a, _, _) ↦ baseMul a (kInv a) == 1#64

#guard kInv 0#64 == 0#64

/-- `(a, b, a * b, a * a, a^-1)` of `E_VECTORS`. -/
def eVectors : List (Limbs × Limbs × Limbs × Limbs × Limbs) := [
  ((0x8a1d921ca352a3c3#64, 0xa10d04b240699a83#64), (0x936d4747ab0e6d1c#64, 0xe46ab5adb68f9c7d#64),
    (0xfbbffa3000b331c0#64, 0xbf494d14ce4eadf8#64), (0x3eb21e43df9bbb1c#64, 0x7836265481e5ee7d#64),
    (0x4dbcb8833d2c881c#64, 0x01d5fd8ef4de46b1#64)),
  ((0x4ced30628e0cd071#64, 0xc694494e11044370#64), (0x079184601cbc456d#64, 0xc2b90e2d4a7acb31#64),
    (0x1df92a5bbf394f60#64, 0x4f9871091371b5d2#64), (0x87f8c19a80de6b2b#64, 0xe1b7b5434dbf44ba#64),
    (0xe5886c008822ac39#64, 0x5014981d45105c3b#64)),
  ((0x1f7678795f345ff4#64, 0xd584a285e92195e8#64), (0xa4fab233b7895f8e#64, 0xe8c4546870efc3e0#64),
    (0x39944740fab79b32#64, 0x677a979829fc8fea#64), (0x33bf067a3def0161#64, 0x7dd98b6fdaf72b54#64),
    (0x126bd1f8da56668e#64, 0xf1e4a54eaa0dc2d0#64)),
  ((0xf8a7e4e12a61d563#64, 0x852495966643d5c8#64), (0x5b2495d1eb090346#64, 0x786d6f68d7273a2f#64),
    (0x6617b862c301fca8#64, 0x1edae1e051362791#64), (0xd03dc472c71a8299#64, 0xab7efb6717791597#64),
    (0x36a2e97ec7233d69#64, 0xb5f24753a7ede4d1#64))]

#guard eVectors.all fun (a, b, c, s, i) ↦ eMul a b == c && eSquare a == s && eInv a == i

#guard eVectors.all fun (a, _, _, _, _) ↦ ePow a 5#64 == eMul (eSquare (eSquare a)) a

#guard eVectors.all fun (a, b, _, _, _) ↦
  [b, (0#64, 1#64), eOne, eZero, (BitVec.allOnes 64, BitVec.allOnes 64)].all fun v ↦
    scaledMul (scaledNew a) v == eMul v a

-- `y * y = E::new(1, 2)`
#guard eMul (0#64, 1#64) (0#64, 1#64) == (1#64, 2#64)

/-- A byte string's lowercase hex. -/
def hex (bytes : List (BitVec 8)) : String := String.join (bytes.map BitVec.toHex)

/-- The bytes `00 01 ..` (mod 256), `n` of them. -/
def counting (n : ℕ) : List (BitVec 8) := (List.range n).map (BitVec.ofNat 8)

#guard hex (keccakHashRust (counting 0)) ==
  "c5d2460186f7233c927e7db2dcc703c0e500b653ca82273b7bfad8045d85a470"

#guard hex (keccakHashRust (counting 135)) ==
  "cbdfd9dee5faad3818d6b06f95a219fd290b0e1706f6a82e5a595b9ce9faca62"

#guard hex (keccakHashRust (counting 136)) ==
  "7ce759f1ab7f9ce437719970c26b0a66ff11fe3e38e17df89cf5d29c7d7f807e"

#guard hex (keccakHashRust (counting 272)) ==
  "fdf2ec49e749960d3c8521a0219af8d03e30e2b3bf19bd16150ee0eaf133d66e"

/-- `stack_offsets_place_largest_first_ties_by_index`'s sizes. -/
def stackSizes : List (List ℕ) := [[], [0], [3, 5, 3, 0, 5, 1, 7, 1], [2, 2, 2]]

#guard stackSizes.all fun sizes ↦
  ((stackOffsetsRust sizes).1.map BitVec.toNat, (stackOffsetsRust sizes).2) ==
    LeanVM.Protocol.Verifier.stackOffsets sizes

end Rv64mc.Model.Tests
