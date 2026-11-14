/-
  LeanVM.Protocol.Verifier

  The leanVM verifier (`Statement.LeanVmVerifier`) on its files: decoding the bytecode, the public
  input and the scalar stream.
-/

module

public import Statement.LeanVmVerifier
public import LeanVM.Facts.Verifier
public import Statement.Fast.Keccak
public import Statement.Fast.QuadExt
public import Statement.Fast.FieldWords

/-!
# The verifier on its files

The verifier is `Statement.LeanVmVerifier`. This module adds the decoders `lake exe leanvm-verify`
and `lake exe leanvm-prove` need to run it on the files the Rust prover's proofs are written to
(`scripts/export-verifier-fixtures-rust.sh`).
-/

namespace LeanVM.Protocol.Verifier

open LeanVM.Parameters

@[expose] public section

open LeanVM.Semantics LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile

/-!
## Decoding the files

* `bytecode.bin`: the bytecode table, 8 little-endian bytes per `K` word (`decodeWords`);
* `public_input.bin`: the 32 bytes of the public input digest (`decodeDigest`);
* `stream.bin`: the scalar stream, 16 bytes per `E` element, its two limbs in order
  (`decodeScalars`).

The Merkle openings are read by `leanvm-verify` (`readPhasesFile`) or from the wire encoding
(`Proof.fromBytes`, `LeanVM.Wire.Encoding`).
-/

/-! ### Words -/

/-- The 64-bit word of eight little-endian bytes. -/
def laneOfBytes (b : Bytes) : UInt64 :=
  UInt64.ofNat ((List.range 8).foldr (fun i acc ↦ (b.getD i 0).toNat + 256 * acc) 0)

/-- Read `n` values of `size` bytes each with `decode`, and the bytes after them; `none` if the
bytes run out (checked on the next `size` bytes, not on the length of all the rest). -/
def readMany {α : Type} (size : ℕ) (decode : Bytes → α) : ℕ → Bytes → Option (List α × Bytes)
  | 0, b => some ([], b)
  | n + 1, b =>
    if (b.take size).length = size then
      (readMany size decode n (b.drop size)).map fun r ↦ (decode (b.take size) :: r.1, r.2)
    else none

/-- The `K` word of eight little-endian bytes. -/
def kOfBytes (b : Bytes) : K := K.ofLane (laneOfBytes b)

/-- The digest of 32 bytes, its four words little-endian. -/
def digestOfBytes (b : Bytes) : Digest :=
  Vector.ofFn fun j : Fin 4 ↦ laneOfBytes (b.drop (8 * j))

/-- The scalar of 16 bytes, two little-endian limbs. -/
def eOfBytes (b : Bytes) : E := E.ofLimbs (kOfBytes b) (kOfBytes (b.drop 8))

/-! ### The files -/

/-- Read exactly the whole of a byte string as values of `size` bytes. -/
def decodeAll {α : Type} (size : ℕ) (decode : Bytes → α) (b : Bytes) : Option (List α) :=
  match readMany size decode (b.length / size) b with
  | some (xs, []) => some xs
  | _ => none

/-- `bytecode.bin`: the bytecode's words. -/
def decodeWords (b : Bytes) : Option (List K) := decodeAll 8 kOfBytes b

/-- `public_input.bin`: the 32-byte public input. -/
def decodeDigest (b : Bytes) : Option Digest :=
  if b.length = 32 then some (digestOfBytes b) else none

/-- `stream.bin`: the scalars. -/
def decodeScalars (b : Bytes) : Option (List E) := decodeAll 16 eOfBytes b

end
end LeanVM.Protocol.Verifier
