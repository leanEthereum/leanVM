import LeanVM.Guest.Value.All

/-!
# Tests: chains over cells and Fiat-Shamir

Compiled checks (`#guard`) of `LeanVM.Guest.Value.Hash` and `LeanVM.Guest.Value.FiatShamir`: a
two-block chain over cells against `blake2sBytes` (and a wrong counter, a wrong flag), the empty
input, one block under the default IV, and the Fiat-Shamir blocks against `Node.observe` and
`Node.squeeze` (and a wrong top limb, a wrong tag).
-/

namespace LeanVMTests.Guest.Value

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Blake2sHash
open LeanVM.Protocol.Compile LeanVM.Protocol.Verifier LeanVM.Guest.Value

/-! ## Chains over cells -/

/-- The cell of sixteen bytes, little-endian. -/
def cellOf (b : List UInt8) : E :=
  let le := fun (c : List UInt8) ↦ c.foldr (fun x acc ↦ x.toNat + 256 * acc) 0
  E.ofLimbs (K.ofBits (le (b.take 8))) (K.ofBits (le ((b.drop 8).take 8))) 0

/-- The block of four cells of 64 bytes. -/
def blockOf64 (b : List UInt8) : Fin 4 → E :=
  ![cellOf (b.take 16), cellOf ((b.drop 16).take 16), cellOf ((b.drop 32).take 16),
    cellOf ((b.drop 48).take 16)]

/-- What `BLAKE2S` writes: the output cells of a compression. -/
def compressCellsOut (m : Fin 4 → E) (cv : E × E) (md : E) : E × E :=
  digestScalars (compress (cellWords cv.1 ++ cellWords cv.2) (messageWords m)
    (unpackMetadata md).1 (unpackMetadata md).2.1 (unpackMetadata md).2.2)

/-- The bytes `0, 1, …, n - 1`. -/
def ramp (n : ℕ) : List UInt8 := (List.range n).map Nat.toUInt8

#guard blockBytes (blockOf64 (ramp 64)) = ramp 64

/-- An 80-byte message as two blocks, the second zero-filled (the `zkDSL.md` example). -/
def two : E × E :=
  compressCellsOut (blockOf64 ((ramp 80).drop 64 ++ List.replicate 48 0))
    (compressCellsOut (blockOf64 ((ramp 80).take 64)) ivCells (metadataCell 64 false))
    (metadataCell 80 true)

#guard two = digestScalars (blake2sBytes (ramp 80))
-- Mutations: the final counter one short, and the first block flagged final.
#guard compressCellsOut (blockOf64 ((ramp 80).drop 64 ++ List.replicate 48 0))
    (compressCellsOut (blockOf64 ((ramp 80).take 64)) ivCells (metadataCell 64 false))
    (metadataCell 79 true) ≠ digestScalars (blake2sBytes (ramp 80))
#guard compressCellsOut (blockOf64 ((ramp 80).drop 64 ++ List.replicate 48 0))
    (compressCellsOut (blockOf64 ((ramp 80).take 64)) ivCells (metadataCell 64 true))
    (metadataCell 80 true) ≠ digestScalars (blake2sBytes (ramp 80))
-- The empty input: one zero block at counter 0, final.
#guard compressCellsOut ![0, 0, 0, 0] ivCells (metadataCell 0 true) = digestScalars (blake2sBytes [])
-- One block under the default IV.
#guard compressCellsOut (blockOf64 (ramp 64)) ivCells (metadataCell 64 true) =
  digestScalars (blake2sBytes (ramp 64))
-- `CompressCells` holds of the honest output and checks the canonicity of every cell.
#guard decide (CompressCells (blockOf64 (ramp 64)) ivCells.1 ivCells.2
  (compressCellsOut (blockOf64 (ramp 64)) ivCells (metadataCell 64 true)).1
  (compressCellsOut (blockOf64 (ramp 64)) ivCells (metadataCell 64 true)).2 (metadataCell 64 true))

/-! ## Fiat-Shamir -/

/-- A state. -/
def cv : Digest := blake2sBytes [1, 2, 3]

/-- A full word. -/
def w : E := E.ofLimbs (K.ofBits 0x1111) (K.ofBits 0x2222) (K.ofBits 0x3333)

#guard digestBytes cv = cellBytes (digestScalars cv).1 ++ cellBytes (digestScalars cv).2
#guard (digestScalars cv).1 + y * y * ofK ((digestScalars cv).2.limb 0) = challengeOf cv
-- `fs_compress` with the honest top limb is the absorb of `blockOf w 1` ...
#guard compressCellsOut (fsBlock (digestScalars cv) w (ofK (w.limb 2)) (eOfNat 1)) ivCells
    (metadataCell 64 true) = digestScalars (LeanVM.Node.observe w cv).2
-- ... and with a wrong one its cell is not canonical, which `BLAKE2S` rejects.
#guard ¬ decide (CompressCells (fsBlock (digestScalars cv) w (ofK 0) (eOfNat 1)) ivCells.1
  ivCells.2 0 0 (metadataCell 64 true))
-- `squeeze_state` is `Node.squeeze`'s state; another tag is not.
#guard compressCellsOut ![(digestScalars cv).1, (digestScalars cv).2, 0, y * eOfNat 2] ivCells
    (metadataCell 64 true) = digestScalars (LeanVM.Node.squeeze cv).2
#guard compressCellsOut ![(digestScalars cv).1, (digestScalars cv).2, 0, y * eOfNat 3] ivCells
    (metadataCell 64 true) ≠ digestScalars (LeanVM.Node.squeeze cv).2
-- `powOk` at zero bits wants the zero nonce.
#guard powOk 0 0 cv
#guard !powOk 0 1 cv

end LeanVMTests.Guest.Value
