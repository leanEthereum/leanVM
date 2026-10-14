import WhirAeneas.Hash.Interface
import LeanVMCircuits.Rec.Statement

namespace WhirAeneas.Hash
open Aeneas Aeneas.Std

abbrev Digest := Aeneas.Std.Array U8 32#usize
abbrev Pair := Aeneas.Std.Array Digest 2#usize

def blockWords (bytes : List (BitVec 8)) (block : Nat) : Vector Word 16 :=
  Vector.ofFn fun i =>
    let offset := 64 * block + 4 * i.val
    BitVec.ofNat 32 ((bytes.getD offset 0).toNat +
      256 * (bytes.getD (offset + 1) 0).toNat +
      65536 * (bytes.getD (offset + 2) 0).toNat +
      16777216 * (bytes.getD (offset + 3) 0).toNat)

/-- The shared RFC block-chain specification, with little-endian decoding and the mandatory empty-message block. No second compression definition is introduced. -/
def hashBytes (bytes : List (BitVec 8)) : Vector Word 8 :=
  let blocks := max 1 ((bytes.length + 63) / 64)
  LeanVMCircuits.Rec.blake2s256 (BitVec.ofNat 64 bytes.length) (blockWords bytes 0)
    ((List.range (blocks - 1)).map fun i => blockWords bytes (i + 1))

def digestWords (digest : Digest) : Vector Word 8 :=
  Vector.ofFn fun i =>
    let offset := 4 * i.val
    BitVec.ofNat 32 ((digest.val.getD offset 0#u8).val +
      256 * (digest.val.getD (offset + 1) 0#u8).val +
      65536 * (digest.val.getD (offset + 2) 0#u8).val +
      16777216 * (digest.val.getD (offset + 3) 0#u8).val)

/-- Each digest is exactly the RFC hash of the corresponding left-then-right pair. Equality of the entire ordered list also fixes output count, including an empty batch. Allocation success and ABI memory validity are separate runtime premises, not consequences of this content contract. -/
def SatisfiesHashPairs (hashPairs : Slice Pair → Result (Aeneas.Std.alloc.vec.Vec Digest)) : Prop :=
  ∀ pairs, 32 * pairs.val.length ≤ Usize.max →
    ∃ outputs, hashPairs pairs = .ok outputs ∧
      outputs.val.map digestWords = pairs.val.map (fun pair =>
        hashBytes ((pair.val.flatMap (fun digest => digest.val)).map (fun byte => byte.bv)))

/-- The single-image hash contract is total successful RFC hashing on representable input lengths. It assumes neither Merkle validity nor any verifier acceptance property. -/
def SatisfiesHashBytes (hash : Slice U8 → Result Digest) : Prop :=
  ∀ input, input.val.length < 2 ^ 64 →
    ∃ output, hash input = .ok output ∧
      digestWords output = hashBytes (input.val.map (fun byte => byte.bv))

end WhirAeneas.Hash
