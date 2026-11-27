import LeanSphincsProofs.Defs
import Keccak256Proofs.Bytes
import Keccak256Proofs.Path

/-!
# What the proofs share

`to_be_bytes` as the statement's big-endian bytes, and `th` at an address. The library models the
extraction calls and the arithmetic of bytes read as numbers, which leanXMSS's proofs use too, are
in `Keccak256Proofs` (`../keccak256`).
-/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM Std.Do
open HashSig HashSig.OverPermutation Sphincs
open LeanVM.Semantics (KeccakState)
open LeanVM.Protocol.KeccakHash (digestBytes keccak256With)
open lean_sphincs
open Keccak256Proofs

namespace LeanSphincsProofs

/-- **`u32::to_be_bytes` is the statement's `bigEndianBytes 4`.** -/
theorem bytes_u32_to_be_bytes (x : Std.U32) :
    bytes (Aeneas.Std.core.num.U32.to_be_bytes x).val = bigEndianBytes 4 x.bv := by
  have h : x.bv.toBEBytes = [x.bv.extractLsb' 24 8, x.bv.extractLsb' 16 8, x.bv.extractLsb' 8 8,
      x.bv.extractLsb' 0 8] := by
    simp [BitVec.toBEBytes, BitVec.toLEBytes]
    refine ⟨?_, ?_, ?_, ?_⟩ <;> bv_bits
  simp only [Aeneas.Std.core.num.U32.to_be_bytes, Array.from_val, h, bytes, List.map_cons,
    List.map_nil, b8]
  rfl

/-- `th` at a Rust address that holds the statement's `A`: the statement's addressed hash. -/
theorem th_adrs {π : KeccakState → KeccakState} (hth : ThSpec π) (seed : Array Std.U8 16#usize)
    (adrs : hash.Adrs) (A : Sphincs.Address) (m : Slice Std.U8) (hA : AdrsIs adrs A) :
    ∃ d, hash.th seed adrs m = ok d ∧
      toDigest d = Id.run (Verification.addressedHash (inId π) (toDigest seed) A (bytes m.val)) := by
  obtain ⟨d, hd, hdig⟩ := hth seed adrs m
  refine ⟨d, hd, ?_⟩
  rw [hdig, hA, ← littleEndianBytes_toDigest seed]
  rfl

/-- `th_digests`: the addressed hash of the digests' bytes, one after the other. -/
theorem th_digests_adrs {π : KeccakState → KeccakState} (hth : ThSpec π)
    (seed : Array Std.U8 16#usize) (a : hash.Adrs) (A : Sphincs.Address)
    (values : Slice (Array Std.U8 16#usize)) (hA : AdrsIs a A)
    (hlen : 16 * values.length ≤ Usize.max) :
    ∃ d, hash.th_digests seed a values = ok d ∧
      toDigest d = Id.run (Verification.addressedHash (inId π) (toDigest seed) A
        (bytes ((values.val.map Array.val).flatten))) := by
  have hflat : ((values.val.map Array.val).flatten).length ≤ Usize.max := by
    rw [flat_length]; exact hlen
  obtain ⟨d, hd, hval⟩ := th_adrs hth seed a A (Slice.from _ hflat) hA
  refine ⟨d, ?_, ?_⟩
  · unfold hash.th_digests core.slice.SliceArray.as_flattened
    simp only [hflat, ↓reduceDIte, Aeneas.Std.bind_ok]
    exact hd
  · rw [hval, slice_from_val]

end LeanSphincsProofs
