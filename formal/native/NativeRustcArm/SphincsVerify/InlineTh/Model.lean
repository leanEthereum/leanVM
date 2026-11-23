module

public import NativeRustc.Sphincs.Model

/-!
# An inlined `th` of a short input

Where `sphincs_verify` inlines `th` (the FORS nodes, the chains' steps, the tree's nodes), its
input `PK.seed | ADRS | M` is shorter than a block: the hashers' states stay zero, the buffer
holds the input, and `finalize` absorbs the padded input into the zero state (`th_short`).
-/

namespace NativeRustcArm.SphincsVerifyProof.InlineTh

open NativeRustc NativeRustc.Keccak NativeRustc.Sphincs LeanVM.Protocol.KeccakHash Native.Keccak

public section

/-- The zero state's bytes. -/
theorem stateBytes_zero : stateBytes (Vector.replicate 25 0) = List.replicate 200 0 := by
  rw [stateBytes, Vector.toList_replicate, wordsBytes_replicate_zero]

/-- **Keccak-256 of a short input**: its padded block absorbed into the zero state, the first 32
bytes. -/
theorem hashBytes_short {d : List UInt8} (h : d.length < 136) :
    hashBytes d = (keccakF (xorBlock (List.replicate 200 0) (finalBlock d))).take 32 := by
  have hd : d.length / 136 = 0 := Nat.div_eq_of_lt h
  rw [hashBytes, ← digestOf_absorb_sponge, hd, Nat.mul_zero, List.drop_zero,
    show sponge d = Vector.replicate 25 0 by rw [sponge, hd]; rfl, ← absorb_stateBytes,
    stateBytes_zero, finalBlock_eq_padBlock]
  rfl

/-- **`th` of a short input**: the first 16 bytes of `keccak_f` of the padded input XORed into
the zero state. -/
theorem th_short {seed adrs m : List UInt8} (h : (seed ++ adrs ++ m).length < 136) :
    th seed adrs m =
      (keccakF (xorBlock (List.replicate 200 0) (finalBlock (seed ++ adrs ++ m)))).take 16 := by
  rw [th, hashBytes_short h, List.take_take]
  rfl

end

end NativeRustcArm.SphincsVerifyProof.InlineTh
