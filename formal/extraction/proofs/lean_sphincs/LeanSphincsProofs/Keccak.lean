import LeanSphincsProofs.Sponge
import LeanSphincsProofs.Permutation
import LeanSphincsProofs.KeccakSpec

/-!
# `keccak256` computes Keccak

The Rust permutation `keccak_f` is the statement's Keccak-f[1600]: both are hash-specs' Keccak-f on
lanes (`Permutation.lean`, `KeccakSpec.lean`), which hash-specs proves to be FIPS 202's. With it the
sponge step and the digest are the statement's (`Sponge.lean`), and so the hasher computes
Keccak-256 with nothing assumed.
-/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM Std.Do
open LeanVM.Semantics (KeccakState keccakF1600)

namespace LeanSphincsProofs

/-- A Rust state's lanes are the lanes of the statement's state it stands for. -/
theorem toState_toArray (a : Array Std.U64 25#usize) : (toState a).toArray = lanesOf a := by
  have hlen : a.val.length = 25 := by simp
  apply _root_.Array.ext
  · simp [toState, lanesOf, hlen]
  · intro i h1 h2
    simp [toState, lanesOf]

/-- **`keccak_f` is Keccak-f[1600]**, the statement's. -/
theorem keccak_f_eq (a : Array Std.U64 25#usize) :
    ∃ a', keccak256.keccak_f a = ok a' ∧ toState a' = keccakF1600 (toState a) := by
  obtain ⟨a', ha, hl⟩ := keccak_f_spec a
  refine ⟨a', ha, ?_⟩
  apply Vector.toArray_inj.mp
  rw [toState_toArray, hl, keccakF1600_eq_fast, toState_toArray]

/-- **The sponge step and the digest of `keccak256`** are Keccak's, over Keccak-f[1600]. -/
theorem spongeSpec : SpongeSpec keccakF1600 := spongeSpec_of_keccak_f keccak_f_eq

end LeanSphincsProofs
