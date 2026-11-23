module

public import NativeRustc.Sphincs.Model

/-!
# The signature's bytes as `sphincs_verify`'s parse writes them

The wrapper's signature bytes in the pieces its loops write (`sigBytes_pieces`: runs of input
words `wb w s n`, the counters' big-endian bytes), and `Signature.fromBytes`' fields as slices of
the bytes: an opening's path is one slice (`flatten_slices`), so are a layer's chain values and its
path's nodes.
-/

@[expose] public section

namespace NativeRustc.Sphincs

open LeanVM.Protocol.KeccakHash Native.Keccak

/-- The bytes of the input words `s .. s + n`. -/
def wb (w : Nat → UInt64) (s n : Nat) : List UInt8 :=
  wordsBytes ((List.range n).map fun i ↦ w (s + i))

theorem length_wb (w : Nat → UInt64) (s n : Nat) : (wb w s n).length = 8 * n := by
  simp [wb, Native.Keccak.Proof.length_wordsBytes]

theorem wb_add (w : Nat → UInt64) (s a b : Nat) :
    wb w s (a + b) = wb w s a ++ wb w (s + a) b := by
  simp only [wb, wordsBytes, List.range_add, List.map_append, List.map_map, List.flatMap_append]
  congr 2
  apply List.map_congr_left
  intro i _
  simp [Nat.add_assoc]

/-- **The signature's bytes in the parse's pieces**: the words `8 .. 535` and `536, 537`, then
per layer the counter, the chain values' words and the path's last words. -/
theorem sigBytes_pieces (w : Nat → UInt64) :
    sigBytes w = wb w 8 528 ++ wb w 536 2 ++ be32 (w 538).toUInt32 ++ wb w 539 140 ++
      wb w 679 4 ++ be32 (w 683).toUInt32 ++ wb w 684 140 ++ wb w 824 4 ++
      be32 (w 828).toUInt32 ++ wb w 829 144 ++ wb w 973 4 := by
  have h0 : wordsBytes ((List.range 530).map fun k ↦ w (8 + k)) = wb w 8 528 ++ wb w 536 2 :=
    wb_add w 8 528 2
  unfold sigBytes
  rw [h0, show List.range 3 = [0, 1, 2] from rfl]
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
  change _ ++ (be32 (w 538).toUInt32 ++ wb w 539 (140 + 4) ++ (be32 (w 683).toUInt32 ++
    wb w 684 (140 + 4) ++ (be32 (w 828).toUInt32 ++ wb w 829 (144 + 4)))) = _
  rw [wb_add, wb_add, wb_add]
  simp only [List.append_assoc]

/-- A slice split in two. -/
theorem slice_add (S : List UInt8) (a m k : Nat) :
    slice S a (m + k) = slice S a m ++ slice S (a + m) k := by
  simp only [slice, List.take_add, List.drop_drop]

/-- Consecutive 16-byte slices make one slice. -/
theorem flatten_slices (S : List UInt8) (a : Nat) :
    ∀ n, ((List.range n).map fun z ↦ slice S (a + 16 * z) 16).flatten = slice S a (16 * n)
  | 0 => by simp [slice]
  | n + 1 => by
    rw [List.range_succ, List.map_append, List.flatten_append, flatten_slices S a n,
      show 16 * (n + 1) = 16 * n + 16 by omega, slice_add]
    simp

end NativeRustc.Sphincs
