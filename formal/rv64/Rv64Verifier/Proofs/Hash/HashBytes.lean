import Rv64Verifier.Proofs.Hash.Bytes
import Rv64Verifier.Proofs.Hash.Run
import RiscvZkvm.Rv64.Logic.MemRegionWrite

/-!
# Byte facts for `keccak_hash`

Sub-ranges of `bytesAt`, `BytesValid`; byte stores (`StoreKind.merge`) read back; the digest's
bytes from its doublewords.
-/

namespace Rv64Verifier.Hash
open RiscvZkvm.Rv64 Rv64Verifier.Sym Rv64Verifier.Contracts Rv64Verifier.Model

theorem length_bytesAt (s : MachineState) (a : Word) (n : Nat) : (bytesAt s a n).length = n := by
  simp [bytesAt]

theorem bytesAt_getD (s : MachineState) (a : Word) {n i : Nat} (hi : i < n) :
    (bytesAt s a n).getD i 0 = s.getByte (a + BitVec.ofNat 64 i) := by
  rw [List.getD_eq_getElem?_getD]; simp [bytesAt, hi]

/-- A part of a byte range. -/
theorem bytesAt_drop_take (s : MachineState) (a : Word) {n k m : Nat} (h : k + m ≤ n) :
    ((bytesAt s a n).drop k).take m = bytesAt s (a + BitVec.ofNat 64 k) m := by
  apply List.ext_getElem
  · simp [bytesAt]; omega
  · intro i h₁ h₂
    simp only [bytesAt, List.getElem_take, List.getElem_drop, List.getElem_map, List.getElem_range]
    rw [ofNat_add_ofNat]

theorem bytesAt_drop (s : MachineState) (a : Word) {n k : Nat} :
    (bytesAt s a n).drop k = bytesAt s (a + BitVec.ofNat 64 k) (n - k) := by
  apply List.ext_getElem
  · simp [bytesAt]
  · intro i h₁ h₂
    simp only [bytesAt, List.getElem_drop, List.getElem_map, List.getElem_range]
    rw [ofNat_add_ofNat]

theorem bytesAt_congr {s t : MachineState} {a b : Word} {n : Nat}
    (h : ∀ i < n, t.getByte (a + BitVec.ofNat 64 i) = s.getByte (b + BitVec.ofNat 64 i)) :
    bytesAt t a n = bytesAt s b n := by
  apply List.ext_getElem (by simp [bytesAt])
  intro i h₁ _
  simp only [bytesAt, List.getElem_map, List.getElem_range]
  exact h i (by simpa [bytesAt] using h₁)

theorem bytesValid_sub {a : Word} {n k m : Nat} (h : BytesValid a n) (hk : k + m ≤ n) :
    BytesValid (a + BitVec.ofNat 64 k) m := by
  refine ⟨?_, fun i hi ↦ ?_⟩
  · rw [BitVec.toNat_add, BitVec.toNat_ofNat]; have := h.1; omega
  · rw [ofNat_add_ofNat]; exact h.2 _ (by omega)

/-- Memory unchanged at the doubleword of a byte leaves the byte unchanged. -/
theorem getByte_congr {s t : MachineState} {a : Word}
    (h : t.getMem (alignToDword a) = s.getMem (alignToDword a)) : t.getByte a = s.getByte a := by
  simp only [MachineState.getByte, h]

theorem extractByte_replaceByte (w : Word) {p q : Nat} (hp : p < 8) (hq : q < 8) (b : BitVec 8) :
    extractByte (replaceByte w p b) q = if p = q then b else extractByte w q := by
  split
  · rename_i h
    subst h
    exact extractByte_replaceByte_same w ⟨p, hp⟩ b
  · rename_i h
    exact extractByte_replaceByte_diff w b hq hp (Ne.symm h)

end Rv64Verifier.Hash
