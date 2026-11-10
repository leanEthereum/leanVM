import Rv64Verifier.Proofs.Walk.Base
import Rv64Verifier.Model.Hash

/-!
# `walk`: words of bytes

The public input is read a byte at a time and assembled into little-endian words
(`assemble_eq`); the IV and the public input are the mirror's bytes, whose words
(`digestWordsRust`) are the doublewords in memory (`digestWords_bytesAt`).
-/

namespace Rv64Verifier.Proofs.Walk
open RiscvZkvm.Rv64 Rv64Verifier.Runtime Rv64Verifier.Model Rv64Verifier.Transcript

/-- A byte of a mapped range is a valid access. -/
theorem valid1 {a : Word} {n : Nat} (h : Mapped a n) (k : Word) (hk : k.toNat < n) :
    Sym.validAccess 1 (a + k) = true := by
  have e : k = BitVec.ofNat 64 k.toNat := by simp
  rw [e]
  exact Mapped.valid h hk

/-- Eight bytes of `w`, as the code assembles them, are `w`. -/
theorem assemble_eq (w : Word) :
    (BitVec.zeroExtend 64 (extractByte w 7) * 16777216 |||
            BitVec.zeroExtend 64 (extractByte w 6) * 65536 |||
          (BitVec.zeroExtend 64 (extractByte w 5) * 256 |||
            BitVec.zeroExtend 64 (extractByte w 4))) *
        4294967296 |||
      (BitVec.zeroExtend 64 (extractByte w 3) * 16777216 |||
          BitVec.zeroExtend 64 (extractByte w 2) * 65536 |||
        (BitVec.zeroExtend 64 (extractByte w 1) * 256 |||
          BitVec.zeroExtend 64 (extractByte w 0))) = w := by
  have m (x : Word) (n : Nat) : x * BitVec.ofNat 64 (2 ^ n) = x <<< n :=
    (Sym.shiftLeft_eq_mul x n).symm
  rw [show (16777216 : Word) = BitVec.ofNat 64 (2 ^ 24) from rfl,
    show (65536 : Word) = BitVec.ofNat 64 (2 ^ 16) from rfl,
    show (256 : Word) = BitVec.ofNat 64 (2 ^ 8) from rfl,
    show (4294967296 : Word) = BitVec.ofNat 64 (2 ^ 32) from rfl]
  simp only [m]
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [extractByte_eq, BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft,
    BitVec.zeroExtend_eq_setWidth, BitVec.getLsbD_setWidth]
  interval_cases i <;> simp

/-- `u64::from_le_bytes` of the bytes of `w` is `w`. -/
theorem fromLeBytes_extract (w : Word) : fromLeBytes ((List.range 8).map (extractByte w)) = w := by
  simp only [fromLeBytes, show List.range 8 = [0, 1, 2, 3, 4, 5, 6, 7] from rfl, List.map_cons,
    List.map_nil, List.foldl_cons, List.foldl_nil, List.getD_cons_zero, List.getD_cons_succ]
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [extractByte_eq, BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth]
  interval_cases i <;> simp

/-- The words of 32 aligned bytes in memory are its doublewords. -/
theorem digestWords_bytesAt (s : MachineState) {a : Word} (ha : a.toNat % 8 = 0) {j : Nat}
    (hj : j < 4) :
    (digestWordsRust (bytesAt s a 32)).getD j 0 = s.getMem (a + BitVec.ofNat 64 (8 * j)) := by
  have hb : (a + BitVec.ofNat 64 (8 * j)).toNat % 8 = 0 := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have e : ((bytesAt s a 32).drop (8 * j)).take 8 =
      (List.range 8).map (extractByte (s.getMem (a + BitVec.ofNat 64 (8 * j)))) := by
    apply List.ext_getElem
    · simp only [List.length_take, List.length_drop, bytesAt_length, List.length_map,
        List.length_range]
      omega
    · intro k h1 h2
      simp only [List.length_map, List.length_range] at h2
      rw [List.getElem_take, List.getElem_drop, bytesAt_getElem, List.getElem_map,
        List.getElem_range, ← byteAt_add hb h2, add_ofNat_add]
  rw [digestWordsRust, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hj,
    Option.map_some, Option.getD_some, e, fromLeBytes_extract]

end Rv64Verifier.Proofs.Walk
