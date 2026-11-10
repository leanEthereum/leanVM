import Rv64Verifier.Proofs.Hash.Contracts
import Rv64Verifier.Proofs.Runtime.Sub

/-!
# A doubleword rebuilt from its bytes

The Merkle climb (`0x8000abfc`, `0x8000af20`, `0x8000ad94`) moves digests a byte at a time: eight
`lbu` of a doubleword, shifted and or-ed back into one (`reassemble`), stored aligned. Four such
make the 32 bytes of a digest (`bytesAt_of_dwords`).
-/

namespace Rv64Verifier.Proofs.Pcs.Vso
open RiscvZkvm.Rv64 Rv64Verifier.Contracts

theorem reassemble (w : Word) :
    (BitVec.zeroExtend 64 (extractByte w 7) <<< ((24#64).toNat % 64) |||
            BitVec.zeroExtend 64 (extractByte w 6) <<< ((16#64).toNat % 64) |||
          (BitVec.zeroExtend 64 (extractByte w 5) <<< ((8#64).toNat % 64) |||
            BitVec.zeroExtend 64 (extractByte w 4))) <<< ((32#64).toNat % 64) |||
      (BitVec.zeroExtend 64 (extractByte w 3) <<< ((24#64).toNat % 64) |||
          BitVec.zeroExtend 64 (extractByte w 2) <<< ((16#64).toNat % 64) |||
        (BitVec.zeroExtend 64 (extractByte w 1) <<< ((8#64).toNat % 64) |||
          BitVec.zeroExtend 64 (extractByte w 0))) = w := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth,
    BitVec.zeroExtend_eq_setWidth, Runtime.getLsbD_extractByte]
  interval_cases i <;> simp

/-- Four aligned doublewords equal make 32 equal bytes. -/
theorem bytesAt_of_dwords {s t : MachineState} {a b : Word} (ha : a.toNat % 8 = 0)
    (hb : b.toNat % 8 = 0)
    (h : ∀ m < 4, t.getMem (a + BitVec.ofNat 64 (8 * m)) = s.getMem (b + BitVec.ofNat 64 (8 * m))) :
    bytesAt t a 32 = bytesAt s b 32 := by
  have hal : ∀ (x : Word) (m : Nat), x.toNat % 8 = 0 → (x + BitVec.ofNat 64 (8 * m)).toNat % 8 = 0 := by
    intro x m hx
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]
    omega
  have e : ∀ (x : Word) (i : Nat), i < 32 →
      x + BitVec.ofNat 64 i = x + BitVec.ofNat 64 (8 * (i / 8)) + BitVec.ofNat 64 (i % 8) := by
    intro x i _
    rw [BitVec.add_assoc, ← BitVec.ofNat_add]
    congr 2
    omega
  simp only [bytesAt]
  apply List.map_congr_left
  intro i hi
  simp only [List.mem_range] at hi
  rw [e a i hi, e b i hi, getByte_aligned t (hal a _ ha) (Nat.mod_lt _ (by omega)),
    getByte_aligned s (hal b _ hb) (Nat.mod_lt _ (by omega)), h (i / 8) (by omega)]

end Rv64Verifier.Proofs.Pcs.Vso
