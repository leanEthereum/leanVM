/-
  Rv64mc.Proof.Transcript.Bytes

  Doublewords from the bytes `memcpy` and `memset` state (`Spec.Runtime.Mem`'s contracts are on bytes): an aligned
  doubleword is its eight bytes, so a copy of aligned words is a copy of the words, and a zeroed aligned word is
  zero.
-/

import Rv64mc.Core.Repr
import RiscvZkvm.Rv64.Logic.MemRegionWrite

namespace Rv64mc.Proof.Transcript

open RiscvZkvm.Rv64

theorem toNat_add_lt8 {b : Word} {k : Nat} (hb : b.toNat % 8 = 0) (hk : k < 8) :
    (b + BitVec.ofNat 64 k).toNat = b.toNat + k := toNat_add_ofNat (by have := b.isLt; omega)

/-- Byte `k` of the aligned doubleword at `b`. -/
theorem getByte_aligned {m : MachineState} {b : Word} {k : Nat} (hb : b.toNat % 8 = 0) (hk : k < 8) :
    m.getByte (b + BitVec.ofNat 64 k) = extractByte (m.getMem b) k := by
  have h := toNat_add_lt8 hb hk
  have ha : alignToDword (b + BitVec.ofNat 64 k) = b := by
    apply BitVec.eq_of_toNat_eq; rw [toNat_alignToDword, h]; omega
  simp only [MachineState.getByte, ha, byteOffset_eq_toNat_mod, h]
  congr 1; omega

/-- **An aligned doubleword is its bytes.** -/
theorem getMem_of_bytes {m m' : MachineState} {b b' : Word} (hb : b.toNat % 8 = 0) (hb' : b'.toNat % 8 = 0)
    (h : ∀ k, k < 8 → m'.getByte (b + BitVec.ofNat 64 k) = m.getByte (b' + BitVec.ofNat 64 k)) :
    m'.getMem b = m.getMem b' :=
  eq_of_forall_extractByte fun k hk => by
    rw [← getByte_aligned hb hk, ← getByte_aligned hb' hk, h k hk]

/-- An aligned doubleword of zero bytes is zero. -/
theorem getMem_of_zero_bytes {m : MachineState} {b : Word} (hb : b.toNat % 8 = 0)
    (h : ∀ k, k < 8 → m.getByte (b + BitVec.ofNat 64 k) = 0#8) : m.getMem b = 0#64 :=
  eq_of_forall_extractByte fun k hk => by
    rw [← getByte_aligned hb hk, h k hk]; simp [extractByte]

/-- **Words copied byte by byte**: the `n` bytes from `src` at `dst`, both aligned, hold the words `src` held. -/
theorem WordsAt.of_copy {m m' : MachineState} {dst src : Word} {ws : List Word} (hw : WordsAt m src ws)
    (hd : dst.toNat % 8 = 0) (hs : src.toNat % 8 = 0) (hdn : dst.toNat + 8 * ws.length < 2 ^ 64)
    (h : ∀ k, k < 8 * ws.length → m'.getByte (dst + BitVec.ofNat 64 k) = m.getByte (src + BitVec.ofNat 64 k)) :
    WordsAt m' dst ws := by
  have hsn := hw.1
  refine ⟨hdn, fun j hj => ?_⟩
  rw [← hw.2 j hj]
  have e : ∀ (a : Word), a.toNat + 8 * ws.length < 2 ^ 64 → ∀ k, k < 8 →
      a + BitVec.ofNat 64 (8 * j) + BitVec.ofNat 64 k = a + BitVec.ofNat 64 (8 * j + k) := fun a _ k _ => by
    rw [BitVec.add_assoc, BitVec.ofNat_add]
  refine getMem_of_bytes ?_ ?_ fun k hk => ?_
  · rw [toNat_add_ofNat (by omega)]; omega
  · rw [toNat_add_ofNat (by omega)]; omega
  · rw [e dst hdn k hk, e src hsn k hk]; exact h _ (by omega)

end Rv64mc.Proof.Transcript
