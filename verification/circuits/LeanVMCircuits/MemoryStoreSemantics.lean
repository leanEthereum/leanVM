module

public import LeanVMCircuits.MemoryWrite

@[expose] public section

namespace LeanVMCircuits.StoreMask

theorem select_eq_store (low high : Bit) (address value cell : Vector Bit 64)
    (hlegal : Memory.LegalWidth low high) (halign : Memory.Aligned low high address) :
    select {
      low, high, amount := #v[address[0], address[1], address[2]],
      value := Words.leftTo 64 (8 * Memory.offset address) 0 (Words.resize 32 0 value), cell
    } = Memory.store low high address value cell := by
  have hwidth : 2 ^ Memory.logWidth low high ≤ 4 := by
    simp [Memory.LegalWidth] at hlegal
    rcases hlegal with h | h | h <;> rw [h] <;> decide
  apply Vector.ext
  intro i hi
  have hindex : 8 * (i / 8) + i % 8 = i := by omega
  have hspan := StoreSpans.contains_iff low high #v[address[0], address[1], address[2]]
    ⟨i / 8, by omega⟩ hlegal halign
  change StoreSpans.contains { low, high, amount := #v[address[0], address[1], address[2]] } ⟨i / 8, by omega⟩ ↔
    Memory.offset address ≤ i / 8 ∧ i / 8 < Memory.offset address + 2 ^ Memory.logWidth low high at hspan
  have hrange :
      (Memory.offset address ≤ i / 8 ∧ i / 8 < Memory.offset address + 2 ^ Memory.logWidth low high) ↔
        (8 * Memory.offset address ≤ i ∧ i < 8 * Memory.offset address + 8 * 2 ^ Memory.logWidth low high) := by
    omega
  simp only [select, Memory.joinBytes, Memory.byte, Memory.store, Vector.getElem_mapFinRange,
    Vector.getElem_ofFn, hspan]
  by_cases hin : 8 * Memory.offset address ≤ i ∧ i < 8 * Memory.offset address + 8 * 2 ^ Memory.logWidth low high
  · have hbyte := hrange.mpr hin
    have hj : i - 8 * Memory.offset address < 32 := by omega
    have hj64 : i - 8 * Memory.offset address < 64 := by omega
    simp [hin, hbyte, hindex, Words.leftTo, Words.resize, Words.filled,
      Vector.getElem_mapFinRange, hj, hj64]
  · have hbyte : ¬ (Memory.offset address ≤ i / 8 ∧
        i / 8 < Memory.offset address + 2 ^ Memory.logWidth low high) := fun h => hin (hrange.mp h)
    simp [hin, hbyte, Vector.getElem_mapFinRange, hindex]

end LeanVMCircuits.StoreMask
