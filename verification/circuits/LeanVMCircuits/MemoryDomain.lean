module

public import LeanVMCircuits.MemorySemantics

@[expose] public section

namespace LeanVMCircuits.Memory

def CellAligned (address : Vector Bit 64) : Prop :=
  address[0] = 0 ∧ address[1] = 0 ∧ address[2] = 0

theorem legal_width_iff (low high : Bit) :
    LegalWidth low high ↔ ¬ (low = 1 ∧ high = 1) := by
  rcases bit_zero_or_one low with rfl | rfl <;>
    rcases bit_zero_or_one high with rfl | rfl <;>
    norm_num [LegalWidth, logWidth]

theorem legal_load_flags (low high signed : Bit) :
    LegalWidth low high ↔ Adder.value #v[low, high, signed] ∈ [0, 1, 2, 4, 5, 6] := by
  rcases bit_zero_or_one low with rfl | rfl <;>
    rcases bit_zero_or_one high with rfl | rfl <;>
    rcases bit_zero_or_one signed with rfl | rfl <;>
    unfold LegalWidth <;> decide +kernel

theorem legal_store_flags (low high : Bit) :
    LegalWidth low high ↔ Adder.value #v[low, high] ∈ [0, 1, 2] := by
  rcases bit_zero_or_one low with rfl | rfl <;>
    rcases bit_zero_or_one high with rfl | rfl <;>
    unfold LegalWidth <;> decide +kernel

theorem bus_aligned_iff (low high : Bit) (address : Vector Bit 64) (hlegal : LegalWidth low high) :
    CellAligned (bus low high address) ↔ Aligned low high address := by
  rcases bit_zero_or_one low with hl | hl <;>
    rcases bit_zero_or_one high with hh | hh <;>
    rcases bit_zero_or_one address[0] with h0 | h0 <;>
    rcases bit_zero_or_one address[1] with h1 | h1 <;>
    rcases bit_zero_or_one address[2] with h2 | h2 <;>
    norm_num [LegalWidth, logWidth, hl, hh] at hlegal
  all_goals
    norm_num [CellAligned, bus, busParts, Aligned, offset, logWidth,
      Adder.value_three, hl, hh, h0, h1, h2, Vector.getElem_mapFinRange, Fin.getElem_fin]

end LeanVMCircuits.Memory
