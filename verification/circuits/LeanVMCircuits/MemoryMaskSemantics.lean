module

public import LeanVMCircuits.MemorySpans
public import LeanVMCircuits.MemoryBytes
public import LeanVMCircuits.MemoryDomain

@[expose] public section

namespace LeanVMCircuits.StoreSpans

abbrev contains (input : Input Bit) (j : Fin 8) : Prop :=
  let spans := select input
  spans.low[j.val % 2]'(by omega) = 1 ∧
    spans.middle[j.val / 2 % 2]'(by omega) = 1 ∧ spans.high[j.val / 4]'(by omega) = 1

theorem contains_iff (low high : Bit) (amount : Vector Bit 3) (j : Fin 8)
    (hlegal : Memory.LegalWidth low high)
    (halign : Adder.value amount % 2 ^ Memory.logWidth low high = 0) :
    contains { low, high, amount } j ↔
      Adder.value amount ≤ j.val ∧ j.val < Adder.value amount + 2 ^ Memory.logWidth low high := by
  rcases bit_zero_or_one low with hl | hl <;>
    rcases bit_zero_or_one high with hh | hh <;>
    rcases bit_zero_or_one amount[0] with h0 | h0 <;>
    rcases bit_zero_or_one amount[1] with h1 | h1 <;>
    rcases bit_zero_or_one amount[2] with h2 | h2 <;>
    norm_num [Memory.LegalWidth, Memory.logWidth, hl, hh] at hlegal
  all_goals
    norm_num [Memory.logWidth, Adder.value_three, hl, hh, h0, h1, h2] at halign
  all_goals
    fin_cases j <;>
      norm_num [contains, select, BooleanOr.select, Memory.logWidth, Adder.value_three,
        hl, hh, h0, h1, h2]

end LeanVMCircuits.StoreSpans
