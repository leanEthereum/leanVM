module

public import LeanVMCircuits.AluRaw

@[expose] public section

namespace LeanVMCircuits.Alu
set_option maxRecDepth 65536


private theorem ofNat_get (n value i : ℕ) (hi : i < n) :
    (Words.ofNat n value)[i] = (((value / 2 ^ i) % 2 : ℕ) : Bit) := by
  induction n with
  | zero => omega
  | succ n ih =>
    by_cases h : i < n
    · simpa only [Words.ofNat, Vector.getElem_push, h, ↓reduceDIte] using ih h
    · have he : i = n := by omega
      subst i
      simp [Words.ofNat]

private theorem bit_indicator (bit : Bit) (p : Prop) [Decidable p] (h : bit = 1 ↔ p) :
    bit = if p then 1 else 0 := by
  rcases bit_zero_or_one bit with hb | hb <;> simp_all

private theorem bit_word (bit : Bit) :
    (Vector.mapFinRange 64 fun i => if i.val = 0 then bit else 0) = Words.ofNat 64 bit.val := by
  apply Vector.ext
  intro i hi
  rw [Vector.getElem_mapFinRange, ofNat_get 64 bit.val i hi]
  rcases bit_zero_or_one bit with rfl | rfl
  · simp
  · by_cases hz : i = 0
    · subst i; norm_num
    · have hp : 1 < 2 ^ i := one_lt_pow₀ (by decide : 1 < (2 : ℕ)) hz
      simp [hz, Nat.div_eq_of_lt hp]
@[simp] private theorem mapFinRange_get (word : Vector Bit 64) :
    (Vector.mapFinRange 64 fun i => word[i.val]) = word := by
  apply Vector.ext
  intro i hi
  simp [Vector.getElem_mapFinRange]
@[simp] private theorem bit_two : (2 : Bit) = 0 := ZMod.natCast_self 2

@[simp] private theorem condition_word (p : Prop) [Decidable p] :
    (Vector.mapFinRange 64 fun i => if i = 0 then (if p then (1 : Bit) else 0) else 0) =
      Words.ofNat 64 (if p then 1 else 0) := by
  by_cases hp : p
  · simpa [hp] using bit_word (1 : Bit)
  · simpa [hp] using bit_word (0 : Bit)



private theorem offset_same (dt old : Vector Bit 64) : AluIndirect.offset dt old old = dt := by
  apply Vector.ext
  intro i hi
  rcases bit_zero_or_one old[i] with hb | hb <;>
    simp [AluIndirect.offset, Vector.getElem_mapFinRange, hb]

theorem afterArithmetic_reference (input : Input Bit) (arithmetic : Adder.Output 64 Bit)
    (hlegal : Legal input.flags)
    (ha : AluArithmetic.Spec { x := input.v1, y := operand input, sub := input.flags[0] } arithmetic) :
    afterArithmetic input arithmetic = reference input := by
  have hs := AluArithmetic.sum_correct
    { x := input.v1, y := operand input, sub := input.flags[0] } arithmetic ha
  change arithmetic.sum = sum input at hs
  have hu (hsub : input.flags[0] = 1) :
      1 + arithmetic.carry = if unsignedLess input then 1 else 0 :=
    bit_indicator _ _ (AluArithmetic.unsigned_correct
      { x := input.v1, y := operand input, sub := input.flags[0] } arithmetic hsub ha)
  have hl (hsub : input.flags[0] = 1) :
      (1 + arithmetic.carry) + input.v1[63] + (operand input)[63] =
        if signedLess input then 1 else 0 :=
    bit_indicator _ _ (AluArithmetic.signed_correct
      { x := input.v1, y := operand input, sub := input.flags[0] } arithmetic hsub ha)
  have hcarry (hsub : input.flags[0] = 1) :
      arithmetic.carry = if unsignedLess input then 0 else 1 := by
    have hb := hu hsub
    rcases bit_zero_or_one arithmetic.carry with hc | hc <;>
      by_cases hp : unsignedLess input <;> simp_all [bit_one_add_one]
  cases input with
  | mk v1 v2 imm flags dt pc4 =>
    have hc := legal_cases hlegal
    simp only [legalFlags, List.map, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    all_goals
      subst flags
      simp only [ofNat_get] at hs hu hl hcarry ⊢
      norm_num at hu hl hcarry
      dsimp +instances only [afterArithmetic, reference, value, jump, Taken,
        AluSelector.selected, AluSelector.none, AluSelector.combine,
        AluLogicWord.select, AluBranch.selected]
      simp +instances only [ofNat_get, hs]
      norm_num [bit_one_add_one, Vector.getElem_mapFinRange]
      try simp +instances only [hl]
      try simp +instances only [hcarry]
      try simp +instances [condition_word, bit_two, offset_same]
      try simp +instances only [AluEquality.difference, Vector.getElem_zipWith,
        AluIndirect.offset, sum, ofNat_get]
      try norm_num [ofNat_get]
      try split_ifs <;> try simp_all only [bit_one_add_one, add_zero, zero_add,
        ite_true, ite_false]
      try simpa using bit_word (1 : Bit)
      try simpa using bit_word (0 : Bit)
      try
        apply Vector.ext
        intro i hi
        simp +instances only [Vector.getElem_mapFinRange, Vector.getElem_zipWith]
        try ac_rfl
      try exact False.elim (zero_ne_one hu)


end LeanVMCircuits.Alu
