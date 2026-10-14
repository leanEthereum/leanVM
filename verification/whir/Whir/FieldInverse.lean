import Whir.FieldEmbedding

/-! The fixed 64-step `kpow` loop and the actual `kinv` exponent implement
ordinary exponentiation and inversion in the certified base field. -/
namespace Whir.FieldModel
open Concrete

private def powStep (n : Nat) (s : K × K) (i : Nat) : K × K :=
  (kmul s.1 s.1, if n.testBit i then kmul s.2 s.1 else s.2)

private theorem kpow_eq_fold (a : K) (n : Nat) :
    kpow a n = ((List.range 64).foldl (powStep n) (a,1)).2 := by
  unfold kpow
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size]
  simp only [Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, ← List.range_eq_range',
    ← apply_ite, List.forIn_pure_yield_eq_foldl, pure_bind]
  change (List.foldl _ (a,1) (List.range 64)).2 = _
  apply congrArg (fun s : K × K => s.2)
  apply congrArg (fun f => List.foldl f (a,1) (List.range 64))
  funext s i
  unfold powStep
  split_ifs <;> rfl

private noncomputable def powInvariant (n i : Nat) (s : K × K) : BaseQuotient :=
  toBaseQuotient s.2 * toBaseQuotient s.1 ^ (n >>> i)

private theorem powStep_invariant (n i : Nat) (s : K × K) :
    powInvariant n (i+1) (powStep n s i) = powInvariant n i s := by
  have hn := Nat.bit_testBit_zero_shiftRight_one (n >>> i)
  rw [Nat.bit_val, Nat.testBit_shiftRight, Nat.add_zero, ← Nat.shiftRight_add] at hn
  rcases s with ⟨x,z⟩
  unfold powInvariant powStep
  dsimp only
  rw [toBaseQuotient_kmul]
  cases h : n.testBit i <;>
    simp only [h, Bool.toNat_false, Bool.toNat_true, Bool.false_eq_true, ↓reduceIte,
      toBaseQuotient_kmul] at hn ⊢ <;>
    rw [← hn] <;>
    simp only [pow_add, pow_mul, pow_zero, pow_one, mul_one, pow_two]; ring

private theorem powFold_invariant (n len start : Nat) (s : K × K) :
    powInvariant n (start+len) ((List.range' start len).foldl (powStep n) s) =
      powInvariant n start s := by
  induction len generalizing start s with
  | zero => simp
  | succ len ih =>
    rw [List.range'_succ, List.foldl_cons,
      show start+(len+1) = (start+1)+len by omega, ih, powStep_invariant]

/-- The exponent bound is essential: `kpow` inspects exactly 64 bits. -/
theorem toBaseQuotient_kpow (a : K) (n : Nat) (hn : n < 2^64) :
    toBaseQuotient (kpow a n) = toBaseQuotient a ^ n := by
  have h := powFold_invariant n 64 0 (a,1)
  have hs : n >>> 64 = 0 := by
    rw [Nat.shiftRight_eq_div_pow, Nat.div_eq_of_lt hn]
  rw [kpow_eq_fold]
  simpa only [powInvariant, Nat.zero_add, ← List.range_eq_range', hs,
    Nat.shiftRight_zero, pow_zero, mul_one, toBaseQuotient_one, one_mul] using h

/-- Exact correctness of the executable inverse, including zero. -/
theorem toBaseQuotient_kinv (a : K) :
    toBaseQuotient (kinv a) = (toBaseQuotient a)⁻¹ := by
  rw [kinv, toBaseQuotient_kpow a _ (by decide)]
  by_cases ha : toBaseQuotient a = 0
  · simp [ha]
  · have hp : toBaseQuotient a ^ (2^64-2) * toBaseQuotient a = 1 := by
      rw [← pow_succ, show (2^64-2)+1 = 2^64-1 by decide]
      have h := FiniteField.pow_card_sub_one_eq_one (toBaseQuotient a) ha
      rw [card_BaseQuotient] at h
      exact h
    exact eq_inv_of_mul_eq_one_left hp

theorem ofK_kinv (a : K) : E.ofK (kinv a) = (E.ofK a)⁻¹ := by
  simpa only [map_inv₀, baseEmbedding_word] using
    congrArg baseEmbedding (toBaseQuotient_kinv a)

end Whir.FieldModel
