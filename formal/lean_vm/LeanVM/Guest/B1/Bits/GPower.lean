/-
  LeanVM.Guest.B1.Bits.GPower

  B1 for `g_power_of_word`: an integer word below `2^6` raised to its g-power.
-/

module

public import LeanVM.Guest.CoreRef
public import LeanVM.Guest.B1.Bits.Meaning
public import LeanVM.Guest.B1.Common.Find

/-!
# `g_power_of_word` (TRIAGE #17)

`g_power_of_word(value)` hints the six bits of `value` into frame cells `1 .. 6`, pins each by
booleanity (`b = b·b`), accumulates the word `Σ b_j·2^j` (at `45`) and the product
`Π (1 + b_j·(1 + g^(2^j)))` (at `50`), the constants folded (`1 + g^(2^j)` the word
`2^(2^j) + 1`), and asserts the word is `value`. So `value = E(n)`, `n < 2^6`, and the function
returns `g^n` (`g_power_of_word_spec`).
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

theorem find_g_power_of_word : coreProgram.find? "g_power_of_word" = some fn% «g_power_of_word» :=
  coreProgram_find?_at (j := idx% «g_power_of_word») rfl

/-- The folded factor constant `1 + g^(2^j)`. -/
theorem word_gpow_one (j : ℕ) (hj : 2 ^ j < 64) (c : ℕ) (hc : c = 2 ^ 2 ^ j ^^^ 1) :
    word c 0 = gen ^ 2 ^ j + 1 := by
  rw [word_eOfNat, gen_pow_eq_eOfNat hj, ← eOfNat_one, ← eOfNat_xor, hc]

/-- The honest values of `g_power_of_word` at `value = E(n)`. -/
def gpwVals (n : ℕ) : List E :=
  let b := fun j => bitE (n.testBit j)
  let w := fun k => word k 0
  let s1 := b 0 + b 1 * w 2
  let s2 := s1 + b 2 * w 4
  let s3 := s2 + b 3 * w 8
  let s4 := s3 + b 4 * w 16
  let s5 := s4 + b 5 * w 32
  let p0 := 1 + b 0 * w 3
  let p1 := p0 * (1 + b 1 * w 5)
  let p2 := p1 * (1 + b 2 * w 17)
  let p3 := p2 * (1 + b 3 * w 257)
  let p4 := p3 * (1 + b 4 * w 65537)
  let p5 := p4 * (1 + b 5 * w 4294967297)
  [eOfNat n, b 0, b 1, b 2, b 3, b 4, b 5,
    1, w 3, b 0 * w 3, p0,
    w 2, b 1 * w 2, s1, 1, w 5, b 1 * w 5, 1 + b 1 * w 5, p1,
    w 4, b 2 * w 4, s2, 1, w 17, b 2 * w 17, 1 + b 2 * w 17, p2,
    w 8, b 3 * w 8, s3, 1, w 257, b 3 * w 257, 1 + b 3 * w 257, p3,
    w 16, b 4 * w 16, s4, 1, w 65537, b 4 * w 65537, 1 + b 4 * w 65537, p4,
    w 32, b 5 * w 32, s5, 1, w 4294967297, b 5 * w 4294967297, 1 + b 5 * w 4294967297, p5, p5]

/-- **`g_power_of_word`'s core IR is its meaning.** -/
theorem g_power_of_word_holds : g_power_of_word_Spec := by
  intro rd args rets
  have w3 := word_gpow_one 0 (by norm_num) 3 (by decide)
  have w5 := word_gpow_one 1 (by norm_num) 5 (by decide)
  have w17 := word_gpow_one 2 (by norm_num) 17 (by decide)
  have w257 := word_gpow_one 3 (by norm_num) 257 (by decide)
  have w65537 := word_gpow_one 4 (by norm_num) 65537 (by decide)
  have w4294967297 := word_gpow_one 5 (by norm_num) 4294967297 (by decide)
  rw [rel_iff_sem find_g_power_of_word, show Fn.params fn% «g_power_of_word» = [.n 0] from rfl,
    show Fn.body fn% «g_power_of_word» = (core% «g_power_of_word» body) from rfl]
  simp only [core_eq% «g_power_of_word» body, Stmt.HoldsList, Stmt.Holds, Atom.Holds,
      List.map_cons, List.map_nil,
    true_and]
  constructor
  · rintro ⟨σ, hp, b0, e7, e8, e9, e10, b1, e11, e12, e13, e14, e15, e16, e17, e18, b2, e19, e20,
      e21, e22, e23, e24, e25, e26, b3, e27, e28, e29, e30, e31, e32, e33, e34, b4, e35, e36, e37,
      e38, e39, e40, e41, e42, b5, e43, e44, e45, e46, e47, e48, e49, e50, ha, e51, hret⟩
    subst hp
    have hb : ∀ j < 6, σ (.n (1 + j)) * σ (.n (1 + j)) = σ (.n (1 + j)) := by
      intro j hj
      interval_cases j
      exacts [b0.symm, b1.symm, b2.symm, b3.symm, b4.symm, b5.symm]
    have hword : ∑ j ∈ Finset.range 6, σ (.n (1 + j)) * eOfNat (2 ^ j) = σ (.n 0) := by
      rw [← (e_add_eq_zero_iff.mp ha)]
      simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
      rw [e45, e44, e43, e37, e36, e35, e29, e28, e27, e21, e20, e19, e13, e12, e11]
      simp [word_eOfNat, eOfNat_one]
    obtain ⟨hK, hlt, hprod⟩ := g_power_of_word_spec (by norm_num) hb hword
    refine ⟨kToNat ((σ (.n 0)).limb 0), hlt, ?_, ?_⟩
    · rw [eOfNat, ofBits_kToNat]; exact eq_ofK_limb hK
    · rw [← hret, e51, ← hprod]
      simp only [Finset.prod_range_succ, Finset.prod_range_zero, one_mul]
      rw [e50, e49, e48, e47, e46, e42, e41, e40, e39, e38, e34, e33, e32, e31, e30, e26, e25, e24,
        e23, e22, e18, e17, e16, e15, e14, e10, e9, e8, e7, w3, w5, w17, w257, w65537,
        w4294967297, word_one]
  · intro hm
    obtain ⟨v, rfl⟩ : ∃ v, args = [v] := by
      match args, hm with
      | [a], _ => exact ⟨a, rfl⟩
    obtain ⟨n, hn, rfl, rfl⟩ := hm
    let σ : Val := fun x => (gpwVals n).getD x.idx 0
    have ev : ∀ k, σ (.n k) = (gpwVals n).getD k 0 := fun _ => rfl
    have hbm : ∀ j, bitE (n.testBit j) = bitE (n.testBit j) * bitE (n.testBit j) :=
      fun j => (bitE_mul_self _).symm
    have hsum : ∑ j ∈ Finset.range 6, bitE (n.testBit j) * coordBasis (0 + j) = eOfNat n := by
      rw [reconstruct_bits 0 hn, Nat.pow_zero, Nat.one_mul, eOfNat128_of_lt (by omega)]
    have hpr := prod_bitE_gen_pow n.testBit 6
    rw [bitsVal_testBit hn] at hpr
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, Finset.prod_range_succ,
      Finset.prod_range_zero, zero_add, one_mul] at hsum hpr
    simp only [coordBasis] at hsum
    refine ⟨σ, rfl, ?_⟩
    simp only [ev, gpwVals, List.getD_cons_succ, List.getD_cons_zero, true_and]
    refine ⟨hbm 0, word_one.symm, hbm 1, word_one.symm, hbm 2, word_one.symm, hbm 3,
      word_one.symm, hbm 4, word_one.symm, hbm 5, word_one.symm, ?_, ?_⟩
    · rw [e_add_eq_zero_iff, ← hsum]
      simp [word_eOfNat, eOfNat128_of_lt, eOfNat_one]
    · rw [← hpr, w3, w5, w17, w257, w65537, w4294967297]

end
end LeanVM.Guest.B1
