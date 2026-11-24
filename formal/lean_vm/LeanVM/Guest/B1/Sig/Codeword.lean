/-
  LeanVM.Guest.B1.Sig.Codeword

  A codeword's groups as its check walks them: the digit values a group's dispatch takes, each
  chain's hinted start, and sums of digits.
-/

module

public import LeanVM.Guest.B1.Sig.WotsSound

/-!
# A codeword's groups

A codeword has `G` groups of three digits and the last chain's group (`cwN`). The digit values a group's
dispatch takes are its selector's exponent (`logG`, the unique exponent below the arm count). `sum_range_three_mul`,
`digitSum_three`, `digitSum_one`, `eOfNat128_add_shift`: digits summed by group and placed base 4.
-/

namespace LeanVM.Guest.B1.Sig

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol.Verifier

@[expose] public section

variable {C : CallRel} {rd : Reader} {σ : Val} {kret : List E → Prop}

/-! ## Exponents -/

open Classical in
/-- The exponent `k < bound` with `x = g^k` (`0` if none). -/
noncomputable def logG (x : E) (bound : Nat) : Nat :=
  ((List.range bound).find? fun k => decide (x = ofK (addressOfIndex k))).getD 0

theorem logG_eq {x : E} {k bound : Nat} (hk : k < bound) (hb : bound ≤ 2 ^ 64 - 1)
    (hx : x = ofK (addressOfIndex k)) : logG x bound = k := by
  classical
  unfold logG
  have hsome : ((List.range bound).find? fun k => decide (x = ofK (addressOfIndex k))).isSome := by
    rw [List.find?_isSome]
    exact ⟨k, List.mem_range.mpr hk, by simp [hx]⟩
  obtain ⟨k', hk'⟩ := Option.isSome_iff_exists.mp hsome
  rw [hk', Option.getD_some]
  have hmem := List.mem_of_find?_eq_some hk'
  have hp := List.find?_some hk'
  simp only [decide_eq_true_eq] at hp
  rw [hx] at hp
  have hk' := List.mem_range.mp hmem
  exact (gpow_injOn (Set.mem_Iio.mpr (by omega)) (Set.mem_Iio.mpr (by omega)) (ofK_injective hp)).symm

/-! ## The groups of a codeword -/

/-! ## The codeword -/

/-- The digits of group `p` of a codeword of `G` groups of three and the last chain's. -/
def cwN (G p : Nat) : Nat := if p < G then 3 else 1

/-! ## Sums of digits -/

theorem sum_range_three_mul {M : Type} [AddCommMonoid M] (g : Nat → M) :
    ∀ m, ∑ i ∈ Finset.range (3 * m), g i = ∑ p ∈ Finset.range m, (g (3 * p) + g (3 * p + 1) + g (3 * p + 2))
  | 0 => by simp
  | m + 1 => by
      rw [Finset.sum_range_succ (n := m), ← sum_range_three_mul g m,
        show 3 * (m + 1) = 3 * m + 2 + 1 by ring, Finset.sum_range_succ, Finset.sum_range_succ,
        Finset.sum_range_succ]
      simp only [add_assoc]

theorem digitSum_three (k : Nat) : digitSum k 3 = k % 4 + k / 4 % 4 + k / 16 % 4 := by
  simp [digitSum]; omega

theorem digitSum_one (k : Nat) (hk : k < 4) : digitSum k 1 = k := by
  simp [digitSum]; omega

theorem eOfNat128_add_shift {S k s : Nat} (hS : S < 2 ^ s) :
    eOfNat128 S + eOfNat128 (2 ^ s * k) = eOfNat128 (S + 2 ^ s * k) := by
  rw [← eOfNat128_xor, Nat.xor_comm, two_pow_mul_xor hS, add_comm]

end
end LeanVM.Guest.B1.Sig
