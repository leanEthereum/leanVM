import Whir.FieldModel

/-! Kernel-checked certificates for the specified degree-64 binary modulus.
The certificate arithmetic is the actual 64-step `Concrete.kmul`, already
proved to preserve the quotient interpretation in `FieldModel`. -/
namespace Whir.FieldModel
open Concrete Polynomial
set_option maxRecDepth 100000

/-- Repeated squaring using the actual carryless multiplier. -/
def squareIter : Nat → K → K
  | 0, a => a
  | n+1, a => squareIter n (kmul a a)

theorem toBaseQuotient_squareIter (n : Nat) (a : K) :
    toBaseQuotient (squareIter n a) = toBaseQuotient a ^ (2^n) := by
  induction n generalizing a with
  | zero => simp [squareIter]
  | succ n ih =>
    rw [squareIter, ih, toBaseQuotient_kmul, ← pow_two, ← pow_mul]
    congr 1
    omega

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem squareIter_32 : squareIter 32 2 = 0x5c62236777028505 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem squareIter_64 : squareIter 64 2 = 2 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem frobenius_bezout :
    kmul 0x53cad161bf5a89c7 (0x5c62236777028505 ^^^ 2) = 1 := by decide +kernel

theorem toBaseQuotient_two : toBaseQuotient 2 = AdjoinRoot.root baseModulus := by
  have h := toBaseQuotient_basis 1 (by decide)
  rw [show (1 : K) <<< UInt64.ofNat 1 = 2 by decide +kernel] at h
  simpa only [pow_one] using h

theorem baseModulus_dvd_frobenius64 :
    baseModulus ∣ (X^(2^64) - X : F₂[X]) := by
  apply AdjoinRoot.mk_eq_zero.mp
  simp only [map_sub, map_pow, AdjoinRoot.mk_X]
  apply sub_eq_zero.mpr
  have h := toBaseQuotient_squareIter 64 2
  rw [squareIter_64, toBaseQuotient_two] at h
  exact h.symm

private theorem coprime_of_quotient_inverse (f g h : F₂[X])
    (hi : AdjoinRoot.mk f h * AdjoinRoot.mk f g = 1) : IsCoprime f g := by
  have hd : f ∣ h * g - 1 :=
    AdjoinRoot.mk_eq_zero.mp (by simp only [map_sub, map_mul, map_one, hi, sub_self])
  obtain ⟨q,hq⟩ := hd
  refine ⟨-q, h, ?_⟩
  rw [sub_eq_iff_eq_add] at hq
  rw [hq, neg_mul, mul_comm q f, ← add_assoc, neg_add_cancel, zero_add]

theorem baseModulus_coprime_frobenius32 :
    IsCoprime baseModulus (X^(2^32) - X : F₂[X]) := by
  have hs := toBaseQuotient_squareIter 32 2
  rw [squareIter_32, toBaseQuotient_two] at hs
  apply coprime_of_quotient_inverse _ _ (wordPoly 0x53cad161bf5a89c7)
  simp only [map_sub, map_pow, AdjoinRoot.mk_X]
  change toBaseQuotient 0x53cad161bf5a89c7 * (_ - _) = 1
  rw [← hs, ← toBaseQuotient_two, CharTwo.sub_eq_add,
    ← toBaseQuotient_xor, ← toBaseQuotient_kmul, frobenius_bezout,
    toBaseQuotient_one]

/-- The prime-power-degree specialization of Rabin's irreducibility criterion.
The only prime divisor of 64 is 2, hence only the exponent 32 needs a coprimality
check in addition to the exponent-64 Frobenius identity. -/
theorem irreducible_degree64_of_rabin (f : F₂[X]) (hdeg : f.natDegree = 64)
    (h64 : f ∣ X^(2^64) - X) (h32 : IsCoprime f (X^(2^32) - X)) :
    Irreducible f := by
  obtain ⟨g,hg,hgf⟩ := exists_irreducible_of_natDegree_pos
    (show 0 < f.natDegree by omega)
  have hcard : Nat.card F₂ = 2 := Nat.card_zmod 2
  have hd : g.natDegree ∣ 64 :=
    hg.natDegree_dvd_of_dvd_X_pow_card_pow_sub_X
      (by rw [hcard]; exact dvd_trans hgf h64)
  have hn : ¬g.natDegree ∣ 32 := by
    intro hh
    have hg32 : g ∣ X^(2^32) - X := by
      have ht := hg.natDegree_dvd_iff_dvd_X_pow_card_pow_sub_X.mp hh
      rw [hcard] at ht
      exact ht
    exact hg.not_isUnit (h32.isUnit_of_dvd' hgf hg32)
  have hd' : g.natDegree ∣ 2^6 := hd
  obtain ⟨k,hk,hgk⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hd'
  have hk6 : k = 6 := by
    by_contra h
    apply hn
    rw [hgk]
    exact Nat.pow_dvd_pow 2 (show k ≤ 5 by omega)
  have hgdeg : g.natDegree = 64 := by simpa [hk6] using hgk
  have hf0 : f ≠ 0 := by intro h; simp [h] at hdeg
  exact (associated_of_dvd_of_natDegree_le hgf hf0 (by omega)).irreducible hg

theorem baseModulus_irreducible : Irreducible baseModulus :=
  irreducible_degree64_of_rabin baseModulus
    (natDegree_eq_of_degree_eq_some baseModulus_degree)
    baseModulus_dvd_frobenius64 baseModulus_coprime_frobenius32

instance : Fact (Irreducible baseModulus) := ⟨baseModulus_irreducible⟩

end Whir.FieldModel
