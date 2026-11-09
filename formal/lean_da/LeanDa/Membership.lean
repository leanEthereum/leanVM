module

public import LeanDa.ReedSolomon

/-!
# The membership test

Proposition prop:rs-membership of `doc/leanvm/body/d-novel-basis.tex` for the crate's code, with
one challenge (`membership.rs:7-14` at leanVM `40f877dc`). The dual codeword of challenges
`z_0 … z_13` is the encoding of the tensor `⊗_j (1, z_j)` (`dual_eq_sum`); the deployed one takes
`z_j = z^(2^j)` (`dualCodewordAt_eq`), whose tensor is `(z^u)_u` (`tensor_powers`). So the inner
product with a row `w` is the polynomial `Σ_u ⟨Xᵤ, w⟩ z^u` in `z` (`eval_membershipPoly`), of
degree below `2^14`, its exponents distinct. A codeword is orthogonal to every `Xᵤ`
(`rsCode_le_orthogonal`), so it passes for every `z` (`dot_dual_eq_zero`). A row that is not a
codeword is not orthogonal to some `Xᵤ` (`mem_rsCode_of_orthogonal`), so the polynomial is
nonzero and has at most `2^14 - 1` roots (`card_acceptSet_le`): at most `2^14 - 1` of the
`|E| = 2^192` challenges accept it.

This module is part of the instantiation of Benedikt Wagner's framework for erasure code
commitments (`PqDas`, ported from https://github.com/b-wagn/fv-pq-da) with LeanDA.
-/

open Polynomial Module

namespace LeanDa

@[expose] public section

/-! ## Bits of a coefficient index -/

/-- The bits of `u`. -/
def bitsOf (u : Fin (2 ^ 14)) : Finset (Fin 14) := Finset.univ.filter fun j ↦ (u : ℕ).testBit j

theorem eq_of_testBit_eq {u v : Fin (2 ^ 14)} (h : ∀ j : Fin 14, (u : ℕ).testBit j = (v : ℕ).testBit j) :
    u = v := by
  refine Fin.ext (Nat.eq_of_testBit_eq fun i ↦ ?_)
  by_cases hi : i < 14
  · exact h ⟨i, hi⟩
  · have hle : 2 ^ 14 ≤ 2 ^ i := Nat.pow_le_pow_right (by norm_num) (by omega)
    rw [Nat.testBit_eq_false_of_lt (by omega), Nat.testBit_eq_false_of_lt (by omega)]

theorem bitsOf_injective : Function.Injective bitsOf := by
  intro u v h
  refine eq_of_testBit_eq fun j ↦ ?_
  have := congrArg (fun t ↦ j ∈ t) h
  simp only [bitsOf, Finset.mem_filter, Finset.mem_univ, true_and, eq_iff_iff] at this
  exact Bool.eq_iff_iff.mpr this

theorem bitsOf_bijective : Function.Bijective bitsOf :=
  (Fintype.bijective_iff_injective_and_card bitsOf).mpr
    ⟨bitsOf_injective, by simp [Fintype.card_finset]⟩

theorem tensor_eq (z : Fin 14 → E) (u : Fin (2 ^ 14)) : tensor z u = ∏ j ∈ bitsOf u, z j := by
  rw [tensor, bitsOf, Finset.prod_filter]

theorem novelX_eval (u : Fin (2 ^ 14)) (x : K) :
    (novelX u).eval x = ∏ j ∈ bitsOf u, (normalizedSubspacePolynomial j).eval x := by
  unfold novelX AdditiveNTT.Xⱼ normalizedSubspacePolynomial
  rw [eval_prod, bitsOf, Finset.prod_filter]
  refine Finset.prod_congr rfl fun i _ ↦ ?_
  rw [eval_pow, Nat.getBit_eq_testBit]
  split_ifs <;> simp

/-- The dual codeword of challenges `z_0 … z_13`: `∏_j (1 + z_j Ŵ_j(x))` on the domain. -/
noncomputable def dualTensorAt (z : Fin 14 → E) (b : Fin (2 ^ 15)) : E :=
  ∏ j : Fin 14, (1 + z j * ι ((normalizedSubspacePolynomial j).eval (point b)))

/-- The challenges `z^(2^j)` of one challenge `z`. -/
def powersOf (z : E) (j : Fin 14) : E := z ^ 2 ^ (j : ℕ)

/-- The deployed dual codeword is that of the challenges `z^(2^j)`. -/
theorem dualCodewordAt_eq (z : E) : dualCodewordAt z = dualTensorAt (powersOf z) := rfl

/-- **The dual codeword is the encoding of the tensor**: `L(x) = Σ_u (⊗_j (1, z_j))_u Xᵤ(x)`. -/
theorem dual_eq_sum (z : Fin 14 → E) (b : Fin (2 ^ 15)) :
    dualTensorAt z b = ∑ u, tensor z u * ι ((novelX u).eval (point b)) := by
  rw [dualTensorAt, Finset.prod_one_add, Finset.powerset_univ,
    ← bitsOf_bijective.sum_comp fun t ↦ ∏ j ∈ t, z j * ι ((normalizedSubspacePolynomial j).eval (point b))]
  refine Finset.sum_congr rfl fun u _ ↦ ?_
  rw [tensor_eq, novelX_eval, map_prod, ← Finset.prod_mul_distrib]

/-- The bits of `u`, weighted, add up to `u` modulo `2^n`. -/
theorem sum_testBit_pow (u : ℕ) :
    ∀ n, ∑ j ∈ Finset.range n, (if u.testBit j then 2 ^ j else 0) = u % 2 ^ n
  | 0 => by simp [Nat.mod_one]
  | n + 1 => by
    rw [Finset.sum_range_succ, sum_testBit_pow u n, Nat.testBit_eq_decide_div_mod_eq, pow_succ,
      Nat.mod_mul]
    rcases Nat.mod_two_eq_zero_or_one (u / 2 ^ n) with h | h <;> simp [h]

/-- **The tensor of the powers `z^(2^j)` is `(z^u)_u`.** -/
theorem tensor_powers (z : E) (u : Fin (2 ^ 14)) : tensor (powersOf z) u = z ^ (u : ℕ) := by
  have h : ∀ j : Fin 14, (if (u : ℕ).testBit j then powersOf z j else 1) =
      z ^ (if (u : ℕ).testBit j then 2 ^ (j : ℕ) else 0) := fun j ↦ by
    split_ifs <;> simp [powersOf]
  rw [tensor, Finset.prod_congr rfl fun j _ ↦ h j, Finset.prod_pow_eq_pow_sum,
    Fin.sum_univ_eq_sum_range (fun j ↦ if (u : ℕ).testBit j then 2 ^ j else 0) 14,
    sum_testBit_pow, Nat.mod_eq_of_lt u.isLt]

/-! ## The membership polynomial -/

/-- The coefficients `⟨Xᵤ, w⟩` of a row on the domain. -/
noncomputable def novelCoeff (w : Row) (u : Fin (2 ^ 14)) : K :=
  ∑ b : Fin (2 ^ 15), (novelX u).eval (point b) * w b

/-- `⟨L, w⟩` as a polynomial in the challenge: `Σ_u ⟨Xᵤ, w⟩ z^u`. -/
noncomputable def membershipPoly (w : Row) : E[X] :=
  ∑ u : Fin (2 ^ 14), C (ι (novelCoeff w u)) * X ^ (u : ℕ)

theorem dot_dual_eq_sum (w : Row) (z : Fin 14 → E) :
    innerProduct (dualTensorAt z) w = ∑ u, ι (novelCoeff w u) * tensor z u := by
  simp only [innerProduct, dual_eq_sum, Finset.sum_mul, novelCoeff, map_sum, map_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun u _ ↦ Finset.sum_congr rfl fun b _ ↦ ?_
  ring

theorem eval_membershipPoly (w : Row) (z : E) :
    (membershipPoly w).eval z = innerProduct (dualCodewordAt z) w := by
  rw [membershipPoly, eval_finsetSum, dualCodewordAt_eq, dot_dual_eq_sum]
  refine Finset.sum_congr rfl fun u _ ↦ ?_
  rw [tensor_powers, eval_mul, eval_C, eval_pow, eval_X]

theorem coeff_membershipPoly (w : Row) (u : Fin (2 ^ 14)) :
    (membershipPoly w).coeff u = ι (novelCoeff w u) := by
  rw [membershipPoly, finsetSum_coeff, Finset.sum_eq_single u]
  · simp
  · intro v _ hv
    rw [coeff_C_mul_X_pow]
    exact ite_eq_right_iff.mpr fun h ↦ absurd (Fin.ext h).symm hv
  · intro hu
    exact absurd (Finset.mem_univ u) hu

theorem membershipPoly_ne_zero {w : Row} {u₀ : Fin (2 ^ 14)} (h : novelCoeff w u₀ ≠ 0) :
    membershipPoly w ≠ 0 := by
  intro h0
  have := coeff_membershipPoly w u₀
  rw [h0, coeff_zero] at this
  exact (map_ne_zero_iff ι ι.injective).mpr h this.symm

theorem natDegree_membershipPoly_le (w : Row) : (membershipPoly w).natDegree ≤ 2 ^ 14 - 1 := by
  rw [membershipPoly]
  refine natDegree_sum_le_of_forall_le _ _ fun u _ ↦ ?_
  refine (natDegree_C_mul_X_pow_le _ _).trans ?_
  have := u.isLt
  omega

/-! ## Completeness and soundness -/

/-- **A codeword passes for all challenges.** -/
theorem dot_dualTensor_eq_zero {w : Row} (hw : w ∈ rsCode) (z : Fin 14 → E) :
    innerProduct (dualTensorAt z) w = 0 := by
  rw [dot_dual_eq_sum]
  refine Finset.sum_eq_zero fun u _ ↦ ?_
  have horth := rsCode_le_orthogonal hw
  rw [LinearMap.BilinForm.mem_orthogonal_iff] at horth
  have hX : evalDomain (novelX u) ∈ rsCode :=
    mem_rsCode.mpr ⟨novelX u, (AdditiveNTT.basisVectors (ZMod 2) basis 14 (by norm_num) u).2, rfl⟩
  have h0 : novelCoeff w u = 0 := by
    have := horth _ hX
    change dotForm (evalDomain (novelX u)) w = 0 at this
    rwa [dotForm_apply] at this
  simp [h0]

/-- **A codeword passes for every challenge.** -/
theorem dot_dual_eq_zero {w : Row} (hw : w ∈ rsCode) (z : E) :
    innerProduct (dualCodewordAt z) w = 0 :=
  dot_dualTensor_eq_zero hw (powersOf z)

/-- The challenges for which a row is orthogonal to the dual codeword. -/
noncomputable def acceptSet (w : Row) : Finset E :=
  Finset.univ.filter fun z ↦ innerProduct (dualCodewordAt z) w = 0

theorem mem_acceptSet {w : Row} {z : E} : z ∈ acceptSet w ↔ innerProduct (dualCodewordAt z) w = 0 := by
  simp [acceptSet]

/-- A nonzero polynomial over a finite field vanishes on at most its degree's number of points.
Generic in the field: at `E`, a hypothesis `z ∈ Finset.univ.filter _` would unfold `Finset.univ`. -/
theorem card_filter_le_natDegree {F : Type*} [Field F] [Fintype F] [DecidableEq F] {p : F[X]}
    (hp : p ≠ 0) (f : F → Prop) [DecidablePred f] (hf : ∀ z, f z → p.eval z = 0) :
    (Finset.univ.filter f).card ≤ p.natDegree := by
  have hsub : Finset.univ.filter f ⊆ p.roots.toFinset := by
    refine Finset.subset_iff.mpr fun z hz ↦ ?_
    rw [Multiset.mem_toFinset, mem_roots hp, IsRoot.def]
    exact hf z (Finset.mem_filter.mp hz).2
  exact (Finset.card_le_card hsub).trans ((Multiset.toFinset_card_le _).trans (card_roots' _))

/-- **A row that is not a codeword is orthogonal to the dual codeword for at most `2^14 - 1`
challenges**, the roots of its membership polynomial (`membership.rs:12-14`). -/
theorem card_acceptSet_le {w : Row} (hw : w ∉ rsCode) : (acceptSet w).card ≤ 2 ^ 14 - 1 := by
  obtain ⟨u₀, hu₀⟩ : ∃ u, novelCoeff w u ≠ 0 := by
    by_contra h
    push Not at h
    exact hw (mem_rsCode_of_orthogonal h)
  exact (card_filter_le_natDegree (membershipPoly_ne_zero hu₀) _
    fun z hz ↦ (eval_membershipPoly w z).trans hz).trans (natDegree_membershipPoly_le w)

end

end LeanDa
