/-
The closed form of Theorem 6.1 of the paper:
`N(n - d) ≤ ∑_{k ≤ min(b, r)} C(b, k) (L - 1)^k ≤ C(b + r, r) L^r` with
`b = ⌊(n - a)/(a - d)⌋` and `r = ⌊log₂((n - d)/(a - d))⌋`.

The paper proves it by counting root-to-leaf paths. Here it is an induction on the recursion,
through Pascal's rule `M(b + 1, r + 1) = M(b, r + 1) + x M(b, r)` for
`M(b, r) = ∑_{k ≤ r} C(b, k) x^k`.
-/
import Interleave.ReedSolomon

open Finset

namespace Interleave

/-- `M(b, r) = ∑_{k ≤ r} C(b, k) x^k`. -/
def treeSum (x b r : ℕ) : ℕ := ∑ k ∈ range (r + 1), b.choose k * x ^ k

/-- The sum stops at `min(b, r)`, as written in the paper. -/
theorem treeSum_eq_min (x b r : ℕ) :
    treeSum x b r = ∑ k ∈ range (min b r + 1), b.choose k * x ^ k := by
  symm
  refine sum_subset (range_mono (by omega)) fun k hk hk' => ?_
  rw [mem_range] at hk hk'
  rw [Nat.choose_eq_zero_of_lt (by omega), zero_mul]

theorem treeSum_pos (x b r : ℕ) : 1 ≤ treeSum x b r := by
  have h := single_le_sum (f := fun k => b.choose k * x ^ k) (fun _ _ => Nat.zero_le _)
    (mem_range.mpr (Nat.succ_pos r))
  simp only [Nat.choose_zero_right, pow_zero, mul_one] at h
  exact h

theorem treeSum_mono_left (x : ℕ) {b b' : ℕ} (h : b ≤ b') (r : ℕ) :
    treeSum x b r ≤ treeSum x b' r :=
  sum_le_sum fun k _ => Nat.mul_le_mul_right _ (Nat.choose_le_choose k h)

theorem treeSum_mono_right (x b : ℕ) {r r' : ℕ} (h : r ≤ r') :
    treeSum x b r ≤ treeSum x b r' :=
  sum_le_sum_of_subset (range_mono (by omega))

/-- Pascal's rule. -/
theorem treeSum_succ_succ (x b r : ℕ) :
    treeSum x (b + 1) (r + 1) = treeSum x b (r + 1) + x * treeSum x b r := by
  unfold treeSum
  rw [sum_range_succ' _ (r + 1), sum_range_succ' _ (r + 1), mul_sum, add_right_comm,
    ← sum_add_distrib]
  simp only [Nat.choose_zero_right, pow_zero, mul_one, add_left_inj]
  refine sum_congr rfl fun k _ => ?_
  rw [Nat.choose_succ_succ']
  ring

/-- The recursion is bounded by the sum: `N(P) ≤ M(⌊(P - g)/g⌋, ⌊log₂⌊P/g⌋⌋)` at `x = L - 1`. -/
theorem treeN_le_treeSum (L : ℕ) {g : ℕ} (hg : 0 < g) (P : ℕ) :
    treeN L g P ≤ treeSum (L - 1) ((P - g) / g) (Nat.log 2 (P / g)) := by
  induction P using Nat.strong_induction_on with
  | _ P ih =>
    by_cases h : 2 * g ≤ P
    · have hq : 2 ≤ P / g := (Nat.le_div_iff_mul_le hg).mpr h
      obtain ⟨r, hr⟩ : ∃ r, Nat.log 2 (P / g) = r + 1 :=
        ⟨Nat.log 2 (P / g) - 1, by have := Nat.log_pos (b := 2) (by omega) hq; omega⟩
      have hb : (P - g) / g = (P - g - g) / g + 1 := by
        rw [← Nat.add_div_right _ hg, Nat.sub_add_cancel (by omega)]
      have h1 : treeN L g (P - g) ≤ treeSum (L - 1) ((P - g - g) / g) (r + 1) := by
        refine (ih (P - g) (by omega)).trans (treeSum_mono_right _ _ ?_)
        rw [← hr]
        exact Nat.log_mono_right (Nat.div_le_div_right (Nat.sub_le P g))
      have h2 : treeN L g (P / 2) ≤ treeSum (L - 1) ((P - g - g) / g) r := by
        have hlog : Nat.log 2 (P / 2 / g) = r := by
          rw [Nat.div_div_eq_div_mul, mul_comm, ← Nat.div_div_eq_div_mul, Nat.log_div_base, hr,
            Nat.add_sub_cancel]
        refine (ih (P / 2) (by omega)).trans ?_
        rw [hlog]
        exact treeSum_mono_left _ (Nat.div_le_div_right (by omega)) r
      rw [treeN_of_le hg h, hr, hb, treeSum_succ_succ]
      exact Nat.add_le_add h1 (Nat.mul_le_mul_left _ h2)
    · rw [treeN_of_lt (by omega)]
      exact treeSum_pos _ _ _

/-- Vandermonde: `∑_{k ≤ r} C(b, k) ≤ C(b + r, r)`. -/
theorem sum_choose_le (b r : ℕ) : ∑ k ∈ range (r + 1), b.choose k ≤ (b + r).choose r := by
  rw [Nat.add_choose_eq, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  refine sum_le_sum fun k hk => ?_
  have hk' : k ≤ r := Nat.lt_succ_iff.mp (mem_range.mp hk)
  exact Nat.le_mul_of_pos_right _ (Nat.choose_pos (Nat.sub_le r k))

/-- The sum is at most `C(b + r, r) L^r`. -/
theorem treeSum_le_choose_mul_pow {L : ℕ} (hL : 1 ≤ L) (b r : ℕ) :
    treeSum (L - 1) b r ≤ (b + r).choose r * L ^ r := by
  refine le_trans ?_ (Nat.mul_le_mul_right _ (sum_choose_le b r))
  rw [sum_mul]
  refine sum_le_sum fun k hk => Nat.mul_le_mul_left _ ?_
  have hk' : k ≤ r := Nat.lt_succ_iff.mp (mem_range.mp hk)
  exact (Nat.pow_le_pow_left (Nat.sub_le L 1) k).trans (Nat.pow_le_pow_right hL hk')

/-- The closed form of the bound of Theorem 6.1 of the paper, in its parameters:
`N(n - d) ≤ ∑_{k ≤ r} C(b, k) (L - 1)^k` with `b = ⌊(n - a)/(a - d)⌋`,
`r = ⌊log₂⌊(n - d)/(a - d)⌋⌋`. -/
theorem treeN_le_closed (L : ℕ) {n d a : ℕ} (hda : d < a) :
    treeN L (a - d) (n - d) ≤
      treeSum (L - 1) ((n - a) / (a - d)) (Nat.log 2 ((n - d) / (a - d))) := by
  have h := treeN_le_treeSum L (g := a - d) (by omega) (n - d)
  have e : n - d - (a - d) = n - a := by omega
  rwa [e] at h

/-- `N(n - d) ≤ C(b + r, r) L^r`. -/
theorem treeN_le_choose_mul_pow {L : ℕ} (hL : 1 ≤ L) {n d a : ℕ} (hda : d < a) :
    treeN L (a - d) (n - d) ≤
      ((n - a) / (a - d) + Nat.log 2 ((n - d) / (a - d))).choose
          (Nat.log 2 ((n - d) / (a - d))) * L ^ Nat.log 2 ((n - d) / (a - d)) :=
  (treeN_le_closed L hda).trans (treeSum_le_choose_mul_pow hL _ _)

variable {ι α : Type*} {D : Finset ι} {C : Set (ι → α)} {d a L : ℕ}

/-- Theorem 6.1 of the paper with the closed form `∑_{k ≤ min(b, r)} C(b, k) (L - 1)^k`. -/
theorem interleave_listBound_closed (hC : AgreeLE D C d) (hda : d < a)
    (hL : ListBound D C a L) (m : Type*) [Finite m] :
    ListBound D (interleave m C) a
      (treeSum (L - 1) ((D.card - a) / (a - d)) (Nat.log 2 ((D.card - d) / (a - d)))) :=
  (interleave_listBound hC hda hL m).mono le_rfl (treeN_le_closed L hda)

/-- Theorem 6.1 of the paper with the closed form `C(b + r, r) L^r`, the form of [GGR11] and of
[ABF26, Lemma 2.10] with floors in place of ceilings. -/
theorem interleave_listBound_choose (hC : AgreeLE D C d) (hda : d < a)
    (hL : ListBound D C a L) (m : Type*) [Finite m] [Nonempty m] :
    ListBound D (interleave m C) a
      (((D.card - a) / (a - d) + Nat.log 2 ((D.card - d) / (a - d))).choose
          (Nat.log 2 ((D.card - d) / (a - d))) * L ^ Nat.log 2 ((D.card - d) / (a - d))) := by
  rcases Nat.eq_zero_or_pos L with rfl | hpos
  · exact (hL.interleave_zero m).mono le_rfl (Nat.zero_le _)
  · exact (interleave_listBound hC hda hL m).mono le_rfl (treeN_le_choose_mul_pow hpos hda)

/-- The closed form for Reed-Solomon codes, lanes and extensions. -/
theorem rs_interleave_closed {K : Type*} [Field K] {D : Finset K} {d a L : ℕ}
    (F : Type*) [CommRing F] [Algebra K F] [Module.Finite K F] (lanes : Type*) [Finite lanes]
    (hL : RSListBound₁ D d a L) (hda : d < a) :
    RSListBound D F lanes d a
      (treeSum (L - 1) ((D.card - a) / (a - d)) (Nat.log 2 ((D.card - d) / (a - d)))) :=
  fun w S hS => (rs_interleave F lanes hL hda w S hS).trans (treeN_le_closed L hda)

end Interleave
