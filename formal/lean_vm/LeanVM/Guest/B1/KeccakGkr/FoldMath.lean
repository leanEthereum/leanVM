/-
  LeanVM.Guest.B1.KeccakGkr.FoldMath

  `fold_shifts` (G:2628-2642) as math: `Σ_w eq(a, w) V[w - r]` for every `r` at once, a bit of
  `w` at a time.
-/

module

public import LeanVM.Guest.B1.KeccakGkr.ShiftMath

namespace LeanVM.Protocol.KeccakGkr

open LeanVM.Parameters LeanVM.Protocol.Verifier Finset

@[expose] public section

/-- Node `p` (the residue of `r` mod `2^t`), cell `k`, of level `t`: the first `t` bits of `w`
folded. -/
def foldF (a : List E) (S : ℕ → E) (t p k : ℕ) : E :=
  ∑ u ∈ range (2 ^ t), eqAt (a.take t) u * S ((u + 2 ^ t * k + 64 - p) % 64)

theorem foldF_zero (a : List E) (S : ℕ → E) {k : ℕ} (hk : k < 64) : foldF a S 0 0 k = S k := by
  simp [foldF, Nat.mod_eq_of_lt hk]

theorem take_succ_snoc (a : List E) {t : ℕ} (ht : t < a.length) :
    a.take (t + 1) = a.take t ++ [a.getD t 0] := by
  rw [List.take_add_one, List.getElem?_eq_getElem ht, List.getD_eq_getElem _ _ ht]
  rfl

/-- **One level of the fold** (`fold_node`). -/
theorem foldF_succ (a : List E) (ha : a.length = 6) (S : ℕ → E) {t p b k : ℕ} (ht : t < 6)
    (hp : p < 2 ^ t) (hb : b < 2) (hk : k < 2 ^ (5 - t)) :
    foldF a S (t + 1) (p + 2 ^ t * b) k =
      (1 + a.getD t 0) * foldF a S t p ((2 * k + (2 ^ (6 - t) - 1) * b) % 2 ^ (6 - t)) +
        a.getD t 0 * foldF a S t p ((2 * k + 1 + (2 ^ (6 - t) - 1) * b) % 2 ^ (6 - t)) := by
  have hlen : (a.take t).length = t := by simp [ha]; omega
  unfold foldF
  rw [sum_range_two_pow_succ, Finset.sum_range_succ, Finset.sum_range_one, Finset.mul_sum,
    Finset.mul_sum, take_succ_snoc a (by omega)]
  have e1 : ∀ u ∈ range (2 ^ t), eqAt (a.take t ++ [a.getD t 0]) (u + 2 ^ t * 0) =
      eqAt (a.take t) u * eq1 (a.getD t 0) 0 := fun u hu ↦ by
    have := eqAt_snoc (a.take t) (a.getD t 0) 0 (x := u) (by rw [hlen]; exact Finset.mem_range.1 hu)
    rwa [hlen] at this
  have e2 : ∀ u ∈ range (2 ^ t), eqAt (a.take t ++ [a.getD t 0]) (u + 2 ^ t * 1) =
      eqAt (a.take t) u * eq1 (a.getD t 0) 1 := fun u hu ↦ by
    have := eqAt_snoc (a.take t) (a.getD t 0) 1 (x := u) (by rw [hlen]; exact Finset.mem_range.1 hu)
    rwa [hlen] at this
  refine congrArg₂ (· + ·) (Finset.sum_congr rfl fun u hu ↦ ?_)
    (Finset.sum_congr rfl fun u hu ↦ ?_)
  · have hu' := Finset.mem_range.1 hu
    rw [e1 u hu]
    simp only [eq1, Nat.zero_mod, zero_ne_one, ↓reduceIte]
    rw [show (u + 2 ^ t * 0 + 2 ^ (t + 1) * k + 64 - (p + 2 ^ t * b)) % 64 =
        (u + 2 ^ t * ((2 * k + (2 ^ (6 - t) - 1) * b) % 2 ^ (6 - t)) + 64 - p) % 64 by
      interval_cases t <;> interval_cases b <;> simp at hp hk ⊢ <;> omega]
    ring
  · have hu' := Finset.mem_range.1 hu
    rw [e2 u hu]
    simp only [eq1, Nat.one_mod, ↓reduceIte]
    rw [show (u + 2 ^ t * 1 + 2 ^ (t + 1) * k + 64 - (p + 2 ^ t * b)) % 64 =
        (u + 2 ^ t * ((2 * k + 1 + (2 ^ (6 - t) - 1) * b) % 2 ^ (6 - t)) + 64 - p) % 64 by
      interval_cases t <;> interval_cases b <;> simp at hp hk ⊢ <;> omega]
    ring

/-- **The shifts** at the last level: `Σ_z V[z]·eq(a, z + r)`. -/
theorem foldF_six (a : List E) (ha : a.length = 6) (S : ℕ → E) {r : ℕ} (hr : r < 64) :
    foldF a S 6 r 0 = ∑ z ∈ range 64, S z * eqAt a ((z + r) % 64) := by
  unfold foldF
  rw [show a.take 6 = a by rw [← ha]; exact List.take_length, show (2 : ℕ) ^ 6 = 64 from rfl]
  refine Finset.sum_nbij' (fun u ↦ (u + 64 - r) % 64) (fun z ↦ (z + r) % 64) ?_ ?_ ?_ ?_ ?_
  · intro u _; simp only [Finset.mem_range]; exact Nat.mod_lt _ (by norm_num)
  · intro z _; simp only [Finset.mem_range]; exact Nat.mod_lt _ (by norm_num)
  · intro u hu; have := Finset.mem_range.1 hu; omega
  · intro z hz; have := Finset.mem_range.1 hz; omega
  · intro u hu
    have := Finset.mem_range.1 hu
    simp only [mul_zero, add_zero]
    rw [show ((u + 64 - r) % 64 + r) % 64 = u by omega, mul_comm]

end
end LeanVM.Protocol.KeccakGkr
