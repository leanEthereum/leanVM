/-
Unions of flats share the top of `X ^ (n / 2) L_W`: the family of Proposition 3.4(a) of the paper,
described by unions of flats (Section 3.4).

`FlatUnion W S i M` says that `S` is a disjoint union of `i` cosets of `W` and of free flats, each
of size at least `2 |W|`, of total size `M`. Then `L_S = L_W ^ i X ^ M + (degree ≤ |S| - |W|)`
(`FlatUnion.hasGap`), and for odd `i` the top is that of `X ^ (|S| - |W|) L_W`
(`FlatUnion.natDegree_le`). With `|S| = 5 |W|` the number of cosets is odd, so every such union
has `L_S = X ^ (4 |W|) L_W + C_S` with `deg C_S ≤ 4 |W|` (`flatUnion_five_eighths`): for
`|W| = n / 8` every such union shares the top of its word, and `C_S` is in the list of the word
`x ↦ x ^ (n / 2) L_W(x)` at degree at most `n / 2` and agreement `5n/8`
(`flatUnion_mem_RSList`).
-/
import Constructions.Gap

open Polynomial
open scoped Classical

namespace Constructions

variable {K : Type*} [Field K]

theorem HasGap.mono {p A : K[X]} {n g g' : ℕ} (h : HasGap p A n g) (hg : g' ≤ g) :
    HasGap p A n g' := fun m hm => h m (by omega)

theorem HasGap.trans {p A B : K[X]} {n g : ℕ} (h : HasGap p A n g) (h' : HasGap A B n g) :
    HasGap p B n g := fun m hm => by
  have e : p - B = (p - A) + (A - B) := by ring
  rw [e, coeff_add, h m hm, h' m hm, add_zero]

theorem HasGap.pow {p A : K[X]} {n g : ℕ} (h : HasGap p A n g) (hA : A.natDegree ≤ n)
    (hp : p.natDegree ≤ n) (j : ℕ) : HasGap (p ^ j) (A ^ j) (j * n) g := by
  induction j with
  | zero =>
    intro m _
    simp
  | succ j ih =>
    rw [pow_succ, pow_succ, Nat.succ_mul]
    exact ih.mul h (natDegree_pow_le.trans (Nat.mul_le_mul_left _ hA)) hp

/-- A disjoint union of `i` cosets of `W` and of free flats of size at least `2 |W|` and total
size `M`. -/
inductive FlatUnion (W : AddSubgroup K) : Finset K → ℕ → ℕ → Prop
  | empty : FlatUnion W ∅ 0 0
  | coset {S : Finset K} {i M : ℕ} (a : K) : FlatUnion W S i M → Disjoint S (flat W a) →
      FlatUnion W (S ∪ flat W a) (i + 1) M
  | free {S : Finset K} {i M : ℕ} (V : AddSubgroup K) (b : K) : Finite V →
      2 * Nat.card W ≤ Nat.card V → FlatUnion W S i M → Disjoint S (flat V b) →
      FlatUnion W (S ∪ flat V b) i (M + Nat.card V)

theorem FlatUnion.card {W : AddSubgroup K} [Finite W] {S : Finset K} {i M : ℕ}
    (h : FlatUnion W S i M) : S.card = i * Nat.card W + M := by
  induction h with
  | empty => simp
  | coset a _ hd ih =>
    rw [Finset.card_union_of_disjoint hd, card_flat, ih]
    ring
  | free V b hV _ _ hd ih =>
    rw [Finset.card_union_of_disjoint hd, card_flat, ih]
    ring

section CharTwo

variable [CharP K 2]

/-- The free flats have sizes divisible by `2 |W|`. -/
theorem FlatUnion.dvd {W : AddSubgroup K} [Finite W] {S : Finset K} {i M : ℕ}
    (h : FlatUnion W S i M) : 2 * Nat.card W ∣ M := by
  induction h with
  | empty => exact dvd_zero _
  | coset a _ _ ih => exact ih
  | free V b hV hle _ _ ih =>
    refine dvd_add ih ?_
    obtain ⟨u, hu⟩ := exists_card_eq_two_pow W
    obtain ⟨v, hv⟩ := exists_card_eq_two_pow V
    rw [hu, hv, ← pow_succ'] at hle ⊢
    exact pow_dvd_pow 2 ((Nat.pow_le_pow_iff_right (by norm_num)).mp hle)

/-- `L_S = L_W ^ i X ^ M + (degree at most |S| - |W|)`. -/
theorem FlatUnion.hasGap {W : AddSubgroup K} [Finite W] {S : Finset K} {i M : ℕ}
    (h : FlatUnion W S i M) :
    HasGap (locator S) (subPoly W ^ i * X ^ M) S.card (Nat.card W) := by
  induction h with
  | empty =>
    intro m _
    simp [locator]
  | @coset S i M a hS hd ih =>
    have hA : (subPoly W ^ i * X ^ M).natDegree ≤ S.card := by
      rw [hS.card]
      refine natDegree_mul_le.trans (Nat.add_le_add ?_ (natDegree_X_pow_le M))
      exact natDegree_pow_le.trans (by rw [subPoly_natDegree])
    have h2 := ih.mul (hasGap_coset W a) hA (by rw [locator_natDegree, card_flat])
    rw [locator_union hd, Finset.card_union_of_disjoint hd, card_flat]
    rwa [show subPoly W ^ (i + 1) * X ^ M = subPoly W ^ i * X ^ M * subPoly W by ring]
  | @free S i M V b hV hle hS hd ih =>
    have hA : (subPoly W ^ i * X ^ M).natDegree ≤ S.card := by
      rw [hS.card]
      refine natDegree_mul_le.trans (Nat.add_le_add ?_ (natDegree_X_pow_le M))
      exact natDegree_pow_le.trans (by rw [subPoly_natDegree])
    have h2 := ih.mul ((hasGap_flat V b).mono (by omega)) hA
      (by rw [locator_natDegree, card_flat])
    rw [locator_union hd, Finset.card_union_of_disjoint hd, card_flat]
    rwa [show subPoly W ^ i * X ^ (M + Nat.card V) = subPoly W ^ i * X ^ M * X ^ Nat.card V by
      ring]

/-- `L_W² = X ^ (2 |W|) + (degree at most |W|)`. -/
theorem hasGap_subPoly_sq (W : AddSubgroup K) [Finite W] :
    HasGap (subPoly W ^ 2) (X ^ (2 * Nat.card W)) (2 * Nat.card W) (Nat.card W) := by
  refine hasGap_of_natDegree_le ?_
  have h2 : (2 : K[X]) = 0 := by
    rw [← C_ofNat, CharTwo.two_eq_zero, C_0]
  have e : subPoly W ^ 2 - X ^ (2 * Nat.card W) = (subPoly W - X ^ Nat.card W) ^ 2 := by
    linear_combination (subPoly W * X ^ Nat.card W - X ^ (2 * Nat.card W)) * h2
  rw [e]
  have h := natDegree_pow_le (p := subPoly W - X ^ Nat.card W) (n := 2)
  have h3 := natDegree_subPoly_sub_le W
  omega

/-- An odd power of `L_W` has the top of `L_W X ^ (2j |W|)`. -/
theorem hasGap_subPoly_odd_pow (W : AddSubgroup K) [Finite W] (j M : ℕ) :
    HasGap (subPoly W ^ (2 * j + 1) * X ^ M) (subPoly W * X ^ (M + 2 * j * Nat.card W))
      ((2 * j + 1) * Nat.card W + M) (Nat.card W) := by
  have h1 := (hasGap_subPoly_sq W).pow (natDegree_X_pow_le _)
    (natDegree_pow_le.trans (by rw [subPoly_natDegree])) j
  have h2 := h1.mul (hasGap_self (subPoly W) (Nat.card W) (Nat.card W))
    (natDegree_pow_le.trans (Nat.mul_le_mul_left _ (natDegree_X_pow_le _)))
    (by rw [subPoly_natDegree])
  have h3 := h2.mul (hasGap_self (X ^ M) M (Nat.card W))
    (natDegree_mul_le.trans (Nat.add_le_add
      (natDegree_pow_le.trans (Nat.mul_le_mul_left _ (natDegree_X_pow_le _)))
      (by rw [subPoly_natDegree]))) (natDegree_X_pow_le M)
  have e1 : (subPoly W ^ 2) ^ j * subPoly W * X ^ M = subPoly W ^ (2 * j + 1) * X ^ M := by ring
  have e2 : (X ^ (2 * Nat.card W)) ^ j * subPoly W * X ^ M =
      subPoly W * X ^ (M + 2 * j * Nat.card W) := by ring
  have e3 : j * (2 * Nat.card W) + Nat.card W + M = (2 * j + 1) * Nat.card W + M := by ring
  rwa [e1, e2, e3] at h3

/-- **The common top of a union of flats, general form.** A disjoint union `S` of an odd number
of cosets of `W` and of flats of size at least `2 |W|` has
`L_S = X ^ (|S| - |W|) L_W + (degree at most |S| - |W|)`. -/
theorem FlatUnion.natDegree_le {W : AddSubgroup K} [Finite W] {S : Finset K} {j M : ℕ}
    (h : FlatUnion W S (2 * j + 1) M) :
    (locator S - subPoly W * X ^ (S.card - Nat.card W)).natDegree ≤ S.card - Nat.card W := by
  have hc := h.card
  have h1 := h.hasGap
  have h2 := hasGap_subPoly_odd_pow W j M
  rw [← hc] at h2
  have e : S.card - Nat.card W = M + 2 * j * Nat.card W := by
    rw [hc]
    have : (2 * j + 1) * Nat.card W = 2 * j * Nat.card W + Nat.card W := by ring
    omega
  rw [e]
  have h3 := (h1.trans h2).natDegree_le
  rwa [e] at h3

/-- **The common top at `|S| = 5 |W|`** (the family of Proposition 3.4(a) of the paper as unions
of flats). Every disjoint union `S` of cosets of `W` and of flats of size at least `2 |W|` with
`|S| = 5 |W|` has `L_S = X ^ (4 |W|) L_W + C_S` with `deg C_S ≤ 4 |W|`. For `|W| = n / 8`:
`L_S = X ^ (n / 2) L_W + C_S`, `deg C_S ≤ n / 2`, `|S| = 5n/8`. -/
theorem flatUnion_five_eighths {W : AddSubgroup K} [Finite W] {S : Finset K} {i M : ℕ}
    (h : FlatUnion W S i M) (hS : S.card = 5 * Nat.card W) :
    (locator S - subPoly W * X ^ (4 * Nat.card W)).natDegree ≤ 4 * Nat.card W := by
  have hc := h.card
  obtain ⟨q, hq⟩ := h.dvd
  have hW : 0 < Nat.card W := by
    rw [← card_pts]
    exact card_pts_pos W
  have hi : i + 2 * q = 5 := by
    have e : (i + 2 * q) * Nat.card W = 5 * Nat.card W := by
      rw [← hS, hc, hq]
      ring
    exact Nat.eq_of_mul_eq_mul_right hW e
  obtain ⟨j, rfl⟩ : ∃ j, i = 2 * j + 1 := ⟨(i - 1) / 2, by omega⟩
  have h1 := h.natDegree_le
  rwa [hS, show 5 * Nat.card W - Nat.card W = 4 * Nat.card W by omega] at h1

/-- `flatUnion_five_eighths` as a list statement: for `S ⊆ D` as above, the polynomial
`C_S = X ^ (4 |W|) L_W - L_S` is in the list of the word `x ↦ x ^ (4 |W|) L_W(x)` at degree at most
`4 |W|` and agreement `5 |W|`. -/
theorem flatUnion_mem_RSList (D : Finset K) {W : AddSubgroup K} [Finite W] {S : Finset K}
    {i M : ℕ} (h : FlatUnion W S i M) (hS : S.card = 5 * Nat.card W) (hSD : S ⊆ D) :
    subPoly W * X ^ (4 * Nat.card W) - locator S ∈
      RSList D (fun x => (subPoly W).eval x * x ^ (4 * Nat.card W))
        (4 * Nat.card W + 1) (5 * Nat.card W) := by
  constructor
  · refine lt_of_le_of_lt degree_le_natDegree ?_
    have h1 := flatUnion_five_eighths h hS
    rw [← natDegree_neg, neg_sub] at h1
    exact_mod_cast Nat.lt_succ_of_le h1
  · rw [← hS]
    refine Finset.card_le_card fun x hx => ?_
    rw [agree, Finset.mem_filter]
    refine ⟨hSD hx, ?_⟩
    simp [locator_eval_eq_zero.mpr hx]

end CharTwo

end Constructions
