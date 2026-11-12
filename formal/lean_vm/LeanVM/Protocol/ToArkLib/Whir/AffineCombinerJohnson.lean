/-
  LeanVM.Protocol.ToArkLib.Whir.AffineCombinerJohnson

  The Johnson count `jl n a r`, in natural numbers, for set systems. Candidate for ArkLib.
-/

module

public import Mathlib.Algebra.Order.Chebyshev
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Tactic

/-!
# The Johnson count

Annex B of the leanVM specification (`doc/leanvm/body/b-polynomial-commitment-scheme.tex`),
`thm:johnson-general`, and [CYWZ26, preprint], Lemma 3.11, in the integer form the Rust analysis
evaluates (`crates/pcs/src/whir_config/affine_mca.rs`, `johnson_list(n, a, r)`):

* `jl n a r = ⌊n (a - r) / (a² - n r)⌋`;
* `card_le_jl`: a family of sets of at least `a` points of an `n`-set, meeting pairwise in at most
  `r` points, has at most `jl n a r` members when `a² > n r`.

The proof is the double count of `LeanVM.Protocol.Whir.johnson_count` (Cauchy-Schwarz on the
incidence counts), repeated here so that the affine-combiner files depend on Mathlib alone.
-/

namespace LeanVM.Protocol.Whir.AffineCombiner

open Finset

@[expose] public section

/-- **The Johnson count** `⌊n (a - r) / (a² - n r)⌋` (`johnson_list(n, a, r)` in the Rust): at most
this many sets of at least `a` points of an `n`-set meet pairwise in at most `r` points, when
`a² > n r` (`card_le_jl`). -/
def jl (n a r : ℕ) : ℕ := n * (a - r) / (a * a - n * r)

section SetSystem

variable {ι β : Type*} [Fintype ι] [DecidableEq ι] [DecidableEq β]

/-- The double count: `L` sets of exactly `a` points of an `n`-set, pairwise meeting in at most `r`
points, satisfy `(|L| a)² ≤ n (|L| a + |L| (|L| - 1) r)`. -/
theorem jl_count (L : Finset β) (S : β → Finset ι) (a r : ℕ)
    (ha : ∀ b ∈ L, (S b).card = a)
    (hr : ∀ b ∈ L, ∀ b' ∈ L, b ≠ b' → (S b ∩ S b').card ≤ r) :
    (L.card * a) ^ 2 ≤ Fintype.card ι * (L.card * a + L.card * (L.card - 1) * r) := by
  set d : ι → ℕ := fun i ↦ ∑ b ∈ L, if i ∈ S b then 1 else 0 with hd
  have hcard (T : Finset ι) : ∑ i, (if i ∈ T then 1 else 0 : ℕ) = T.card := by
    rw [Finset.sum_boole]
    simp
  have h1 : ∑ i, d i = L.card * a := by
    rw [hd, Finset.sum_comm, Finset.sum_congr rfl fun b hb ↦ (hcard (S b)).trans (ha b hb)]
    simp
  have h2 : ∑ i, d i ^ 2 = ∑ b ∈ L, ∑ b' ∈ L, (S b ∩ S b').card := by
    simp_rw [hd, sq, Finset.sum_mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun b _ ↦ ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun b' _ ↦ ?_
    rw [← hcard]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    by_cases h : i ∈ S b <;> by_cases h' : i ∈ S b' <;> simp [h, h']
  have h3 : ∑ b ∈ L, ∑ b' ∈ L, (S b ∩ S b').card ≤ L.card * a + L.card * (L.card - 1) * r := by
    calc
      _ ≤ ∑ b ∈ L, (a + (L.card - 1) * r) := by
        refine Finset.sum_le_sum fun b hb ↦ ?_
        rw [← Finset.add_sum_erase L _ hb, Finset.inter_self, ha b hb]
        refine Nat.add_le_add_left ?_ a
        calc
          _ ≤ ∑ _b' ∈ L.erase b, r := Finset.sum_le_sum fun b' hb' ↦
                hr b hb b' (Finset.mem_of_mem_erase hb') (Finset.ne_of_mem_erase hb').symm
          _ = (L.card - 1) * r := by rw [Finset.sum_const, Finset.card_erase_of_mem hb,
                smul_eq_mul]
      _ = _ := by rw [Finset.sum_const, smul_eq_mul]; ring
  calc
    (L.card * a) ^ 2 = (∑ i, d i) ^ 2 := by rw [h1]
    _ ≤ (univ : Finset ι).card * ∑ i, d i ^ 2 := sq_sum_le_card_mul_sum_sq
    _ ≤ _ := by
      rw [Finset.card_univ, h2]
      exact Nat.mul_le_mul_left _ h3

/-- The double count for sets of at least `a` points: each set is shrunk to `a` of its points. -/
theorem jl_count_of_le (L : Finset β) (T : β → Finset ι) (a r : ℕ)
    (ha : ∀ b ∈ L, a ≤ (T b).card)
    (hr : ∀ b ∈ L, ∀ b' ∈ L, b ≠ b' → (T b ∩ T b').card ≤ r) :
    (L.card * a) ^ 2 ≤ Fintype.card ι * (L.card * a + L.card * (L.card - 1) * r) := by
  have hex (b : β) : ∃ S : Finset ι, b ∈ L → S ⊆ T b ∧ S.card = a := by
    by_cases hb : b ∈ L
    · obtain ⟨S, hS, hcard⟩ := Finset.exists_subset_card_eq (ha b hb)
      exact ⟨S, fun _ ↦ ⟨hS, hcard⟩⟩
    · exact ⟨∅, fun h ↦ absurd h hb⟩
  choose S hS using hex
  refine jl_count L S a r (fun b hb ↦ (hS b hb).2) fun b hb b' hb' hne ↦ ?_
  exact (Finset.card_le_card (Finset.inter_subset_inter (hS b hb).1 (hS b' hb').1)).trans
    (hr b hb b' hb' hne)

/-- **Johnson bound, integer form** (Annex B, `thm:johnson-general`; [CYWZ26, Lemma 3.11]): a
family of sets of at least `a` points of an `n`-set, meeting pairwise in at most `r` points, has
at most `jl n a r` members when `a² > n r`. -/
theorem card_le_jl (L : Finset β) (T : β → Finset ι) (a r : ℕ)
    (ha : ∀ b ∈ L, a ≤ (T b).card)
    (hr : ∀ b ∈ L, ∀ b' ∈ L, b ≠ b' → (T b ∩ T b').card ≤ r)
    (hgap : Fintype.card ι * r < a * a) :
    L.card ≤ jl (Fintype.card ι) a r := by
  set n := Fintype.card ι
  rcases L.eq_empty_or_nonempty with rfl | ⟨b₀, hb₀⟩
  · simp
  have han : a ≤ n := (ha b₀ hb₀).trans (Finset.card_le_univ _)
  have hra : r ≤ a := by
    by_contra h
    have : a * a ≤ n * r := Nat.mul_le_mul han (not_le.mp h).le
    omega
  have hN : 1 ≤ L.card := Finset.card_pos.mpr ⟨b₀, hb₀⟩
  have hcount := jl_count_of_le L T a r ha hr
  unfold jl
  rw [Nat.le_div_iff_mul_le (by omega)]
  -- Divide the double count by `|L|`, in the integers.
  set N := L.card
  have hz : ((N : ℤ) * a) ^ 2 ≤ n * (N * a + N * (N - 1) * r) := by
    have := (Nat.cast_le (α := ℤ)).mpr hcount
    push_cast [Nat.cast_sub hN] at this
    linarith
  have hNpos : (0 : ℤ) < N := by exact_mod_cast hN
  have hdiv : (N : ℤ) * (a * a - n * r) ≤ n * (a - r) := by
    have h₁ : (N : ℤ) * ((N : ℤ) * (a * a - n * r)) ≤ N * (n * (a - r)) := by nlinarith
    exact le_of_mul_le_mul_left h₁ hNpos
  have hsub1 : ((a * a - n * r : ℕ) : ℤ) = a * a - n * r := by
    rw [Nat.cast_sub (by omega)]; push_cast; ring
  have hsub2 : ((a - r : ℕ) : ℤ) = a - r := by rw [Nat.cast_sub hra]
  have : ((N * (a * a - n * r) : ℕ) : ℤ) ≤ ((n * (a - r) : ℕ) : ℤ) := by
    push_cast [hsub1, hsub2]
    linarith
  exact_mod_cast this

end SetSystem

end
end LeanVM.Protocol.Whir.AffineCombiner
