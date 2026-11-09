/-
  LeanVM.Protocol.ToArkLib.Whir.Johnson

  The Johnson bound in agreement form, for set systems, interleaved words of a code with bounded
  pairwise agreement, and interleaved Reed-Solomon codes. Candidate for ArkLib.
-/

module

public import LeanVM.Protocol.ToArkLib.Whir.Interleaved
public import ArkLib.Data.CodingTheory.HiddenDerivative.Parameters.Johnson.FiniteBounds
import Mathlib.Algebra.Order.Chebyshev

/-!
# The Johnson bound for interleaved codes

Annex B of the leanVM specification (leanVM `127510d1`,
`doc/leanvm/body/b-polynomial-commitment-scheme.tex`), `thm:johnson-general` and its interleaved
corollary `thm:johnson-interleaved`: if distinct codewords agree on at most `r n` of `n`
coordinates, at most `1 / (2 η √r)` codewords agree with a word on `(√r + η) n` coordinates.

* `johnson_count`: the double count behind the bound, for a set system. If `L` sets of
  size `a` in an `n`-set meet pairwise in at most `r` points, then
  `(|L| a)² ≤ n (|L| a + |L| (|L| - 1) r)`; Cauchy-Schwarz on the incidence counts.
  `johnson_count_of_le` takes sets of size at least `a`.
* `card_mul_johnson_le`: the real form,
  `|L| (2 η √r + η²) ≤ 1 - r` when the sets have at least `(√r + η) n` elements and meet in at
  most `r n`; `card_le_johnson` its corollary `|L| ≤ 1 / (2 η √r)` for `r > 0`.
* `card_iList_mul_le_johnson`, `card_iList_le_johnson`: the bound for the list `iList C A O` of
  an interleaved word, when distinct interleaved codewords agree on at most `d ≤ r n`
  coordinates and `A ≥ (√r + η) n`.
* `card_iList_rs_le_johnson`: the interleaved Reed-Solomon instance, with degree bound `D`
  (dimension `D + 1`) and the slightly reduced rate `ρ₋ = D / n` of ArkLib's Johnson
  parametrization; `card_iList_johnsonAgreement_le` states it at ArkLib's threshold
  `⌈johnsonAgreement n D η * n⌉₊`, the radius `1 - √ρ₋ - η` of
  `mcaError_affineLine_johnson_le` (`iListRad_one_sub_johnsonAgreement`).

The hypotheses are weaker than the Annex's: no upper bound `η < 1 - √r` is needed (beyond it the
list is empty or the bound still holds), and the alphabet and code are arbitrary in the
set-system and list forms. The Annex states the interleaved bound with the rate `k / n`; distinct
Reed-Solomon codewords agree on at most `k - 1 = D` coordinates, so `ρ₋ = D / n` is valid and
the rate `k / n` is a weakening. The reduced rate must be positive (`0 < D`) for the form
`1 / (2 η √ρ₋)`, whose value at `ρ₋ = 0` is `0` in Lean; `card_iList_mul_le_johnson` covers
`r = 0` with the bound `|L| η² ≤ 1`.
-/

namespace LeanVM.Protocol.Whir

open Finset ReedSolomon.HiddenDerivative

@[expose] public section

/-! ## The double count -/

section SetSystem

variable {ι β : Type*} [Fintype ι] [DecidableEq ι] [DecidableEq β]

/-- **Johnson double count.** `L` sets of exactly `a` points of an `n`-set, pairwise meeting in at
most `r` points, satisfy `(|L| a)² ≤ n (|L| a + |L| (|L| - 1) r)`. -/
theorem johnson_count (L : Finset β) (S : β → Finset ι) (a r : ℕ)
    (ha : ∀ b ∈ L, (S b).card = a)
    (hr : ∀ b ∈ L, ∀ b' ∈ L, b ≠ b' → (S b ∩ S b').card ≤ r) :
    (L.card * a) ^ 2 ≤ Fintype.card ι * (L.card * a + L.card * (L.card - 1) * r) := by
  -- `d i` counts the sets through the point `i`.
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

/-- **Johnson double count, at least `a` points.** The same bound for sets of at least `a`
points: each set is shrunk to `a` of its points, which only shrinks the intersections. -/
theorem johnson_count_of_le (L : Finset β) (T : β → Finset ι) (a r : ℕ)
    (ha : ∀ b ∈ L, a ≤ (T b).card)
    (hr : ∀ b ∈ L, ∀ b' ∈ L, b ≠ b' → (T b ∩ T b').card ≤ r) :
    (L.card * a) ^ 2 ≤ Fintype.card ι * (L.card * a + L.card * (L.card - 1) * r) := by
  classical
  have hex (b : β) : ∃ S : Finset ι, b ∈ L → S ⊆ T b ∧ S.card = a := by
    by_cases hb : b ∈ L
    · obtain ⟨S, hS, hcard⟩ := Finset.exists_subset_card_eq (ha b hb)
      exact ⟨S, fun _ ↦ ⟨hS, hcard⟩⟩
    · exact ⟨∅, fun h ↦ absurd h hb⟩
  choose S hS using hex
  refine johnson_count L S a r (fun b hb ↦ (hS b hb).2) fun b hb b' hb' hne ↦ ?_
  exact (Finset.card_le_card (Finset.inter_subset_inter (hS b hb).1 (hS b' hb').1)).trans
    (hr b hb b' hb' hne)

/-- **Johnson bound, real form, nonempty family.** If each of the sets in a nonempty family
`L` has at least `(√r + η) n` points and two distinct ones meet in at most `r n` points, then
`|L| (2 η √r + η²) ≤ 1 - r`. -/
theorem card_mul_johnson_le_of_nonempty (L : Finset β) (T : β → Finset ι) {r η : ℝ}
    (hn : 0 < Fintype.card ι) (hr0 : 0 ≤ r) (hη : 0 ≤ η) (hL : L.Nonempty)
    (ha : ∀ b ∈ L, (√r + η) * Fintype.card ι ≤ (T b).card)
    (hr : ∀ b ∈ L, ∀ b' ∈ L, b ≠ b' → ((T b ∩ T b').card : ℝ) ≤ r * Fintype.card ι) :
    (L.card : ℝ) * (2 * η * √r + η ^ 2) ≤ 1 - r := by
  set n := Fintype.card ι with hnDef
  set a := ⌈(√r + η) * n⌉₊ with haDef
  set m := ⌊r * n⌋₊ with hmDef
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hrn : 0 ≤ r * n := mul_nonneg hr0 hnR.le
  have hcount := johnson_count_of_le L T a m (fun b hb ↦ Nat.ceil_le.mpr (ha b hb))
    fun b hb b' hb' hne ↦ Nat.le_floor (hr b hb b' hb' hne)
  obtain ⟨b₀, hb₀⟩ := hL
  have haN : a ≤ n := (Nat.ceil_le.mpr (ha b₀ hb₀)).trans (Finset.card_le_univ _)
  have hL1 : 1 ≤ L.card := Finset.card_pos.mpr ⟨b₀, hb₀⟩
  -- Real-valued names for the quantities.
  have hLR : (1 : ℝ) ≤ L.card := by exact_mod_cast hL1
  have haR : (√r + η) * n ≤ (a : ℝ) := Nat.le_ceil _
  have haNR : (a : ℝ) ≤ n := by exact_mod_cast haN
  have hmR : (m : ℝ) ≤ r * n := Nat.floor_le hrn
  have hcountR : ((L.card : ℝ) * a) ^ 2 ≤
      n * (L.card * a + L.card * (L.card - 1) * m) := by
    have := (Nat.cast_le (α := ℝ)).mpr hcount
    push_cast [Nat.cast_sub hL1] at this
    linarith
  have hsq : √r * √r = r := Real.mul_self_sqrt hr0
  have hsqnn : 0 ≤ √r := Real.sqrt_nonneg r
  have ha0 : 0 ≤ (√r + η) * n := by positivity
  -- Divide the count by `|L|`: `|L| a² ≤ n a + (|L| - 1) n m`.
  have hdiv : (L.card : ℝ) * a ^ 2 ≤ n * a + (L.card - 1) * n * (r * n) := by
    have h₁ : (L.card : ℝ) * (L.card * a ^ 2) ≤ L.card * (n * a + (L.card - 1) * n * m) := by
      nlinarith
    have h₂ : (L.card : ℝ) * a ^ 2 ≤ n * a + (L.card - 1) * n * m :=
      le_of_mul_le_mul_left h₁ (by linarith)
    have h₃ : ((L.card : ℝ) - 1) * n * m ≤ (L.card - 1) * n * (r * n) :=
      mul_le_mul_of_nonneg_left hmR (mul_nonneg (by linarith) hnR.le)
    linarith
  have hasq : ((√r + η) * n) ^ 2 ≤ (a : ℝ) ^ 2 := pow_le_pow_left₀ ha0 haR 2
  have hkey : (L.card : ℝ) * ((2 * η * √r + η ^ 2) * n ^ 2) ≤ (1 - r) * n ^ 2 := by
    have e : ((√r + η) * n) ^ 2 = (r + (2 * η * √r + η ^ 2)) * n ^ 2 := by
      rw [show ((√r + η) * n) ^ 2 = (√r ^ 2 + (2 * η * √r + η ^ 2)) * n ^ 2 by ring,
        Real.sq_sqrt hr0]
    have hLa : (L.card : ℝ) * ((r + (2 * η * √r + η ^ 2)) * n ^ 2) ≤ L.card * a ^ 2 := by
      rw [← e]; exact mul_le_mul_of_nonneg_left hasq (by linarith)
    nlinarith
  have hn2 : (0 : ℝ) < n ^ 2 := by positivity
  nlinarith

/-- **Johnson bound, real form.** If each of the sets in `L` has at least `(√r + η) n` points and
two distinct ones meet in at most `r n` points, with `0 ≤ r ≤ 1`, then
`|L| (2 η √r + η²) ≤ 1 - r`. -/
theorem card_mul_johnson_le (L : Finset β) (T : β → Finset ι) {r η : ℝ}
    (hn : 0 < Fintype.card ι) (hr0 : 0 ≤ r) (hr1 : r ≤ 1) (hη : 0 ≤ η)
    (ha : ∀ b ∈ L, (√r + η) * Fintype.card ι ≤ (T b).card)
    (hr : ∀ b ∈ L, ∀ b' ∈ L, b ≠ b' → ((T b ∩ T b').card : ℝ) ≤ r * Fintype.card ι) :
    (L.card : ℝ) * (2 * η * √r + η ^ 2) ≤ 1 - r := by
  rcases L.eq_empty_or_nonempty with rfl | hL
  · simp; linarith
  · exact card_mul_johnson_le_of_nonempty L T hn hr0 hη hL ha hr

/-- **Johnson bound** (Annex B, `thm:johnson-general`, set-system form): with `r > 0` and
`η > 0`, at most `1 / (2 η √r)` sets of at least `(√r + η) n` points meet pairwise in at most
`r n` points. -/
theorem card_le_johnson (L : Finset β) (T : β → Finset ι) {r η : ℝ}
    (hn : 0 < Fintype.card ι) (hr0 : 0 < r) (hη : 0 < η)
    (ha : ∀ b ∈ L, (√r + η) * Fintype.card ι ≤ (T b).card)
    (hr : ∀ b ∈ L, ∀ b' ∈ L, b ≠ b' → ((T b ∩ T b').card : ℝ) ≤ r * Fintype.card ι) :
    (L.card : ℝ) ≤ 1 / (2 * η * √r) := by
  have hpos : 0 < 2 * η * √r := by positivity
  rw [le_div_iff₀ hpos]
  rcases L.eq_empty_or_nonempty with rfl | hL
  · simp
  · have := card_mul_johnson_le_of_nonempty L T hn hr0.le hη.le hL ha hr
    nlinarith [sq_nonneg η, Nat.cast_nonneg (α := ℝ) L.card]

end SetSystem

/-! ## Lists of interleaved words -/

/-- Where `O` agrees with both `U` and `V`, `U` and `V` agree with each other. -/
theorem agreeSet_inter_subset {F ι ρ : Type*} [DecidableEq F] [Fintype ι] [DecidableEq ι]
    [Fintype ρ] (O U V : ρ → ι → F) :
    agreeSet O U ∩ agreeSet O V ⊆ agreeSet U V := by
  intro x hx
  rw [Finset.mem_inter, mem_agreeSet, mem_agreeSet] at hx
  exact (mem_agreeSet U V x).mpr fun r ↦ (hx.1 r).symm.trans (hx.2 r)

section List

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {ι ρ : Type*} [Fintype ι]
  [DecidableEq ι] [Fintype ρ]

omit [DecidableEq ι] in
/-- Every list member agrees with `O` on at least the threshold. -/
theorem le_card_agreeSet_of_mem_iList {C : Submodule F (ι → F)} {A : ℕ} {O U : ρ → ι → F}
    (hU : U ∈ iList C A O) : A ≤ (agreeSet O U).card :=
  (isClose_iff_le_card_agreeSet A O U).mp ((mem_iList C A O U).mp hU).2

/-- The hypotheses of the Johnson bound for a list: the threshold and the pairwise agreement. -/
private theorem iList_johnson_hyps (C : Submodule F (ι → F)) (d A : ℕ) {r η : ℝ}
    (hd : (d : ℝ) ≤ r * Fintype.card ι)
    (hdist : ∀ U V : ρ → ι → F, IsInterleavedCodeword C U → IsInterleavedCodeword C V →
      U ≠ V → (agreeSet U V).card ≤ d)
    (hA : (√r + η) * Fintype.card ι ≤ A) (O : ρ → ι → F) :
    (∀ U ∈ iList C A O, (√r + η) * Fintype.card ι ≤ (agreeSet O U).card) ∧
    (∀ U ∈ iList C A O, ∀ V ∈ iList C A O, U ≠ V →
      ((agreeSet O U ∩ agreeSet O V).card : ℝ) ≤ r * Fintype.card ι) := by
  refine ⟨fun U hU ↦ hA.trans (by exact_mod_cast le_card_agreeSet_of_mem_iList hU),
    fun U hU V hV hne ↦ ?_⟩
  have hc := (Finset.card_le_card (agreeSet_inter_subset O U V)).trans
    (hdist U V ((mem_iList C A O U).mp hU).1 ((mem_iList C A O V).mp hV).1 hne)
  exact (by exact_mod_cast hc : ((agreeSet O U ∩ agreeSet O V).card : ℝ) ≤ d).trans hd

/-- **Johnson bound for lists** (Annex B, `thm:johnson-general`): if distinct interleaved
codewords of `C` agree on at most `d ≤ r n` coordinates, with `r > 0`, `η > 0` and the threshold
`A ≥ (√r + η) n`, the list of every interleaved word has at most `1 / (2 η √r)` members. -/
theorem card_iList_le_johnson (C : Submodule F (ι → F)) (d A : ℕ) {r η : ℝ}
    (hn : 0 < Fintype.card ι) (hr0 : 0 < r) (hη : 0 < η)
    (hd : (d : ℝ) ≤ r * Fintype.card ι)
    (hdist : ∀ U V : ρ → ι → F, IsInterleavedCodeword C U → IsInterleavedCodeword C V →
      U ≠ V → (agreeSet U V).card ≤ d)
    (hA : (√r + η) * Fintype.card ι ≤ A) (O : ρ → ι → F) :
    ((iList C A O).card : ℝ) ≤ 1 / (2 * η * √r) :=
  let h := iList_johnson_hyps C d A hd hdist hA O
  card_le_johnson _ (agreeSet O) hn hr0 hη h.1 h.2

/-- **Johnson bound for interleaved Reed-Solomon codes** (Annex B, `thm:johnson-interleaved`).
For the code of polynomials of degree at most `D ≥ 1` on `n > 0` points, with the reduced rate
`ρ₋ = D / n`, every interleaved word has at most `1 / (2 η √ρ₋)` interleaved codewords agreeing
with it on a common set of `A ≥ (√ρ₋ + η) n` coordinates. -/
theorem card_iList_rs_le_johnson (domain : ι ↪ F) {D A : ℕ} {η : ℝ} (hD : 0 < D)
    (hn : 0 < Fintype.card ι) (hη : 0 < η)
    (hA : (√((D : ℝ) / Fintype.card ι) + η) * Fintype.card ι ≤ A) (O : ρ → ι → F) :
    ((iList (ReedSolomon.code domain (D + 1)) A O).card : ℝ) ≤
      1 / (2 * η * √((D : ℝ) / Fintype.card ι)) := by
  have hnR : (0 : ℝ) < Fintype.card ι := by exact_mod_cast hn
  refine card_iList_le_johnson _ D A hn (by positivity) hη ?_ ?_ hA O
  · rw [div_mul_cancel₀ _ hnR.ne']
  · intro U V hU hV hne
    exact Nat.lt_succ_iff.mp (card_agreeSet_lt domain hU hV hne)

/-- **Johnson bound at ArkLib's Johnson threshold.** The list of an interleaved word of the
Reed-Solomon code of dimension `D + 1` on `n` points, at the threshold
`⌈johnsonAgreement n D η * n⌉₊` of `ReedSolomon.mcaError_affineLine_johnson_le` (radius
`1 - √ρ₋ - η`), has at most `1 / (2 η √ρ₋)` members. -/
theorem card_iList_johnsonAgreement_le {n : ℕ} (domain : Fin n ↪ F) {D : ℕ} {η : ℝ}
    (hD : 0 < D) (hn : 0 < n) (hη : 0 < η) (O : ρ → Fin n → F) :
    ((iList (ReedSolomon.code domain (D + 1)) ⌈johnsonAgreement n D η * n⌉₊ O).card : ℝ) ≤
      1 / (2 * η * √(johnsonRhoMinus n D)) := by
  have h := card_iList_rs_le_johnson (ρ := ρ) domain hD (by simpa using hn) hη
    (A := ⌈johnsonAgreement n D η * n⌉₊) (by
      simpa [johnsonAgreement, johnsonRhoMinus] using Nat.le_ceil (johnsonAgreement n D η * n))
    O
  simpa [johnsonRhoMinus] using h

/-- **Johnson bound as a natural number.** The list size is at most `⌊1 / (2 η √ρ₋)⌋₊`. -/
theorem card_iList_johnsonAgreement_le_floor {n : ℕ} (domain : Fin n ↪ F) {D : ℕ} {η : ℝ}
    (hD : 0 < D) (hn : 0 < n) (hη : 0 < η) (O : ρ → Fin n → F) :
    (iList (ReedSolomon.code domain (D + 1)) ⌈johnsonAgreement n D η * n⌉₊ O).card ≤
      ⌊1 / (2 * η * √(johnsonRhoMinus n D))⌋₊ :=
  Nat.le_floor (card_iList_johnsonAgreement_le domain hD hn hη O)

end List

end
end LeanVM.Protocol.Whir
