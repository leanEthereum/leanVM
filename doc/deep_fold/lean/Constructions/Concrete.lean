/-
The constructions put together, and at the deployed sizes in `GF(2^128)`.

`flats_break_mca`: on a subspace domain of size `n = 4k`, a pole pair whose first word is far from
every polynomial has at least `(n - 1) |K|` affine challenges at which its fold is within agreement
`n / 2 - 1` of a polynomial of degree below `k - 1`. The remaining statements instantiate the
hypotheses in `GaloisField 2 128` with `n = 2 ^ 26` (rate 1/4, `k = 2 ^ 24`) and `n = 2 ^ 25`
(rate 1/2, `k = 2 ^ 24`), so they are satisfiable at the sizes leanVM uses.
-/
import Constructions.Pole
import Constructions.GluedCount

open Polynomial Finset
open scoped Classical

namespace Constructions

variable {K : Type*} [Field K] [CharP K 2]

/-- A finite subspace contains subspaces of every smaller power-of-two size. -/
theorem exists_addSubgroup_card (D : AddSubgroup K) [Finite D] {m : ℕ}
    (hm : 2 ^ m ≤ Nat.card D) : ∃ V : AddSubgroup K, V ≤ D ∧ Nat.card V = 2 ^ m := by
  let _ : Algebra (ZMod 2) K := ZMod.algebra K 2
  obtain ⟨V', h1, h2, h3⟩ := ZModModule.exists_submodule_subset_card_le Nat.prime_two
    (AddSubgroup.toZModSubmodule 2 D) (k := 2 ^ m) hm (by positivity)
  refine ⟨V'.toAddSubgroup, h3, ?_⟩
  have hfin : Finite V'.toAddSubgroup :=
    Set.finite_coe_iff.mpr ((Set.toFinite (D : Set K)).subset h3)
  obtain ⟨j, hj⟩ := exists_card_eq_two_pow V'.toAddSubgroup
  have h1' : Nat.card V'.toAddSubgroup ≤ 2 ^ m := h1
  have h2' : 2 ^ m < 2 * Nat.card V'.toAddSubgroup := h2
  rw [hj] at h1' h2' ⊢
  rw [← pow_succ'] at h2'
  have a1 : j ≤ m := (Nat.pow_le_pow_iff_right (by norm_num)).mp h1'
  have a2 : m < j + 1 := (Nat.pow_lt_pow_iff_right (by norm_num)).mp h2'
  rw [show j = m by omega]

/-- **Flats break mutual correlated agreement at the Johnson radius (rate 1/4).** Let `D` be a
subspace domain of size `n = 2 ^ (s + 1)` in a finite field `K` of characteristic two, `k = n / 4`,
and `(k - 1) · C(n - 1, 2) + n < |K|`. There is a pole `β₀` outside `D` such that the pair
`f₀ = 1 / (x - β₀)`, `f₁ = x ^ (n / 2 - 1) / (x - β₀)` has:
`f₀` agrees with every polynomial of degree at most `k - 2` on at most `k - 1` points, and for at
least `(n - 1) |K|` challenges `(α, β)` the fold `f₁ + (α + β x) f₀` agrees with a polynomial of
degree at most `k - 2` on at least `n / 2 - 1` points. -/
theorem flats_break_mca [Fintype K] (D : AddSubgroup K) [Finite D] {s : ℕ} (hs : 2 ≤ s)
    (hD : Nat.card D = 2 ^ (s + 1))
    (hK : (2 ^ (s - 1) - 1) * (2 ^ (s + 1) - 1).choose 2 + 2 ^ (s + 1) < Fintype.card K) :
    ∃ β₀ : K, β₀ ∉ D ∧
      (∀ G : K[X], G.natDegree ≤ 2 ^ (s - 1) - 2 →
        (agree (pts D) (poleWord β₀) G).card ≤ 2 ^ (s - 1) - 1) ∧
      (2 ^ (s + 1) - 1) * Fintype.card K ≤
        (univ.filter (fun c : K × K => Close (pts D)
          (affFold (poleWord β₀) (poleNum (fun x => x ^ (2 ^ s - 1)) β₀) c)
          (2 ^ (s - 1) - 2) (2 ^ s - 1))).card := by
  have h2 : 2 ≤ 2 ^ (s - 1) := by
    calc 2 = 2 ^ 1 := (pow_one 2).symm
      _ ≤ 2 ^ (s - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hlist := flats_quarter D (by omega : 1 ≤ s) hD
  obtain ⟨t, htsub, htcard⟩ := Set.exists_subset_encard_eq hlist
  have htfin : t.Finite := Set.finite_of_encard_eq_coe htcard
  have hcard : htfin.toFinset.card = 2 ^ (s + 1) - 1 := by
    have := htfin.encard_eq_coe_toFinset_card
    rw [htcard, hD] at this
    exact_mod_cast this.symm
  have h𝒞 : ∀ Ci ∈ htfin.toFinset, Ci.natDegree ≤ 2 ^ (s - 1) - 2 + 1 ∧
      2 ^ s - 1 ≤ (agree (pts D) (fun x => x ^ (2 ^ s - 1)) Ci).card := by
    intro Ci hCi
    obtain ⟨hdeg, hagr⟩ := htsub (htfin.mem_toFinset.mp hCi)
    refine ⟨?_, hagr⟩
    by_cases h0 : Ci = 0
    · simp [h0]
    · have := (natDegree_lt_iff_degree_lt h0).mpr hdeg
      omega
  have hK' : (2 ^ (s - 1) - 2 + 1) * htfin.toFinset.card.choose 2 + (pts D).card <
      Fintype.card K := by
    rw [hcard, card_pts, hD, show 2 ^ (s - 1) - 2 + 1 = 2 ^ (s - 1) - 1 by omega]
    exact hK
  obtain ⟨β₀, hβ₀, hbad⟩ :=
    list_gives_bad_challenges (pts D) (fun x => x ^ (2 ^ s - 1)) htfin.toFinset h𝒞 hK'
  refine ⟨β₀, fun h => hβ₀ (mem_pts.mpr h), ?_, ?_⟩
  · intro G hG
    have := card_agree_poleWord_le hβ₀ hG
    omega
  · rwa [hcard] at hbad

/-! ### `GF(2^128)` -/

noncomputable local instance : Fintype (GaloisField 2 128) := Fintype.ofFinite _

theorem card_GF128 : Nat.card (GaloisField 2 128) = 2 ^ 128 := GaloisField.card 2 128 (by norm_num)

/-- `GF(2^128)` has subspaces of every size `2 ^ m`, `m ≤ 128`. -/
theorem exists_domain_GF128 {m : ℕ} (hm : m ≤ 128) :
    ∃ D : AddSubgroup (GaloisField 2 128), Nat.card D = 2 ^ m := by
  have htop : Nat.card (⊤ : AddSubgroup (GaloisField 2 128)) = 2 ^ 128 := by
    rw [AddSubgroup.card_top, card_GF128]
  obtain ⟨V, -, hV⟩ := exists_addSubgroup_card (⊤ : AddSubgroup (GaloisField 2 128)) (m := m)
    (by rw [htop]; exact Nat.pow_le_pow_right (by norm_num) hm)
  exact ⟨V, hV⟩

/-- Rate 1/4 at the deployed size: in `GF(2^128)` there is a subspace domain of `n = 2 ^ 26`
points on which the word `x ↦ x ^ (2 ^ 25 - 1)` has at least `2 ^ 26 - 1` polynomials of degree
below `2 ^ 24 = n / 4` at agreement `2 ^ 25 - 1 = n / 2 - 1`. This holds for every such domain. -/
theorem flats_quarter_GF128 :
    ∃ D : AddSubgroup (GaloisField 2 128), Nat.card D = 2 ^ 26 ∧
      ((2 ^ 26 - 1 : ℕ) : ℕ∞) ≤
        (RSList (pts D) (fun x => x ^ (2 ^ 25 - 1)) (2 ^ 24) (2 ^ 25 - 1)).encard := by
  obtain ⟨D, hD⟩ := exists_domain_GF128 (m := 26) (by norm_num)
  have : Finite D := Nat.finite_of_card_ne_zero (by rw [hD]; positivity)
  have h := flats_quarter D (s := 25) (by norm_num) hD
  rw [hD] at h
  exact ⟨D, hD, h⟩

/-- The pole pair at the deployed size: in `GF(2^128)`, on a subspace domain of `2 ^ 26` points,
a pair of words whose first word agrees with every polynomial of degree at most `2 ^ 24 - 2` on
fewer than `2 ^ 24` points, and whose affine fold is within agreement `2 ^ 25 - 1` of a polynomial
of degree at most `2 ^ 24 - 2` for at least `(2 ^ 26 - 1) · 2 ^ 128` of the `2 ^ 256` challenges. -/
theorem flats_break_mca_GF128 :
    ∃ (D : AddSubgroup (GaloisField 2 128)) (f₀ f₁ : GaloisField 2 128 → GaloisField 2 128),
      Nat.card D = 2 ^ 26 ∧
      (∀ G : (GaloisField 2 128)[X], G.natDegree ≤ 2 ^ 24 - 2 →
        (agree (pts D) f₀ G).card ≤ 2 ^ 24 - 1) ∧
      (2 ^ 26 - 1) * 2 ^ 128 ≤
        (univ.filter (fun c : GaloisField 2 128 × GaloisField 2 128 =>
          Close (pts D) (affFold f₀ f₁ c) (2 ^ 24 - 2) (2 ^ 25 - 1))).card := by
  obtain ⟨D, hD⟩ := exists_domain_GF128 (m := 26) (by norm_num)
  have : Finite D := Nat.finite_of_card_ne_zero (by rw [hD]; positivity)
  have hcardK : Fintype.card (GaloisField 2 128) = 2 ^ 128 := by
    rw [Fintype.card_eq_nat_card, card_GF128]
  obtain ⟨β₀, -, h1, h2⟩ := flats_break_mca D (s := 25) (by norm_num) hD (by
    rw [hcardK, Nat.choose_two_right]
    norm_num)
  rw [hcardK] at h2
  exact ⟨D, poleWord β₀, poleNum (fun x => x ^ (2 ^ 25 - 1)) β₀, hD, h1, h2⟩

/-- Rate 1/2 at the deployed size: in `GF(2^128)` there are a subspace domain of `n = 2 ^ 25`
points and a word with at least `2 ^ 25 - 2` polynomials of degree at most `2 ^ 24 = n / 2` at
agreement `5 · 2 ^ 22 = 5n/8`. -/
theorem five_eighths_slack_GF128 :
    ∃ (D : AddSubgroup (GaloisField 2 128)) (w : GaloisField 2 128 → GaloisField 2 128),
      Nat.card D = 2 ^ 25 ∧
      ((2 ^ 25 - 2 : ℕ) : ℕ∞) ≤ (RSList (pts D) w (2 ^ 24 + 1) (5 * 2 ^ 22)).encard := by
  obtain ⟨D, hD⟩ := exists_domain_GF128 (m := 25) (by norm_num)
  have : Finite D := Nat.finite_of_card_ne_zero (by rw [hD]; positivity)
  obtain ⟨H, hHD, hH⟩ := exists_addSubgroup_card D (m := 24) (by rw [hD]; norm_num)
  have : Finite H := Nat.finite_of_card_ne_zero (by rw [hH]; positivity)
  obtain ⟨P, hPH, hPc⟩ := Finset.exists_subset_card_eq (s := pts H) (n := 3 * 2 ^ 22)
    (by rw [card_pts, hH]; norm_num)
  have h := five_eighths_slack D H hHD (by rw [hH, hD]; norm_num) (m := 2 ^ 22)
    (by rw [hD]; norm_num) P (fun x hx => mem_pts.mp (hPH hx)) hPc
  rw [hD] at h
  exact ⟨D, padWord P (2 * 2 ^ 22), hD, by simpa using h⟩

/-- Rate 1/2, genuine codewords, at the deployed size: at least `2 ^ 25 - 2` polynomials of
degree below `2 ^ 24 = n / 2` at agreement `5n/8 - 1`. -/
theorem five_eighths_genuine_GF128 :
    ∃ (D : AddSubgroup (GaloisField 2 128)) (w : GaloisField 2 128 → GaloisField 2 128),
      Nat.card D = 2 ^ 25 ∧
      ((2 ^ 25 - 2 : ℕ) : ℕ∞) ≤ (RSList (pts D) w (2 ^ 24) (5 * 2 ^ 22 - 1)).encard := by
  obtain ⟨D, hD⟩ := exists_domain_GF128 (m := 25) (by norm_num)
  have : Finite D := Nat.finite_of_card_ne_zero (by rw [hD]; positivity)
  obtain ⟨H, hHD, hH⟩ := exists_addSubgroup_card D (m := 24) (by rw [hD]; norm_num)
  have : Finite H := Nat.finite_of_card_ne_zero (by rw [hH]; positivity)
  obtain ⟨P, hPH, hPc⟩ := Finset.exists_subset_card_eq (s := pts H) (n := 3 * 2 ^ 22 - 1)
    (by rw [card_pts, hH]; norm_num)
  have h := five_eighths_genuine D H hHD (by rw [hH, hD]; norm_num) (m := 2 ^ 22)
    (by norm_num) (by rw [hD]; norm_num) P (fun x hx => mem_pts.mp (hPH hx)) hPc
  rw [hD] at h
  exact ⟨D, padWord P (2 * 2 ^ 22), hD, by simpa using h⟩

/-- The word `L_U ^ 5` at the deployed size: in `GF(2^128)`, a subspace domain of `n = 2 ^ 25`
points and a subspace `U` of `2 ^ 22 = n / 8` points such that `L_U ^ 5` has at least `2 ^ 22 - 1`
polynomials of degree at most `2 ^ 24 = n / 2` at agreement `5 · 2 ^ 22 = 5n/8`. -/
theorem glued_list_card_GF128 :
    ∃ D U : AddSubgroup (GaloisField 2 128), U ≤ D ∧ Nat.card D = 2 ^ 25 ∧ Nat.card U = 2 ^ 22 ∧
      ((2 ^ 22 - 1 : ℕ) : ℕ∞) ≤
        (RSList (pts D) (fun x => (subPoly U).eval x ^ 5) (2 ^ 24 + 1) (5 * 2 ^ 22)).encard := by
  obtain ⟨D, hD⟩ := exists_domain_GF128 (m := 25) (by norm_num)
  have : Finite D := Nat.finite_of_card_ne_zero (by rw [hD]; positivity)
  obtain ⟨U, hUD, hU⟩ := exists_addSubgroup_card D (m := 22) (by rw [hD]; norm_num)
  have h := glued_list_card D U hUD (by rw [hD, hU]; norm_num)
  rw [hU] at h
  exact ⟨D, U, hUD, hD, hU, by simpa using h⟩

end Constructions
