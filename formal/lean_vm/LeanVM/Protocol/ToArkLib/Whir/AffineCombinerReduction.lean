/-
  LeanVM.Protocol.ToArkLib.Whir.AffineCombinerReduction

  [CYWZ26, preprint], Lemma 4.7 from Lemma 4.3: the non-persistent count of the interpolant from
  a factorization of it with bounded excluded pairs. Candidate for ArkLib.
-/

module

public import LeanVM.Protocol.ToArkLib.Whir.AffineCombinerFactorCount
public import LeanVM.Protocol.ToArkLib.Whir.AffineCombinerMca

/-!
# The non-persistent count from a factorization

[CYWZ26, preprint], proof of Lemma 4.7, with Lemma 4.3 as its input. A
`ExcludedFactorization Q p D M` records what the preprint's Lemma 4.3 and (4.6) extract from the
interpolant `Q ∈ L[X, Y, Z]`, `L` of characteristic `p`:

* a polynomial `C(X, Y)` (`cpoly`, the product of the factors without `Z`) and Frobenius-reduced
  factors `R_i` with exponents `e_i = p^κ_i` and `(Y, Z)`-degrees `h_i ≥ 1` (`R_i` is the
  preprint's `R_i`, with `Q_i(X^e, Y^e, Z) = R_i^e`);
* `deg_Y C + Σ h_i ≤ D` and `e_i ≤ M` ((4.6));
* every root `P` of `Q(X, α + β X, Z)` has `C(X, α + β X) = 0` or is a root `P(X^e_i)` of some
  `R_i(X, α' + β' X, Z)`, `α'^e_i = α`, `β'^e_i = β` ((4.7));
* at most `deg_Y C` pairs of `F²` have `C(X, α + β X) = 0`, and for each `i` at most
  `h_i (h_i - 1)` pairs have a root `P(X^e_i)` of `R_i` along the line at which `∂_Z R_i` also
  vanishes (the two halves of `|E| ≤ D²`, Lemma 4.3).

`card_nonpersSet_le_of_factorization`: such a factorization of an interpolant that vanishes on
every exceptional triple bounds the non-persistent pairs by `D² + 4 d² M² D³ (n / (A - B))²`:
each such pair lies on `C`, in an excluded set, or in `factorPairs` of some `R_i`
(`card_factorPairs_le`, Claims 4.8 and 4.9), and
`deg_Y C + Σ h_i (h_i - 1) ≤ D²`, `Σ e_i² h_i³ ≤ M² D³`.

`interpolantCount_of_factorization`: if every interpolant admits such a factorization (Lemma 4.3),
`InterpolantCount` holds.
-/

namespace LeanVM.Protocol.Whir.AffineCombiner

open Finset Polynomial

@[expose] public section

variable {F L : Type*} [Field F] [Fintype F] [Field L] [Algebra F L]

open Classical in
/-- **A factorization of the interpolant with bounded excluded pairs** ([CYWZ26, Lemma 4.3 and
(4.6), (4.7)]), over a field `L` of characteristic `p`, with the challenges in `F`. -/
structure ExcludedFactorization (Q : MvPolynomial (Fin 3) L) (p D M : ℕ) where
  /-- The number of factors with positive `Z`-degree. -/
  r : ℕ
  /-- The Frobenius-reduced factors. -/
  R : Fin r → MvPolynomial (Fin 3) L
  /-- Their Frobenius exponents `e_i = p^κ_i`. -/
  κ : Fin r → ℕ
  /-- Their `(Y, Z)`-degrees. -/
  h : Fin r → ℕ
  /-- The factor without `Z`, in `X` and `Y`. -/
  cpoly : MvPolynomial (Fin 2) L
  /-- Its `Y`-degree bound. -/
  cY : ℕ
  deg_R : ∀ i, ∀ m ∈ (R i).support, m 1 + m 2 ≤ h i
  one_le_h : ∀ i, 1 ≤ h i
  e_le : ∀ i, p ^ κ i ≤ M
  deg_sum : cY + ∑ i, h i ≤ D
  cover : ∀ (α β : L) (P : L[X]), MvPolynomial.aeval ![X, C α + C β * X, P] Q = 0 →
    MvPolynomial.aeval ![X, C α + C β * X] cpoly = 0 ∨
      ∃ i, ∃ α' β' : L, α' ^ p ^ κ i = α ∧ β' ^ p ^ κ i = β ∧
        MvPolynomial.aeval ![X, C α' + C β' * X, P.comp (X ^ p ^ κ i)] (R i) = 0
  card_line : (univ.filter fun ab : F × F ↦ MvPolynomial.aeval
    ![X, C (algebraMap F L ab.1) + C (algebraMap F L ab.2) * X] cpoly = 0).card ≤ cY
  card_excluded : ∀ i, (univ.filter fun ab : F × F ↦ ∃ (P : L[X]) (α' β' : L),
    α' ^ p ^ κ i = algebraMap F L ab.1 ∧ β' ^ p ^ κ i = algebraMap F L ab.2 ∧
    MvPolynomial.aeval ![X, C α' + C β' * X, P.comp (X ^ p ^ κ i)] (R i) = 0 ∧
    MvPolynomial.aeval ![X, C α' + C β' * X, P.comp (X ^ p ^ κ i)]
      (MvPolynomial.pderiv 2 (R i)) = 0).card ≤ h i * (h i - 1)

theorem sum_cube_le_cube_sum {ι : Type*} (s : Finset ι) (a : ι → ℕ) :
    ∑ i ∈ s, a i ^ 3 ≤ (∑ i ∈ s, a i) ^ 3 := by
  calc ∑ i ∈ s, a i ^ 3 ≤ ∑ i ∈ s, a i * (∑ j ∈ s, a j) ^ 2 := by
        refine sum_le_sum fun i hi ↦ ?_
        rw [pow_succ']
        exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (single_le_sum (fun _ _ ↦ Nat.zero_le _)
          hi) 2)
    _ = (∑ i ∈ s, a i) ^ 3 := by rw [← sum_mul]; ring

theorem sum_sq_le_sq_sum {ι : Type*} (s : Finset ι) (a : ι → ℕ) :
    ∑ i ∈ s, a i ^ 2 ≤ (∑ i ∈ s, a i) ^ 2 := by
  calc ∑ i ∈ s, a i ^ 2 ≤ ∑ i ∈ s, a i * (∑ j ∈ s, a j) := by
        refine sum_le_sum fun i hi ↦ ?_
        rw [sq]
        exact Nat.mul_le_mul_left _ (single_le_sum (fun _ _ ↦ Nat.zero_le _) hi)
    _ = (∑ i ∈ s, a i) ^ 2 := by rw [← sum_mul]; ring

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **Lemma 4.7 from Lemma 4.3**: an interpolant vanishing on every exceptional triple, with an
excluded factorization, leaves at most `D² + 4 d² M² D³ (n / (A - B))²` non-persistent pairs. -/
theorem card_nonpersSet_le_of_factorization {p : ℕ} [Fact p.Prime] [CharP L p] (dom : ι ↪ F)
    (f g : ι → L) {d A m D B : ℕ} (hd : 1 ≤ d) (hdB : d + 1 < B) (hBA : B < A)
    (hAn : A ≤ Fintype.card ι) (Q : MvPolynomial (Fin 3) L)
    (hvan : ∀ α β P, IsExcTriple dom f g d A α β P →
      MvPolynomial.aeval ![X, linL α β, P] Q = 0)
    (fac : ExcludedFactorization (F := F) Q p D (bigM d A m D)) :
    ((nonpersSet dom f g d A B).card : ℚ) ≤ nAffRest (Fintype.card ι) d A m D B := by
  classical
  set n := Fintype.card ι
  set M := bigM d A m D
  set Cs := univ.filter fun ab : F × F ↦ MvPolynomial.aeval
    ![X, C (algebraMap F L ab.1) + C (algebraMap F L ab.2) * X] fac.cpoly = 0
  set Es : Fin fac.r → Finset (F × F) := fun i ↦ univ.filter fun ab : F × F ↦
    ∃ (P : L[X]) (α' β' : L), α' ^ p ^ fac.κ i = algebraMap F L ab.1 ∧
      β' ^ p ^ fac.κ i = algebraMap F L ab.2 ∧
      MvPolynomial.aeval ![X, C α' + C β' * X, P.comp (X ^ p ^ fac.κ i)] (fac.R i) = 0 ∧
      MvPolynomial.aeval ![X, C α' + C β' * X, P.comp (X ^ p ^ fac.κ i)]
        (MvPolynomial.pderiv 2 (fac.R i)) = 0
  set Fs : Fin fac.r → Finset (F × F) := fun i ↦
    factorPairs dom f g (fac.R i) (p ^ fac.κ i) d A B
  have hsub : nonpersSet dom f g d A B ⊆
      Cs ∪ (univ.biUnion Es ∪ univ.biUnion Fs) := by
    intro ab hab
    obtain ⟨P, hexc, hnp⟩ := (mem_filter.mp hab).2
    have hQ := hvan ab.1 ab.2 P hexc
    rcases fac.cover _ _ P (by simpa [linL] using hQ) with hC | ⟨i, α', β', hα, hβ, hR⟩
    · exact mem_union_left _ (mem_filter.mpr ⟨mem_univ _, hC⟩)
    · refine mem_union_right _ ?_
      by_cases hZ : MvPolynomial.aeval ![X, C α' + C β' * X, P.comp (X ^ p ^ fac.κ i)]
          (MvPolynomial.pderiv 2 (fac.R i)) = 0
      · exact mem_union_left _ (mem_biUnion.mpr ⟨i, mem_univ _,
          mem_filter.mpr ⟨mem_univ _, P, α', β', hα, hβ, hR, hZ⟩⟩)
      · exact mem_union_right _ (mem_biUnion.mpr ⟨i, mem_univ _,
          mem_filter.mpr ⟨mem_univ _, P, α', β', hexc.1, hexc.2.1, hnp, hα, hβ, hR, hZ⟩⟩)
  -- Each factor's count.
  have hF : ∀ i, ((Fs i).card : ℚ) ≤
      4 * d ^ 2 * (p ^ fac.κ i : ℕ) ^ 2 * fac.h i ^ 3 * ((n : ℚ) / ((A - B : ℕ) : ℚ)) ^ 2 := by
    intro i
    have := card_factorPairs_le dom f g (fac.R i) (p ^ fac.κ i) d (fac.h i) (κ := fac.κ i) rfl
      (fac.deg_R i) hd (fac.one_le_h i) hdB hBA hAn
    refine this.trans (le_of_eq ?_)
    push_cast
    ring
  -- Totals.
  have hcard : ((nonpersSet dom f g d A B).card : ℚ) ≤
      (fac.cY + ∑ i, fac.h i * (fac.h i - 1) : ℕ) +
        ∑ i, 4 * d ^ 2 * (p ^ fac.κ i : ℕ) ^ 2 * fac.h i ^ 3 *
          ((n : ℚ) / ((A - B : ℕ) : ℚ)) ^ 2 := by
    have h1 := card_le_card hsub
    have h2 := card_union_le Cs (univ.biUnion Es ∪ univ.biUnion Fs)
    have h3 := card_union_le (univ.biUnion Es) (univ.biUnion Fs)
    have h4 : (univ.biUnion Es).card ≤ ∑ i, fac.h i * (fac.h i - 1) :=
      card_biUnion_le.trans (sum_le_sum fun i _ ↦ fac.card_excluded i)
    have h5 : ((univ.biUnion Fs).card : ℚ) ≤ ∑ i, ((Fs i).card : ℚ) := by
      exact_mod_cast card_biUnion_le
    have h6 : ((nonpersSet dom f g d A B).card : ℚ) ≤
        (Cs.card + (univ.biUnion Es).card : ℕ) + ((univ.biUnion Fs).card : ℚ) := by
      exact_mod_cast (h1.trans (h2.trans (by omega)))
    have h7 : (Cs.card + (univ.biUnion Es).card : ℕ) ≤ fac.cY + ∑ i, fac.h i * (fac.h i - 1) :=
      add_le_add fac.card_line h4
    calc _ ≤ _ := h6
      _ ≤ _ := add_le_add (by exact_mod_cast h7) (h5.trans (sum_le_sum fun i _ ↦ hF i))
  refine hcard.trans ?_
  unfold nAffRest
  -- `deg_Y C + Σ h_i (h_i - 1) ≤ D²`.
  have hE : (fac.cY + ∑ i, fac.h i * (fac.h i - 1) : ℕ) ≤ D ^ 2 := by
    have hsq := sum_sq_le_sq_sum univ fac.h
    have hle : ∑ i, fac.h i * (fac.h i - 1) ≤ ∑ i, fac.h i ^ 2 :=
      sum_le_sum fun i _ ↦ by rw [sq]; exact Nat.mul_le_mul_left _ (Nat.sub_le _ _)
    have hcY : fac.cY ≤ fac.cY ^ 2 := by rw [sq]; exact Nat.le_mul_self _
    calc fac.cY + ∑ i, fac.h i * (fac.h i - 1) ≤ fac.cY ^ 2 + (∑ i, fac.h i) ^ 2 :=
          add_le_add hcY (hle.trans hsq)
      _ ≤ (fac.cY + ∑ i, fac.h i) ^ 2 := by rw [add_sq]; omega
      _ ≤ D ^ 2 := Nat.pow_le_pow_left fac.deg_sum 2
  -- `Σ e_i² h_i³ ≤ M² D³`.
  have hN : (∑ i, (p ^ fac.κ i : ℕ) ^ 2 * fac.h i ^ 3 : ℕ) ≤ M ^ 2 * D ^ 3 := by
    calc ∑ i, (p ^ fac.κ i) ^ 2 * fac.h i ^ 3 ≤ ∑ i, M ^ 2 * fac.h i ^ 3 :=
          sum_le_sum fun i _ ↦ Nat.mul_le_mul_right _ (Nat.pow_le_pow_left (fac.e_le i) 2)
      _ = M ^ 2 * ∑ i, fac.h i ^ 3 := by rw [mul_sum]
      _ ≤ M ^ 2 * (∑ i, fac.h i) ^ 3 := Nat.mul_le_mul_left _ (sum_cube_le_cube_sum _ _)
      _ ≤ M ^ 2 * D ^ 3 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left
          (le_trans (Nat.le_add_left _ _) fac.deg_sum) 3)
  have hEq : (((fac.cY + ∑ i, fac.h i * (fac.h i - 1) : ℕ)) : ℚ) ≤ (D : ℚ) ^ 2 := by
    exact_mod_cast hE
  have hNq : ((∑ i, (p ^ fac.κ i : ℕ) ^ 2 * fac.h i ^ 3 : ℕ) : ℚ) ≤
      (M : ℚ) ^ 2 * (D : ℚ) ^ 3 := by exact_mod_cast hN
  have hv : (0 : ℚ) ≤ ((n : ℚ) / ((A - B : ℕ) : ℚ)) ^ 2 := by positivity
  have hsumq : ∑ i, 4 * (d : ℚ) ^ 2 * ((p ^ fac.κ i : ℕ) : ℚ) ^ 2 * (fac.h i : ℚ) ^ 3 *
      ((n : ℚ) / ((A - B : ℕ) : ℚ)) ^ 2 = 4 * (d : ℚ) ^ 2 *
        ((∑ i, (p ^ fac.κ i : ℕ) ^ 2 * fac.h i ^ 3 : ℕ) : ℚ) * ((n : ℚ) / ((A - B : ℕ) : ℚ)) ^ 2 := by
    push_cast
    rw [mul_sum, sum_mul]
    refine sum_congr rfl fun i _ ↦ ?_
    ring
  rw [hsumq]
  have : 4 * (d : ℚ) ^ 2 * ((∑ i, (p ^ fac.κ i : ℕ) ^ 2 * fac.h i ^ 3 : ℕ) : ℚ) *
      ((n : ℚ) / ((A - B : ℕ) : ℚ)) ^ 2 ≤
      4 * (d : ℚ) ^ 2 * ((M : ℚ) ^ 2 * (D : ℚ) ^ 3) * ((n : ℚ) / ((A - B : ℕ) : ℚ)) ^ 2 := by
    gcongr
  linarith

/-- **The non-persistent count from Lemma 4.3**: if every nonzero interpolant over `L` (degree
bounds `deg_{Y,Z} ≤ D`, `deg_Z ≤ M`) has an excluded factorization, then `InterpolantCount`
holds at admissible parameters. -/
theorem interpolantCount_of_factorization {p : ℕ} [Fact p.Prime] [CharP L p] (dom : ι ↪ F)
    {d A m D B : ℕ} (hadm : Admissible (Fintype.card ι) d A m D B)
    (hfac : ∀ Q : MvPolynomial (Fin 3) L, Q ≠ 0 →
      (∀ s ∈ Q.support, s 1 + s 2 ≤ D ∧ s 2 ≤ bigM d A m D) →
      Nonempty (ExcludedFactorization (F := F) Q p D (bigM d A m D))) :
    InterpolantCount L dom d A m D B := by
  intro f g Q hQ hsupp hvan
  obtain ⟨fac⟩ := hfac Q hQ hsupp
  obtain ⟨hd, hAn, -, -, -, hdB, hBA, -⟩ := hadm
  exact card_nonpersSet_le_of_factorization dom f g hd hdB hBA hAn Q hvan fac

/-- **Lemma 4.3 for the interpolants over the algebraic closure** ([CYWZ26, Lemma 4.3] with (4.6)
and (4.7)): every nonzero `Q ∈ F̄[X, Y, Z]` with `deg_{Y,Z} Q ≤ D` and `deg_Z Q ≤ M` has an
excluded factorization. This is the one statement the affine MCA count below still assumes. -/
def Lemma43 (F : Type*) [Field F] [Fintype F] (p D M : ℕ) : Prop :=
  ∀ Q : MvPolynomial (Fin 3) (AlgebraicClosure F), Q ≠ 0 →
    (∀ s ∈ Q.support, s 1 + s 2 ≤ D ∧ s 2 ≤ M) →
    Nonempty (ExcludedFactorization (F := F) Q p D M)

/-- **Affine MCA, counting form, from Lemma 4.3** (Annex B, `thm:mca-affine`): at admissible
`(m, D, B)`, every pair of interleaved words has at most `nAff q n d A m D B = q² ε_aff`
exceptional pairs. -/
theorem card_excSet_le_nAff_of_lemma43 {p : ℕ} [Fact p.Prime] [CharP F p] {ρ : Type*}
    [Fintype ρ] (dom : ι ↪ F) {d A m D B : ℕ} (hadm : Admissible (Fintype.card ι) d A m D B)
    (h43 : Lemma43 F p D (bigM d A m D)) (f g : ρ → ι → F) :
    ((excSet dom f g d A).card : ℚ) ≤ nAff (Fintype.card F) (Fintype.card ι) d A m D B := by
  have : CharP (AlgebraicClosure F) p :=
    charP_of_injective_algebraMap (algebraMap F (AlgebraicClosure F)).injective p
  exact card_excSet_le_nAff dom hadm (interpolantCount_of_factorization dom hadm h43) f g

/-- **One affine fold round from Lemma 4.3** (Annex B, `lem:fold-list`, counting form): the
escapes `(α, β)` number at most `nAff + 2 jl n (A - 1) d q`, the Annex's `ε_aff + 2L/|E|` times
`q²`. -/
theorem card_foldBad_le_nAff_of_lemma43 [DecidableEq F] {p : ℕ} [Fact p.Prime] [CharP F p]
    {ρ : Type*} [Fintype ρ] (dom : ι ↪ F) (f g : ρ → ι → F) {d A m D B : ℕ}
    (hgap : Fintype.card ι * d < (A - 1) * (A - 1))
    (hadm : Admissible (Fintype.card ι) d A m D B) (h43 : Lemma43 F p D (bigM d A m D))
    (Λ₀ Λ₁ : (ρ → F[X]) →ₗ[F] F) (c : F)
    (hviol : ∀ q ∈ pairList dom f g (A - 1) d, Λ₀ q.1 + Λ₁ q.2 ≠ c) (u₀ v₀ c₀ v₁ c₁ : F) :
    ((foldBad dom f g A d Λ₀ Λ₁ c u₀ v₀ c₀ v₁ c₁).card : ℚ) ≤
      nAff (Fintype.card F) (Fintype.card ι) d A m D B +
        2 * jl (Fintype.card ι) (A - 1) d * (Fintype.card F : ℚ) := by
  have : CharP (AlgebraicClosure F) p :=
    charP_of_injective_algebraMap (algebraMap F (AlgebraicClosure F)).injective p
  exact card_foldBad_le_nAff dom f g hgap hadm (interpolantCount_of_factorization dom hadm h43)
    Λ₀ Λ₁ c hviol u₀ v₀ c₀ v₁ c₁

end

end LeanVM.Protocol.Whir.AffineCombiner
