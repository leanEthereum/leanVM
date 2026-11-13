/-
  LeanVM.Protocol.ToArkLib.Whir.AffineCombinerFactor

  The non-persistent pairs whose candidate is a simple root of one factor `R` of the
  interpolant: at most `4 d² e² h³ (n / (A - B))²` of them ([CWYZ26], Claims 4.8 and
  4.9). Candidate for ArkLib.
-/

module

public import LeanVM.Protocol.ToArkLib.Whir.AffineCombinerChart
public import LeanVM.Protocol.ToArkLib.Whir.AffineCombinerCore
public import ArkLib.ToMathlib.RingTheory.Nullstellensatz.AgreementIncidence
public import ArkLib.ToMathlib.RingTheory.Nullstellensatz.PrincipalOpen
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.Algebra.Polynomial.Taylor
public import Mathlib.Algebra.Polynomial.Expand
public import Mathlib.RingTheory.MvPolynomial.Tower

/-!
# One factor of the interpolant

[CWYZ26], Claims 4.8 and 4.9, for one factor `R ∈ L[X, Y, Z]` whose monomials
`X^i Y^t Z^j` have `t + j ≤ h`, and a Frobenius power `e = p^κ` (`p` the characteristic of `L`).
A pair `(α, β) ∈ F²` is counted (`factorPairs`) when some `P` of degree at most `d` agrees with
`f + (α + β x) g` on at least `A` points, is not persistent, and is a simple root of `R` along
the line: `R(X, α' + β' X, P(X^e)) = 0 ≠ ∂_Z R(X, α' + β' X, P(X^e))` for `e`-th roots `α'`, `β'`
of `α`, `β` in `L` ([CWYZ26], (4.7)).

`card_factorPairs_le`: at most `h (2 e d h n / (A - B))² = 4 d² e² h³ (n / (A - B))²` such pairs,
if `d + 1 < B < A ≤ n`.

The proof is the paper's, in the coordinates `(Y, V, Z)` of its Claim 4.9, over
`k = AlgebraicClosure L(T₀)`:

* A counted triple gives the point `y = (α' + β' T₀, β', P(T₀^e))` of the surface
  `R(T₀, Y, Z) = 0` (`chartA R 0 0`), off the separant `S = ∂_Z R(T₀, Y, Z)` (`chartA R 0 1`).
* Hensel's numerators `N_n` (`AffineCombinerHensel`) give the Taylor coefficients of `P` at
  `T₀^e`: `N_{e j}(y) = S(y)^(2 e j - 1) τ_j` (`hatP_eq`), because
  `P((T₀ + W)^e) = P(T₀^e + W^e)` in characteristic `p`.
* The agreement cut at `x` (`chartCut`, degree at most `2 e d h`) vanishes at `y` exactly when
  `P` agrees at `x`; at any point `z` off `S` it vanishes exactly when the polynomial `P̂_z`
  read off the chart agrees with `f + (a + b x) g` for `a = (z₀ - z₁ T₀)^e`, `b = z₁^e`
  (`aeval_chartCut`).
* A positive-dimensional component containing more than `B` cuts has a second point, so the
  linear system of its `B + 1` agreement equations has a nonzero solution over `k`, hence over `L`
  (`exists_ne_zero_mulVec_of_map`), which makes every counted triple on it persistent
  (`persistent_of_two_points`).
* ArkLib's `MvPolynomial.card_le_of_agreement_off_excluded_of_hypersurface` (the induction of
  Claim 4.8 with Bézout for the cuts) bounds the remaining points by
  `deg(surface) · (n · deg(cut) / (A - B))²`.
-/

namespace LeanVM.Protocol.Whir.AffineCombiner

open Finset Polynomial Polynomial.UniversalHenselNumerator

@[expose] public section

/-! ## Linear algebra over an extension -/

/-- A linear system over `L` with a nonzero solution over an extension has one over `L`. -/
theorem exists_ne_zero_mulVec_of_map {L k : Type*} [Field L] [Field k] [Algebra L k]
    {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n] [DecidableEq m] (M : Matrix m n L)
    (v : n → k) (hv : v ≠ 0) (hMv : (M.map (algebraMap L k)).mulVec v = 0) :
    ∃ w : n → L, w ≠ 0 ∧ M.mulVec w = 0 := by
  by_contra hno
  push Not at hno
  have hker : LinearMap.ker (Matrix.mulVecLin M) = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro w hw
    by_contra hne
    exact hno w hne hw
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective _ hker
  set N := LinearMap.toMatrix' g
  have hNM : N * M = 1 := by
    have h1 := congrArg LinearMap.toMatrix' hg
    rw [LinearMap.toMatrix'_comp, LinearMap.toMatrix'_id,
      show LinearMap.toMatrix' (Matrix.mulVecLin M) = M from LinearMap.toMatrix'_toLin' M] at h1
    exact h1
  apply hv
  have := congrArg (fun A ↦ (A.map (algebraMap L k)).mulVec v) hNM
  simp only [Matrix.map_mul, ← Matrix.mulVec_mulVec, hMv, Matrix.mulVec_zero] at this
  rw [Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mulVec] at this
  exact this.symm


/-! ## The agreement cuts -/

section Cut

variable {F L : Type*} [Field F] [Field L] [Algebra F L] {ι : Type*}
  (dom : ι ↪ F) (f g : ι → L) (R : MvPolynomial (Fin 3) L) (e d h : ℕ)

/-- Hensel's numerators of the chart, with outer-degree cap `h`. -/
noncomputable def chartN (n : ℕ) : ChartRing L :=
  numerators (chartRs R) (chartA R 0 1) h n

/-- **The agreement cut at `x`**: `S^(2ed-1)` times `P̂(x) - f(x) - ((Y - V T₀)^e + V^e x) g(x)`,
with `P̂ = Z + Σ_{1 ≤ j ≤ d} (N_{ej} / S^(2ej-1)) (X - T₀^e)^j`. -/
noncomputable def chartCut (x : ι) : ChartRing L :=
  chartA R 0 1 ^ (2 * e * d - 1) * MvPolynomial.X 2 +
    ∑ j ∈ Icc 1 d, chartN R h (e * j) * chartA R 0 1 ^ (2 * e * (d - j)) *
      MvPolynomial.C (algebraMap L (RatFunc L) (pt dom x) - RatFunc.X ^ e) ^ j -
    chartA R 0 1 ^ (2 * e * d - 1) * (MvPolynomial.C (algebraMap L (RatFunc L) (f x)) +
      ((MvPolynomial.X 0 - MvPolynomial.X 1 * MvPolynomial.C RatFunc.X) ^ e +
        MvPolynomial.X 1 ^ e * MvPolynomial.C (algebraMap L (RatFunc L) (pt dom x))) *
      MvPolynomial.C (algebraMap L (RatFunc L) (g x)))

/-- **Degree of the cuts**: at most `2 e d h`. -/
theorem totalDegree_chartCut_le {R : MvPolynomial (Fin 3) L} {h : ℕ}
    (hR : ∀ m ∈ R.support, m 1 + m 2 ≤ h) (hd : 1 ≤ d) (he : 1 ≤ e) (hh : 1 ≤ h) (x : ι) :
    (chartCut dom f g R e d h x).totalDegree ≤ 2 * e * d * h := by
  have hs : (chartA R 0 1).totalDegree ≤ h - 1 := by
    have := chartA_totalDegree_le R hR 0 1 hh; omega
  set s := chartA R 0 1
  have hN : ∀ n, 1 ≤ n → (chartN R h n).totalDegree ≤ 1 + (2 * n - 1) * (h - 1) :=
    totalDegree_numerators_le (chartRs R) s le_rfl
      (fun a b hb ↦ chartA_totalDegree_le R hR a b hb) hs
  set M := 2 * e * d - 1
  have hspow (k : ℕ) : (s ^ k).totalDegree ≤ k * (h - 1) :=
    (MvPolynomial.totalDegree_pow _ _).trans (Nat.mul_le_mul_left _ hs)
  have hE : 2 ≤ 2 * e * d := by nlinarith
  -- Every term has degree at most `M (h - 1) + e`.
  have hbound : M * (h - 1) + e ≤ 2 * e * d * h := by
    have h1 : M * (h - 1) ≤ 2 * e * d * (h - 1) := Nat.mul_le_mul_right _ (Nat.sub_le _ _)
    have h2 : 2 * e * d * (h - 1) + 2 * e * d = 2 * e * d * h := by
      rw [← Nat.mul_succ]; congr 1; omega
    have h3 : e ≤ 2 * e * d := by nlinarith
    omega
  have hT1 : (s ^ M * MvPolynomial.X 2 : ChartRing L).totalDegree ≤ M * (h - 1) + e :=
    (MvPolynomial.totalDegree_mul _ _).trans (add_le_add (hspow M)
      ((MvPolynomial.totalDegree_X _).le.trans he))
  have hT2 : (∑ j ∈ Icc 1 d, chartN R h (e * j) * s ^ (2 * e * (d - j)) *
      MvPolynomial.C (algebraMap L (RatFunc L) (pt dom x) - RatFunc.X ^ e) ^ j :
        ChartRing L).totalDegree ≤ M * (h - 1) + e := by
    refine (MvPolynomial.totalDegree_finsetSum _ _).trans (Finset.sup_le fun j hj ↦ ?_)
    obtain ⟨hj1, hjd⟩ := mem_Icc.mp hj
    have hej : 1 ≤ e * j := Nat.mul_pos he hj1
    refine (MvPolynomial.totalDegree_mul _ _).trans ?_
    rw [← MvPolynomial.C_pow, MvPolynomial.totalDegree_C, add_zero]
    refine (MvPolynomial.totalDegree_mul _ _).trans ?_
    have hsplit : (2 * (e * j) - 1) + 2 * e * (d - j) = M := by
      have h2 : 1 ≤ e * j := Nat.mul_pos he hj1
      simp only [M]
      zify [hjd, (by omega : 1 ≤ 2 * (e * j)), (by nlinarith : 1 ≤ 2 * e * d)]
      ring
    calc _ ≤ 1 + (2 * (e * j) - 1) * (h - 1) + 2 * e * (d - j) * (h - 1) :=
          add_le_add (hN _ hej) (hspow _)
      _ = 1 + M * (h - 1) := by rw [← hsplit, add_mul]; ring
      _ ≤ M * (h - 1) + e := by omega
  have hT3 : (s ^ M * (MvPolynomial.C (algebraMap L (RatFunc L) (f x)) +
      ((MvPolynomial.X 0 - MvPolynomial.X 1 * MvPolynomial.C RatFunc.X) ^ e +
        MvPolynomial.X 1 ^ e * MvPolynomial.C (algebraMap L (RatFunc L) (pt dom x))) *
      MvPolynomial.C (algebraMap L (RatFunc L) (g x))) : ChartRing L).totalDegree ≤
        M * (h - 1) + e := by
    refine (MvPolynomial.totalDegree_mul _ _).trans (add_le_add (hspow M) ?_)
    refine (MvPolynomial.totalDegree_add _ _).trans (max_le (by simp) ?_)
    refine (MvPolynomial.totalDegree_mul _ _).trans ?_
    rw [MvPolynomial.totalDegree_C, add_zero]
    refine (MvPolynomial.totalDegree_add _ _).trans (max_le ?_ ?_)
    · refine (MvPolynomial.totalDegree_pow _ _).trans ?_
      have : (MvPolynomial.X 0 - MvPolynomial.X 1 * MvPolynomial.C RatFunc.X :
          ChartRing L).totalDegree ≤ 1 := by
        refine (MvPolynomial.totalDegree_sub _ _).trans (max_le
          (MvPolynomial.totalDegree_X _).le ?_)
        refine (MvPolynomial.totalDegree_mul _ _).trans ?_
        rw [MvPolynomial.totalDegree_C, add_zero]
        exact (MvPolynomial.totalDegree_X _).le
      calc _ ≤ e * 1 := Nat.mul_le_mul_left _ this
        _ = e := mul_one e
    · refine (MvPolynomial.totalDegree_mul _ _).trans ?_
      rw [MvPolynomial.totalDegree_C, add_zero]
      exact (MvPolynomial.totalDegree_pow _ _).trans
        (by have := MvPolynomial.totalDegree_X (R := RatFunc L) (1 : Fin 3); nlinarith)
  refine le_trans ?_ hbound
  refine (MvPolynomial.totalDegree_sub _ _).trans (max_le ?_ hT3)
  exact (MvPolynomial.totalDegree_add _ _).trans (max_le hT1 hT2)

variable {k : Type*} [Field k] [Algebra (RatFunc L) k] [Algebra L k]
  [IsScalarTower L (RatFunc L) k]

/-- The polynomial read off the chart at `z`:
`P̂_z = z₂ + Σ_{1 ≤ j ≤ d} (N_{ej}(z) / S(z)^(2ej-1)) (X - T₀^e)^j`. -/
noncomputable def hatP (z : Fin 3 → k) : k[X] :=
  C (z 2) + ∑ j ∈ Icc 1 d, C (MvPolynomial.aeval z (chartN R h (e * j)) /
    MvPolynomial.aeval z (chartA R 0 1) ^ (2 * e * j - 1)) *
      (X - C (algebraMap (RatFunc L) k RatFunc.X ^ e)) ^ j

/-- **The cut at a point off the separant**:
`cut_x(z) = S(z)^(2ed-1) (P̂_z(x) - f(x) - ((z₀ - z₁ T₀)^e + z₁^e x) g(x))`. -/
theorem aeval_chartCut (z : Fin 3 → k) (hs : MvPolynomial.aeval z (chartA R 0 1) ≠ 0)
    (he : 1 ≤ e) (x : ι) :
    MvPolynomial.aeval z (chartCut dom f g R e d h x) =
      MvPolynomial.aeval z (chartA R 0 1) ^ (2 * e * d - 1) *
        ((hatP R e d h z).eval (algebraMap L k (pt dom x)) - algebraMap L k (f x) -
          ((z 0 - z 1 * algebraMap (RatFunc L) k RatFunc.X) ^ e +
            z 1 ^ e * algebraMap L k (pt dom x)) * algebraMap L k (g x)) := by
  have hc (c : L) : algebraMap (RatFunc L) k (algebraMap L (RatFunc L) c) = algebraMap L k c :=
    (IsScalarTower.algebraMap_apply L (RatFunc L) k c).symm
  simp only [chartCut, hatP, map_sub, map_add, map_mul, map_pow, map_sum, MvPolynomial.aeval_X,
    MvPolynomial.aeval_C, hc, eval_add, eval_C, eval_finsetSum, eval_mul, eval_pow, eval_sub,
    eval_X]
  generalize MvPolynomial.aeval z (chartA R 0 1) = sz at hs ⊢
  have hsum : ∑ j ∈ Icc 1 d, MvPolynomial.aeval z (chartN R h (e * j)) * sz ^ (2 * e * (d - j)) *
      (algebraMap L k (pt dom x) - algebraMap (RatFunc L) k RatFunc.X ^ e) ^ j =
      sz ^ (2 * e * d - 1) * ∑ j ∈ Icc 1 d, MvPolynomial.aeval z (chartN R h (e * j)) /
        sz ^ (2 * e * j - 1) *
        (algebraMap L k (pt dom x) - algebraMap (RatFunc L) k RatFunc.X ^ e) ^ j := by
    rw [Finset.mul_sum]
    refine sum_congr rfl fun j hj ↦ ?_
    obtain ⟨hj1, hjd⟩ := mem_Icc.mp hj
    have hsplit : sz ^ (2 * e * d - 1) = sz ^ (2 * e * (d - j)) * sz ^ (2 * e * j - 1) := by
      rw [← pow_add]
      congr 1
      have h2 : 1 ≤ e * j := Nat.mul_pos he hj1
      zify [hjd, (by nlinarith : 1 ≤ 2 * e * j), (by nlinarith : 1 ≤ 2 * e * d)]
      ring
    rw [hsplit]
    field_simp
  rw [hsum]
  ring

end Cut

/-! ## Points of counted triples -/

section Genuine

variable {L : Type*} [Field L] (R : MvPolynomial (Fin 3) L) (e d h : ℕ)
  {k : Type*} [Field k] [Algebra (RatFunc L) k] [Algebra L k] [IsScalarTower L (RatFunc L) k]

/-- **The chart point of a triple**: `(α' + β' T₀, β', P(T₀^e))`. -/
noncomputable def chartPoint (α' β' : L) (P : L[X]) : Fin 3 → k :=
  ![algebraMap L k α' + algebraMap L k β' * algebraMap (RatFunc L) k RatFunc.X,
    algebraMap L k β', (P.map (algebraMap L k)).eval (algebraMap (RatFunc L) k RatFunc.X ^ e)]

/-- Evaluating at `T₀`: `L[X] → k` is injective. -/
theorem eval₂_T₀_eq (Q : L[X]) :
    Q.eval₂ (algebraMap L k) (algebraMap (RatFunc L) k RatFunc.X) =
      algebraMap (RatFunc L) k (algebraMap L[X] (RatFunc L) Q) := by
  induction Q using Polynomial.induction_on' with
  | add p q hp hq => simp [hp, hq]
  | monomial n a =>
    rw [eval₂_monomial, ← C_mul_X_pow_eq_monomial, map_mul, map_pow, RatFunc.algebraMap_C,
      RatFunc.algebraMap_X, map_mul, map_pow, IsScalarTower.algebraMap_apply L (RatFunc L) k]
    rfl

theorem eval₂_T₀_ne_zero {Q : L[X]} (hQ : Q ≠ 0) :
    Q.eval₂ (algebraMap L k) (algebraMap (RatFunc L) k RatFunc.X) ≠ 0 := by
  rw [eval₂_T₀_eq]
  exact (map_ne_zero_iff _ (algebraMap (RatFunc L) k).injective).mpr
    ((map_ne_zero_iff _ (RatFunc.algebraMap_injective L)).mpr hQ)

omit [IsScalarTower L (RatFunc L) k] in
/-- **A polynomial identity along the line, at `T₀`**: `Q(T₀, z₀, z₂)` is
`Q(X, α' + β' X, P(X^e))` evaluated at `T₀`. -/
theorem aeval_chartPoint_line (Q : MvPolynomial (Fin 3) L) (α' β' : L) (P : L[X]) :
    MvPolynomial.aeval ![algebraMap (RatFunc L) k RatFunc.X, chartPoint e α' β' P 0,
        chartPoint e α' β' P 2] Q =
      (MvPolynomial.aeval ![X, C α' + C β' * X, P.comp (X ^ e)] Q).eval₂ (algebraMap L k)
        (algebraMap (RatFunc L) k RatFunc.X) := by
  symm
  refine map_aeval_eq (S := L[X]) (S' := k)
    (eval₂RingHom (algebraMap L k) (algebraMap (RatFunc L) k RatFunc.X)) (fun c ↦ ?_) _ _
    (fun i ↦ ?_) Q
  · simp
  · fin_cases i <;> simp [chartPoint, eval₂_comp, eval_map]

/-- On a counted triple, the chart point lies on the surface `R(T₀, Y, Z) = 0`. -/
theorem aeval_chartA_zero_chartPoint {α' β' : L} {P : L[X]}
    (hroot : MvPolynomial.aeval ![X, C α' + C β' * X, P.comp (X ^ e)] R = 0) :
    MvPolynomial.aeval (chartPoint (k := k) e α' β' P) (chartA R 0 0) = 0 := by
  rw [(aeval_chartA_zero R _).1]
  simp only [aeval_chartPoint_line, hroot, eval₂_zero]

/-- On a simple root, the chart point is off the separant. -/
theorem aeval_chartA_one_chartPoint_ne_zero {α' β' : L} {P : L[X]}
    (hsimple : MvPolynomial.aeval ![X, C α' + C β' * X, P.comp (X ^ e)]
      (MvPolynomial.pderiv 2 R) ≠ 0) :
    MvPolynomial.aeval (chartPoint (k := k) e α' β' P) (chartA R 0 1) ≠ 0 := by
  rw [(aeval_chartA_zero R _).2]
  simp only [aeval_chartPoint_line]
  exact eval₂_T₀_ne_zero hsimple

end Genuine

/-! ## The Taylor coefficients of a counted triple -/

section Taylor

/-- Composition commutes with evaluation of a polynomial over polynomials. -/
theorem eval_map_compRingHom {K : Type*} [CommRing K] (Φ : Polynomial K[X]) (E q : K[X]) :
    (Φ.map (compRingHom q)).eval (E.comp q) = (Φ.eval E).comp q := by
  rw [eval_map, ← coe_compRingHom_apply, eval₂_hom, coe_compRingHom_apply]

theorem sum_Icc_one_eq {M : Type*} [AddCommMonoid M] (f : ℕ → M) (d : ℕ) :
    ∑ j ∈ Icc 1 d, f j = ∑ i ∈ range d, f (i + 1) := by
  induction d with
  | zero => simp
  | succ d ih => rw [Finset.sum_Icc_succ_top (by omega), ih, sum_range_succ]

variable {L : Type*} [Field L] (R : MvPolynomial (Fin 3) L) (e d h : ℕ)
  {k : Type*} [Field k] [Algebra (RatFunc L) k] [Algebra L k] [IsScalarTower L (RatFunc L) k]

/-- **The chart reconstructs the candidate** ([CWYZ26, Claim 4.9]): at the chart point of a simple
root `P(X^e)` of `R` along the line, `P̂ = P`. Hensel's numerators are the coefficients of
`P((T₀ + W)^e) - P(T₀^e) = P(T₀^e + W^e) - P(T₀^e)`, whose coefficient of `W^(ej)` is the
`j`-th Taylor coefficient of `P` at `T₀^e`. -/
theorem hatP_eq {p κ : ℕ} [hp : Fact p.Prime] [CharP k p] (he : e = p ^ κ)
    (hR : ∀ m ∈ R.support, m 1 + m 2 ≤ h) (hh : 1 ≤ h) {α' β' : L} {P : L[X]}
    (hP : P.natDegree ≤ d)
    (hroot : MvPolynomial.aeval ![X, C α' + C β' * X, P.comp (X ^ e)] R = 0)
    (hs : MvPolynomial.aeval (chartPoint (k := k) e α' β' P) (chartA R 0 1) ≠ 0) :
    hatP R e d h (chartPoint (k := k) e α' β' P) = P.map (algebraMap L k) := by
  set z := chartPoint (k := k) e α' β' P with hz
  set sz := MvPolynomial.aeval z (chartA R 0 1)
  set T := algebraMap (RatFunc L) k RatFunc.X
  set r := T ^ e
  set Pk := P.map (algebraMap L k)
  set τ := taylor r Pk with hτ
  set Rsz := (chartRs R).map (mapRingHom (MvPolynomial.aeval z).toRingHom) with hRsz
  have he0 : 0 < e := he ▸ pow_pos hp.out.pos κ
  set E : k[X] := expand k e (τ - C (τ.coeff 0))
  set q : k[X] := C (sz ^ 2) * X
  set ε : k[X] := C sz⁻¹ * E.comp q
  have hz2 : z 2 = τ.coeff 0 := by simp [z, chartPoint, τ, taylor_coeff_zero, Pk, r, T]
  -- `R(T₀ + W, z₀ + z₁ W, z₂ + E(W)) = 0`.
  have hRE : Rsz.eval E = 0 := by
    have h1 : Rsz.eval E =
        MvPolynomial.aeval ![C T + X, C (z 0) + C (z 1) * X, C (z 2) + E] R := by
      rw [hRsz, map_chartRs, ← coe_evalRingHom]
      exact map_aeval_eq (S := k[X][X]) (S' := k[X]) (evalRingHom E)
        (fun c ↦ by simp [Polynomial.algebraMap_apply]) _ _ (fun i ↦ by fin_cases i <;> simp [T]) R
    have hfrob : (C T + X : k[X]) ^ e = C r + X ^ e := by
      rw [he, add_pow_char_pow, ← C_pow]
      simp [r, he]
    have hPk : (Pk.comp (X ^ e)).comp (C T + X) = C (z 2) + E := by
      have hL : (Pk.comp (X ^ e)).comp (C T + X) = Pk.comp (C r + X ^ e) := by
        rw [comp_assoc, X_pow_comp, hfrob]
      have hRt : C (z 2) + E = Pk.comp (C r + X ^ e) := by
        rw [hz2]
        simp only [E, map_sub, expand_C]
        rw [add_sub_cancel, expand_eq_comp_X_pow, hτ, taylor_apply, comp_assoc, add_comp, X_comp,
          C_comp, add_comm]
      rw [hL, hRt]
    have h2 : ((compRingHom (C T + X)).comp (mapRingHom (algebraMap L k)))
        (MvPolynomial.aeval ![X, C α' + C β' * X, P.comp (X ^ e)] R) =
        MvPolynomial.aeval ![C T + X, C (z 0) + C (z 1) * X, C (z 2) + E] R := by
      refine map_aeval_eq (S := L[X]) (S' := k[X]) _
        (fun c ↦ by simp [Polynomial.algebraMap_apply]) _ _ (fun i ↦ ?_) R
      fin_cases i
      · simp
      · simp only [RingHom.coe_comp, Function.comp_apply, coe_mapRingHom, coe_compRingHom_apply,
          Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_zero, map_C, map_X, C_comp, X_comp, z,
          chartPoint, T, map_add, map_mul]
        ring
      · simp only [RingHom.coe_comp, Function.comp_apply, coe_mapRingHom, coe_compRingHom_apply,
          Fin.reduceFinMk, Matrix.cons_val, map_comp, Polynomial.map_pow, map_X]
        exact hPk
    rw [h1, ← h2, hroot, map_zero]
  -- Hensel's numerators at `z` are the coefficients of `ε(w) = E(s² w) / s`.
  have h01 : (Rsz.coeff 1).coeff 0 = sz := by simp [Rsz, coeff_map, chartA, sz]
  have hdeg : Rsz.natDegree ≤ h := natDegree_map_le.trans (natDegree_chartRs_le R hR)
  have hE0 : E.coeff 0 = 0 := by
    rw [show (0 : ℕ) = 0 * e from (zero_mul e).symm, coeff_expand_mul he0, coeff_sub,
      coeff_C_zero, sub_self]
  have hε0 : ε.coeff 0 = 0 := by
    simp only [ε, q, coeff_C_mul, coeff_comp_C_mul_X, hE0, mul_zero]
  have hroot' : (Rsz.map (compRingHom q)).eval (C sz * ε) = 0 := by
    have : C sz * ε = E.comp q := by
      rw [← mul_assoc, ← C_mul, mul_inv_cancel₀ hs, C_1, one_mul]
    rw [this, eval_map_compRingHom, hRE, zero_comp]
  have hN := eq_numerators_of_root Rsz sz hs h01 hdeg hh ε hε0 hroot'
  -- `N_{ej}(z) / s^(2ej-1) = τ_j`.
  have hcoeff : ∀ j ∈ Icc 1 d,
      MvPolynomial.aeval z (chartN R h (e * j)) / sz ^ (2 * e * j - 1) = τ.coeff j := by
    intro j hj
    obtain ⟨hj1, -⟩ := mem_Icc.mp hj
    have hej : 1 ≤ e * j := Nat.mul_pos he0 hj1
    have hmap : MvPolynomial.aeval z (chartN R h (e * j)) = numerators Rsz sz h (e * j) :=
      numerators_map (MvPolynomial.aeval z).toRingHom (chartRs R) (chartA R 0 1) h (e * j)
    rw [hmap, ← hN _ hej]
    have hE : E.coeff (e * j) = τ.coeff j := by
      rw [mul_comm, coeff_expand_mul he0, coeff_sub, coeff_C_of_ne_zero (by omega), sub_zero]
    simp only [ε, q, coeff_C_mul, coeff_comp_C_mul_X, hE]
    have hpow : (sz ^ 2) ^ (e * j) = sz * sz ^ (2 * e * j - 1) := by
      rw [← pow_mul, ← pow_succ']
      congr 1
      have : 1 ≤ 2 * e * j := by nlinarith
      rw [Nat.mul_assoc]; omega
    rw [hpow]
    field_simp
  -- Taylor: `P = Σ_j τ_j (X - T₀^e)^j`.
  have hτdeg : τ.natDegree < d + 1 := by
    rw [natDegree_taylor]; exact Nat.lt_succ_of_le (natDegree_map_le.trans hP)
  rw [hatP, sum_congr rfl fun j hj ↦ by rw [hcoeff j hj], hz2]
  conv_rhs => rw [← sum_taylor_eq Pk r, ← hτ, sum_over_range' τ (fun n ↦ by simp) (d + 1) hτdeg,
    sum_range_succ']
  rw [sum_Icc_one_eq, add_comm]
  simp [r, T]

end Taylor
end

end LeanVM.Protocol.Whir.AffineCombiner
