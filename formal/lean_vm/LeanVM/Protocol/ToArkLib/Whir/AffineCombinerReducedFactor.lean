/-
  LeanVM.Protocol.ToArkLib.Whir.AffineCombinerReducedFactor

  [CYWZ26, preprint], Lemma 4.3 for one irreducible factor: its Frobenius reduction `R` (the
  preprint's `R_i`, `Q_i(X^e, Y^e, Z) = R_i^e`), and the bound `h (h - 1)` on the lines along which
  `R` and `∂_Z R` have a common root. Candidate for ArkLib.
-/

module

public import LeanVM.Protocol.ToArkLib.Whir.AffineCombinerYZDegree
public import ArkLib.Data.Polynomial.FrobeniusContraction
public import ArkLib.Data.Polynomial.FractionFieldResultant
public import ArkLib.Data.Polynomial.ResultantDegree
public import ArkLib.Data.Polynomial.ResultantSpecialization
public import Mathlib.FieldTheory.Perfect

/-!
# The Frobenius reduction of a factor

Let `L` be a perfect field of characteristic `p` and `q ∈ L[X, Y, Z]` irreducible with positive
`Z`-degree. In the nested form `L[X][Y][Z]`, ArkLib's Frobenius contraction writes
`q = G(X, Y, Z^e)`, `e = p^κ`, with `G` irreducible and `∂_Z G ≠ 0`. The reduced factor `R` is
`G` with every coefficient replaced by its `e`-th root (`exists_reducedFactor`):

* `R` is irreducible, `∂_Z R ≠ 0`, `1 ≤ yzDeg R ≤ yzDeg q` and `e ≤ deg_Z q`;
* if `q(X, α + β X, P) = 0` and `α'^e = α`, `β'^e = β`, then `R(X, α' + β' X, P(X^e)) = 0`, as
  `R(X, α' + β' X, P(X^e))^e = q(X, α + β X, P)(X^e)`.

`card_excludedLines_le`: for an irreducible `R` with `∂_Z R ≠ 0`, at most `h (h - 1)` pairs
`(α, β) ∈ F²` (`h = yzDeg R`) have a root `P(X^e)` of `R(X, α' + β' X, Z)` at which
`∂_Z R(X, α' + β' X, Z)` also vanishes: the resultant `Res_Z(R, ∂_Z R) ∈ L[X][Y]` is nonzero
(ArkLib's `resultant_derivative_ne_zero_of_irreducible`), vanishes at `Y = α' + β' X` there
(`map_resultant_eq_zero_of_common_root`), and has `Y`-degree at most `(2b - 1)h - b² ≤ h (h - 1)`
(`natDegree_resultant_derivative_padded_le_of_coeff_add_le`).
-/

namespace LeanVM.Protocol.Whir.AffineCombiner

open Polynomial

@[expose] public section

variable {L : Type*} [Field L]

/-! ## Ring homs out of `L[X][Y][Z]` -/

theorem nested_ringHom_ext {S : Type*} [Semiring S] {f g : L[X][X][X] →+* S}
    (h0 : ∀ c : L, f (C (C (C c))) = g (C (C (C c)))) (h1 : f (C (C X)) = g (C (C X)))
    (h2 : f (C X) = g (C X)) (h3 : f X = g X) : f = g := by
  refine Polynomial.ringHom_ext (fun a ↦ ?_) h3
  have hC : f.comp C = g.comp C := by
    refine Polynomial.ringHom_ext (fun b ↦ ?_) h2
    have : (f.comp C).comp C = (g.comp C).comp C :=
      Polynomial.ringHom_ext (fun c ↦ h0 c) h1
    exact congrArg (fun φ : L[X] →+* S ↦ φ b) this
  exact congrArg (fun φ : L[X][X] →+* S ↦ φ a) hC

theorem trivEval_X_eq (y z : L[X]) (A : L[X][X][X]) :
    trivEval X y z A = (A.map (evalRingHom y)).eval z := by
  rw [eval_map]
  have : eval₂RingHom (eval₂RingHom (C : L →+* L[X]) X) y = evalRingHom y := by
    refine Polynomial.ringHom_ext (fun a ↦ ?_) (by simp)
    simp
  simp only [trivEval, coe_eval₂RingHom, this]

/-- `trivEval` commutes with every ring endomorphism of `L[X]` fixing `L`. -/
theorem map_trivEval (φ : L[X] →+* L[X]) (hφ : ∀ c, φ (C c) = C c) (x y z : L[X])
    (A : L[X][X][X]) : φ (trivEval x y z A) = trivEval (φ x) (φ y) (φ z) A := by
  have : φ.comp (trivEval x y z) = trivEval (φ x) (φ y) (φ z) :=
    nested_ringHom_ext (fun c ↦ by simp [trivEval, hφ]) (by simp [trivEval])
      (by simp [trivEval]) (by simp [trivEval])
  exact congrArg (fun ψ : L[X][X][X] →+* L[X] ↦ ψ A) this

theorem trivEval_expand (x y z : L[X]) (e : ℕ) (A : L[X][X][X]) :
    trivEval x y z (expand _ e A) = trivEval x y (z ^ e) A := by
  simp only [trivEval, coe_eval₂RingHom, expand_eq_comp_X_pow, eval₂_comp, eval₂_X_pow]

/-! ## The reduction -/

variable {p : ℕ} [Fact p.Prime] [CharP L p] [PerfectRing L p]

/-- **The Frobenius reduction of an irreducible factor** ([CYWZ26, Lemma 4.3, (4.6), (4.7)]). -/
theorem exists_reducedFactor (q : MvPolynomial (Fin 3) L) (hq : Irreducible q)
    (hZ : 0 < MvPolynomial.degreeOf 2 q) :
    ∃ (R : MvPolynomial (Fin 3) L) (κ : ℕ), Irreducible R ∧ MvPolynomial.pderiv 2 R ≠ 0 ∧
      1 ≤ yzDeg R ∧ yzDeg R ≤ yzDeg q ∧ p ^ κ ≤ MvPolynomial.degreeOf 2 q ∧
      ∀ (α β : L) (P : L[X]), MvPolynomial.aeval ![X, C α + C β * X, P] q = 0 →
        ∀ α' β' : L, α' ^ p ^ κ = α → β' ^ p ^ κ = β →
          MvPolynomial.aeval ![X, C α' + C β' * X, P.comp (X ^ p ^ κ)] R = 0 := by
  classical
  set A := trivEquiv L q with hA
  have hAirr : Irreducible A := (MulEquiv.irreducible_iff (trivEquiv L).toMulEquiv).mpr hq
  -- `A` has positive degree in `Z`.
  have hApos : 0 < A.natDegree := by
    obtain ⟨m, hm, hm2⟩ : ∃ m ∈ q.support, 0 < m 2 := by
      by_contra h
      push Not at h
      have : MvPolynomial.degreeOf 2 q ≤ 0 := by
        rw [MvPolynomial.degreeOf_le_iff]; intro m hm; exact h m hm
      omega
    have hc : ((A.coeff (m 2)).coeff (m 1)).coeff (m 0) ≠ 0 := by
      rw [hA, coeff_trivEquiv]; exact MvPolynomial.mem_support_iff.mp hm
    exact lt_of_lt_of_le hm2 (le_natDegree_of_ne_zero (fun h ↦ hc (by rw [h]; simp)))
  obtain ⟨κ, G, hGd, hGA, -, hGpos, hGirr⟩ :=
    exists_irreducible_frobeniusContraction_expChar p hApos hAirr
  set e := p ^ κ with he
  have he0 : 0 < e := pow_pos (Fact.out : p.Prime).pos κ
  set σ : L ≃+* L := (iterateFrobeniusEquiv L p κ).symm
  set Ψ : L[X][X][X] ≃+* L[X][X][X] := mapEquiv (mapEquiv (mapEquiv σ))
  set R := (trivEquiv L).symm (Ψ G) with hRdef
  have hRt : trivEquiv L R = Ψ G := by simp [hRdef]
  -- Coefficients.
  have hcoeffR : ∀ m, R.coeff m = σ (((G.coeff (m 2)).coeff (m 1)).coeff (m 0)) := by
    intro m
    rw [← coeff_trivEquiv, hRt]
    simp [Ψ, coeff_map]
  have hcoeffq : ∀ i j k, q.coeff (tri k j (e * i)) = ((G.coeff i).coeff j).coeff k := by
    intro i j k
    rw [← coeff_trivEquiv, tri_two, tri_one, tri_zero, ← hA, ← hGA, coeff_expand_mul' he0]
  have hσ : ∀ c, σ c = 0 ↔ c = 0 := fun c ↦ map_eq_zero_iff σ σ.injective
  refine ⟨R, κ, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hRdef]
    exact (MulEquiv.irreducible_iff (trivEquiv L).symm.toMulEquiv).mpr
      ((MulEquiv.irreducible_iff Ψ.toMulEquiv).mpr hGirr)
  · intro h0
    apply hGd
    have := congrArg (trivEquiv L) h0
    rw [trivEquiv_pderiv, hRt, map_zero] at this
    have hΨd : derivative (Ψ G) = Ψ (derivative G) := by
      simp [Ψ, derivative_map]
    rw [hΨd] at this
    exact (map_eq_zero_iff Ψ Ψ.injective).mp this
  · -- The top `Z`-coefficient of `G` gives a monomial of `R` with `Z`-exponent at least `1`.
    obtain ⟨j, hj⟩ : ∃ j, (G.coeff G.natDegree).coeff j ≠ 0 := by
      by_contra h; push Not at h
      exact (leadingCoeff_ne_zero.mpr (ne_zero_of_natDegree_gt hGpos)) (Polynomial.ext h)
    obtain ⟨k, hk⟩ : ∃ k, ((G.coeff G.natDegree).coeff j).coeff k ≠ 0 := by
      by_contra h; push Not at h
      exact hj (Polynomial.ext h)
    have hmem : tri k j G.natDegree ∈ R.support := by
      rw [MvPolynomial.mem_support_iff, hcoeffR]
      simpa [hσ] using hk
    have := le_yzDeg hmem
    simp only [tri_one, tri_two] at this
    omega
  · rw [yzDeg_le_iff]
    intro m hm
    have hc : ((G.coeff (m 2)).coeff (m 1)).coeff (m 0) ≠ 0 := by
      have := MvPolynomial.mem_support_iff.mp hm
      rwa [hcoeffR, Ne, hσ] at this
    have hmq : tri (m 0) (m 1) (e * m 2) ∈ q.support := by
      rw [MvPolynomial.mem_support_iff, hcoeffq]; exact hc
    have := le_yzDeg hmq
    simp only [tri_one, tri_two] at this
    have : m 2 ≤ e * m 2 := Nat.le_mul_of_pos_left _ he0
    omega
  · obtain ⟨j, hj⟩ : ∃ j, (G.coeff G.natDegree).coeff j ≠ 0 := by
      by_contra h; push Not at h
      exact (leadingCoeff_ne_zero.mpr (ne_zero_of_natDegree_gt hGpos)) (Polynomial.ext h)
    obtain ⟨k, hk⟩ : ∃ k, ((G.coeff G.natDegree).coeff j).coeff k ≠ 0 := by
      by_contra h; push Not at h
      exact hj (Polynomial.ext h)
    have hmq : tri k j (e * G.natDegree) ∈ q.support := by
      rw [MvPolynomial.mem_support_iff, hcoeffq]; exact hk
    have := MvPolynomial.monomial_le_degreeOf 2 hmq
    simp only [tri_two] at this
    exact le_trans (Nat.le_mul_of_pos_right _ hGpos) this
  · -- `R(X, α' + β' X, P(X^e))^e = q(X, α + β X, P)(X^e)`.
    intro α β P hqP α' β' hα hβ
    set frob : L[X] →+* L[X] := iterateFrobenius L[X] p κ
    have hfrob (x : L[X]) : frob x = x ^ e := rfl
    set cmp : L[X] →+* L[X] := compRingHom (X ^ e)
    have hRfrob : frob (MvPolynomial.aeval ![X, C α' + C β' * X, P.comp (X ^ e)] R) =
        trivEval (X ^ e) (C α + C β * X ^ e) ((P.comp (X ^ e)) ^ e) G := by
      rw [← trivEval_trivEquiv, hRt]
      have : frob.comp ((trivEval X (C α' + C β' * X) (P.comp (X ^ e))).comp Ψ.toRingHom) =
          trivEval (X ^ e) (C α + C β * X ^ e) ((P.comp (X ^ e)) ^ e) := by
        refine nested_ringHom_ext (fun c ↦ ?_) ?_ ?_ ?_
        · simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, Ψ,
            mapEquiv_apply, map_C, trivEval, coe_eval₂RingHom, eval₂_C, hfrob]
          rw [← C_pow, show σ c ^ e = c from (iterateFrobeniusEquiv L p κ).apply_symm_apply c]
        · simp [Ψ, trivEval, hfrob]
        · simp [Ψ, trivEval, hfrob, add_pow_char_pow, mul_pow, ← C_pow, hα, hβ, he]
        · simp [Ψ, trivEval, hfrob]
      exact congrArg (fun φ : L[X][X][X] →+* L[X] ↦ φ G) this
    have hqfrob : cmp (MvPolynomial.aeval ![X, C α + C β * X, P] q) =
        trivEval (X ^ e) (C α + C β * X ^ e) ((P.comp (X ^ e)) ^ e) G := by
      rw [← trivEval_trivEquiv, ← hA, ← hGA, trivEval_expand, map_trivEval cmp
        (fun c ↦ by simp [cmp])]
      simp [cmp, pow_comp]
    rw [hqP, map_zero, ← hRfrob, hfrob] at hqfrob
    exact pow_eq_zero_iff he0.ne' |>.mp hqfrob.symm

end

end LeanVM.Protocol.Whir.AffineCombiner
