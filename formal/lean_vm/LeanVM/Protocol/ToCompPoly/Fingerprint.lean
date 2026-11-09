/-
  LeanVM.Protocol.ToCompPoly.Fingerprint

  Symbolic linear fingerprints of tuples over arbitrary commutative rings.
-/

module

public import Mathlib.Algebra.MvPolynomial.CommRing
public import Mathlib.Algebra.MvPolynomial.Rename
public import Mathlib.RingTheory.MvPolynomial.Basic

/-!
# Linear fingerprints

A tuple `t` of `m` slots is fingerprinted with one weight per slot: `π_A(t) = Σ_i A_i · t_i`, a
linear form in `m` formal variables `A_i` (`fingerprintPoly`). Its evaluation at a point `α` is
`Σ_i α_i · φ(t_i)` (`eval₂_fingerprintPoly`), its coefficient at `A_i` is `t_i`, so distinct tuples
have distinct fingerprints in every characteristic (`fingerprintPoly_injective`), and its total
degree is at most one (`totalDegree_fingerprintPoly`). With a separate variable `X`, indexed by
`none`, a grand-product factor `X − π_A(t)` has total degree at most one as well
(`totalDegree_fingerprintFactorPoly`).

It replaces the multilinear fingerprint `Σ_ι eq(A, ι)·t_ι` on four variables derived from
Verified-zkEVM/leanth (`Leanth/ProofSystem/Logup.lean`, revision
`23929f8c922cd4461ab22dbfaa6520f3ad23a3b2`), whose factors had degree four: leanVM's bus now
draws a weight per slot (`doc/leanvm/body/05-arithmetization.tex`, §5.2). Nothing here
transcribes a source.
-/

namespace LeanVM.Protocol

@[expose] public section

variable {R S : Type*} [CommRing R] [CommRing S] {m : ℕ}

/-- The symbolic linear fingerprint of a tuple: `Σ_i A_i · t_i`. -/
noncomputable def fingerprintPoly (t : Vector R m) : MvPolynomial (Fin m) R :=
  ∑ i : Fin m, MvPolynomial.X i * MvPolynomial.C t[i]

/-- Evaluation at `α` is `Σ_i α_i · φ(t_i)`. -/
theorem eval₂_fingerprintPoly (t : Vector R m) (φ : R →+* S) (α : Fin m → S) :
    MvPolynomial.eval₂ φ α (fingerprintPoly t) = ∑ i : Fin m, α i * φ t[i] := by
  simp [fingerprintPoly, MvPolynomial.eval₂_sum]

/-- The coefficient of `A_i` is slot `i`. -/
theorem coeff_fingerprintPoly (t : Vector R m) (i : Fin m) :
    (fingerprintPoly t).coeff (Finsupp.single i 1) = t[i] := by
  classical
  simp only [fingerprintPoly, MvPolynomial.coeff_sum, MvPolynomial.coeff_X_mul',
    MvPolynomial.coeff_C]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hj
    simp only [Finsupp.mem_support_iff, Finsupp.single_apply]
    simp only [ne_eq, ite_eq_right_iff, one_ne_zero, imp_false, not_not]
    intro h
    exact absurd h.symm hj
  · simp

/-- The constant coefficient is zero. -/
theorem constantCoeff_fingerprintPoly (t : Vector R m) :
    MvPolynomial.constantCoeff (fingerprintPoly t) = 0 := by
  simp [fingerprintPoly]

/-- Distinct tuples give distinct fingerprints; no field hypothesis is needed. -/
theorem fingerprintPoly_injective :
    Function.Injective (fingerprintPoly (R := R) (m := m)) := by
  intro t u h
  apply Vector.ext
  intro i hi
  have := congrArg (fun P ↦ P.coeff (Finsupp.single (⟨i, hi⟩ : Fin m) 1)) h
  simpa only [coeff_fingerprintPoly, Fin.getElem_fin] using this

private theorem totalDegree_X_le_one {σ : Type*} (i : σ) :
    (MvPolynomial.X i : MvPolynomial σ R).totalDegree ≤ 1 := by
  rcases subsingleton_or_nontrivial R with h | h
  · rw [Subsingleton.elim (MvPolynomial.X i : MvPolynomial σ R) 0, MvPolynomial.totalDegree_zero]
    exact zero_le_one
  · exact (MvPolynomial.totalDegree_X i).le

/-- A fingerprint has total degree at most one. -/
theorem totalDegree_fingerprintPoly (t : Vector R m) : (fingerprintPoly t).totalDegree ≤ 1 := by
  classical
  refine (MvPolynomial.totalDegree_finsetSum _ _).trans (Finset.sup_le fun i _ ↦ ?_)
  refine (MvPolynomial.totalDegree_mul _ _).trans ?_
  rw [MvPolynomial.totalDegree_C, add_zero]
  exact totalDegree_X_le_one i

/-- Coefficient mapping commutes with fingerprints, including noninjective maps. -/
theorem map_fingerprintPoly (t : Vector R m) (φ : R →+* S) :
    MvPolynomial.map φ (fingerprintPoly t) = fingerprintPoly (t.map φ) := by
  simp [fingerprintPoly]

/-- A grand-product factor with a distinct formal challenge at `none`; the fingerprint
weights occupy `some i`. -/
noncomputable def fingerprintFactorPoly (t : Vector R m) : MvPolynomial (Option (Fin m)) R :=
  MvPolynomial.X none - MvPolynomial.rename some (fingerprintPoly t)

/-- The extra formal variable evaluates to the grand-product challenge. -/
theorem eval₂_fingerprintFactorPoly (t : Vector R m) (φ : R →+* S) (α : Fin m → S) (β : S) :
    MvPolynomial.eval₂ φ (fun i ↦ i.elim β α) (fingerprintFactorPoly t) =
      β - ∑ i : Fin m, α i * φ t[i] := by
  rw [fingerprintFactorPoly, MvPolynomial.eval₂_sub, MvPolynomial.eval₂_X,
    MvPolynomial.eval₂_rename]
  exact congrArg (β - ·) (eval₂_fingerprintPoly t φ α)

/-- A grand-product factor has total degree at most one. -/
theorem totalDegree_fingerprintFactorPoly (t : Vector R m) :
    (fingerprintFactorPoly t).totalDegree ≤ 1 := by
  classical
  refine (MvPolynomial.totalDegree_sub _ _).trans (max_le ?_ ?_)
  · exact totalDegree_X_le_one _
  · exact (MvPolynomial.totalDegree_rename_le some _).trans (totalDegree_fingerprintPoly t)

end
end LeanVM.Protocol
