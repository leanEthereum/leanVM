module

public import LeanVMCircuits.Rec.Field

@[expose] public section

/-!
The recursion machine's extension `E = K[y] / (y^3 + y + 1)`, an element written as three `K` limbs `(c0, c1, c2)`
for `c0 + c1 y + c2 y^2`, and the limb formulas of its arithmetic.
-/

namespace LeanVMCircuits.Rec

open Polynomial

noncomputable def extModulus : K[X] := X ^ 3 + X + 1

abbrev E := AdjoinRoot extModulus

noncomputable def y : E := AdjoinRoot.root extModulus

noncomputable def emb (k : K) : E := AdjoinRoot.of extModulus k

/-- The element `c0 + c1 y + c2 y^2` of `E`. -/
noncomputable def toE (c0 c1 c2 : K) : E := emb c0 + emb c1 * y + emb c2 * y ^ 2

theorem y_cubed : y ^ 3 + y + 1 = 0 := by
  have h : AdjoinRoot.mk extModulus (X ^ 3 + X + 1) = 0 := AdjoinRoot.mk_self
  simp only [map_add, map_pow, AdjoinRoot.mk_X, map_one] at h
  exact h

theorem two_K : (2 : K) = 0 := two_eq_zero

theorem two_E : (2 : E) = 0 := by
  have h : AdjoinRoot.of extModulus (2 : K) = AdjoinRoot.of extModulus 0 := by rw [two_K]
  rwa [map_ofNat, map_zero] at h

theorem emb_add (a b : K) : emb (a + b) = emb a + emb b := map_add _ a b
theorem emb_zero : emb 0 = 0 := map_zero _

theorem emb_mul (a b : K) : emb (a * b) = emb a * emb b := map_mul _ a b

/-- The product of two elements by their limbs: `p_i = sum_{j+l=i} a_j b_l`, then `y^3 = y + 1` and `y^4 = y^2 + y`
fold `p_3` and `p_4` down. -/
theorem toE_mul (a0 a1 a2 b0 b1 b2 : K) :
    toE a0 a1 a2 * toE b0 b1 b2 =
      toE (a0 * b0 + (a1 * b2 + a2 * b1)) (a0 * b1 + a1 * b0 + (a1 * b2 + a2 * b1) + a2 * b2)
        (a0 * b2 + a1 * b1 + a2 * b0 + a2 * b2) := by
  simp only [toE, emb_add, emb_mul]
  set A0 := emb a0; set A1 := emb a1; set A2 := emb a2
  set B0 := emb b0; set B1 := emb b1; set B2 := emb b2
  linear_combination (A1 * B2 + A2 * B1 + A2 * B2 * y) * y_cubed -
    ((A1 * B2 + A2 * B1) * (1 + y) + A2 * B2 * (y + y ^ 2)) * two_E

theorem toE_add (a0 a1 a2 b0 b1 b2 : K) : toE a0 a1 a2 + toE b0 b1 b2 = toE (a0 + b0) (a1 + b1) (a2 + b2) := by
  simp only [toE, emb_add]; ring

/-- An element times a `K` scalar, limb by limb. -/
theorem toE_smul (a0 a1 a2 k : K) : toE a0 a1 a2 * emb k = toE (a0 * k) (a1 * k) (a2 * k) := by
  simp only [toE, emb_mul]; ring

theorem extModulus_monic : extModulus.Monic := by unfold extModulus; monicity!

theorem extModulus_natDegree : extModulus.natDegree = 3 := by unfold extModulus; compute_degree!

/-- The limbs of an element are its coordinates in the basis `1, y, y^2`: two limb triples naming one element are
equal. -/
theorem toE_injective (a0 a1 a2 b0 b1 b2 : K) (h : toE a0 a1 a2 = toE b0 b1 b2) : a0 = b0 ∧ a1 = b1 ∧ a2 = b2 := by
  set pb := AdjoinRoot.powerBasis' extModulus_monic
  have hdim : pb.dim = 3 := extModulus_natDegree
  have key : ∀ c0 c1 c2 : K, pb.basis.repr (toE c0 c1 c2) =
      fun i : Fin pb.dim => if (i : ℕ) = 0 then c0 else if (i : ℕ) = 1 then c1 else if (i : ℕ) = 2 then c2 else 0 := by
    intro c0 c1 c2
    have hsum : toE c0 c1 c2 = ∑ i : Fin pb.dim,
        (if (i : ℕ) = 0 then c0 else if (i : ℕ) = 1 then c1 else if (i : ℕ) = 2 then c2 else 0) • pb.basis i := by
      rw [PowerBasis.coe_basis]
      have hd : pb.dim = 3 := hdim
      rw [Fin.sum_univ_eq_sum_range (fun i => (if i = 0 then c0 else if i = 1 then c1 else if i = 2 then c2 else 0) •
        pb.gen ^ i), hd]
      simp [Finset.sum_range_succ, toE, pb, emb, Algebra.smul_def, y]
    rw [hsum, Module.Basis.repr_sum_self]
  have h0 := congrFun (key a0 a1 a2) ⟨0, by omega⟩
  have h1 := congrFun (key a0 a1 a2) ⟨1, by omega⟩
  have h2 := congrFun (key a0 a1 a2) ⟨2, by omega⟩
  rw [h] at h0 h1 h2
  rw [key] at h0 h1 h2
  simp at h0 h1 h2
  exact ⟨h0.symm, h1.symm, h2.symm⟩

end LeanVMCircuits.Rec
