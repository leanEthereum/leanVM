module

public import LeanDa.Scheme
public import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# The additive Reed-Solomon code at rate one half is self-dual

`doc/leanvm/body/d-novel-basis.tex` §sec:ntt-duality on the crate's domain: the `2^14` points
`point b` of `K`, the span of `e_0 … e_13`, embedded in `E`, where the symbols live. Lemma
lem:domain-sum (`sum_eval_eq_zero`): over a finite additive subgroup `D` of a field, the
coefficient of `X^(|D|-1)` of a polynomial of degree below `|D|` is its sum over `D` divided by
`∏_(d ∈ D, d ≠ 0) d`, by Lagrange interpolation, so a polynomial of degree at most `|D| - 2` sums
to zero. Corollary cor:rs-dual (`orthogonal_rsCode`): two codewords of degree below `2^13` are
orthogonal, and the dimensions add up, so the code is its own dual. The novel basis spans the
polynomials of `K[X]` of degree below `2^13` over `K`, so their monomials, which span those of
`E[X]` over `E`: a word orthogonal to every `Xⱼ` on the domain is a codeword
(`mem_rsCode_of_orthogonal`).

The code is also the image of the systematic encoder (`range_encodeRow`).

This module is part of the instantiation of Benedikt Wagner's framework for erasure code
commitments (`PqDas`, ported from https://github.com/b-wagn/fv-pq-da) with LeanDA.
-/

open Polynomial Module

namespace LeanDa

@[expose] public section

/-! ## Bits of `K` -/

theorem ofBits_add (a b : ℕ) : K.ofBits a + K.ofBits b = K.ofBits (a ^^^ b) := by
  apply BF64.ext
  simp [K.ofBits, BF64.add_def, BitVec.ofNat_xor]

theorem ofBits_zero : K.ofBits 0 = 0 := rfl

theorem ofBits_inj {a b : ℕ} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) (h : K.ofBits a = K.ofBits b) :
    a = b := by
  have h' := congrArg (fun x : K ↦ x.toBitVec.toNat) h
  simp only [K.ofBits, BF64.toBitVec_ofBitVec, BitVec.toNat_ofNat] at h'
  rwa [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at h'

/-- Bit `c` of an element of `K`, a `GF(2)`-linear functional. -/
def bitAt (c : ℕ) : K →+ ZMod 2 where
  toFun x := if x.toBitVec.getLsbD c then 1 else 0
  map_zero' := by simp
  map_add' x y := by
    simp only [BF64.add_def, BF64.toBitVec_ofBitVec, BitVec.getLsbD_xor]
    cases x.toBitVec.getLsbD c <;> cases y.toBitVec.getLsbD c <;> decide

theorem zmod_two_cases (g : ZMod 2) : g = 0 ∨ g = 1 := by
  revert g; decide

theorem smul_eq_ite (g : ZMod 2) (x : K) : g • x = if g = 1 then x else 0 := by
  rcases zmod_two_cases g with rfl | rfl
  · simp
  · simp

theorem bitAt_smul (c : ℕ) (g : ZMod 2) (x : K) : bitAt c (g • x) = g * bitAt c x := by
  rw [smul_eq_ite]
  rcases zmod_two_cases g with rfl | rfl <;> simp

theorem bitAt_basis (c : ℕ) (d : Fin 16) : bitAt c (basis d) = if (d : ℕ) = c then 1 else 0 := by
  have hd : (2 : ℕ) ^ (d : ℕ) < 2 ^ 64 := Nat.pow_lt_pow_right (by norm_num) (by omega)
  simp only [bitAt, basis, K.ofBits, AddMonoidHom.coe_mk, ZeroHom.coe_mk,
    BF64.toBitVec_ofBitVec, BitVec.getLsbD_ofNat, Nat.testBit_two_pow]
  by_cases h : (d : ℕ) = c
  · subst h; simp [show (d : ℕ) < 64 by omega]
  · simp [h]

/-- `e_0 … e_15` are linearly independent over `GF(2)`. -/
theorem basis_linearIndependent : LinearIndependent (ZMod 2) basis := by
  rw [Fintype.linearIndependent_iff]
  intro g hg c
  have h := congrArg (bitAt c) hg
  simp only [map_sum, bitAt_smul, bitAt_basis, map_zero, mul_ite, mul_one, mul_zero,
    Fin.val_inj, Finset.sum_ite_eq', Finset.mem_univ, ite_true] at h
  exact h

instance : Fact (LinearIndependent (ZMod 2) basis) := ⟨basis_linearIndependent⟩

/-! ## The domain -/

theorem point_add (a b : ℕ) : point a + point b = point (a ^^^ b) := ofBits_add a b

theorem point_injective : Function.Injective fun b : Fin (2 ^ 14) ↦ ι (point b) := by
  intro a b h
  exact Fin.ext (ofBits_inj (by omega) (by omega) (ι.injective h))

/-- The domain `S_14`, the span of `e_0 … e_13`, in `E`. -/
noncomputable def domain : Finset E := Finset.univ.image fun b : Fin (2 ^ 14) ↦ ι (point b)

theorem card_domain : domain.card = 2 ^ 14 := by
  rw [domain, Finset.card_image_of_injective _ point_injective, Finset.card_univ, Fintype.card_fin]

theorem sub_mem_domain {x y : E} (hx : x ∈ domain) (hy : y ∈ domain) : x - y ∈ domain := by
  simp only [domain, Finset.mem_image, Finset.mem_univ, true_and] at hx hy ⊢
  obtain ⟨a, rfl⟩ := hx
  obtain ⟨b, rfl⟩ := hy
  refine ⟨⟨a ^^^ b, Nat.xor_lt_two_pow a.isLt b.isLt⟩, ?_⟩
  rw [← map_sub, CharTwo.sub_eq_add, point_add]

theorem sum_domain (f : E → E) : ∑ x ∈ domain, f x = ∑ b : Fin (2 ^ 14), f (ι (point b)) := by
  rw [domain, Finset.sum_image fun a _ b _ h ↦ point_injective h]

/-! ## Lemma lem:domain-sum -/

/-- Over a finite additive subgroup `S` of a field, a polynomial of degree at most `|S| - 2`
sums to zero. -/
theorem sum_eval_eq_zero {F : Type*} [Field F] [DecidableEq F] (S : Finset F)
    (hsub : ∀ x ∈ S, ∀ y ∈ S, x - y ∈ S) {P : F[X]} (hP : P.natDegree + 1 < S.card) :
    ∑ x ∈ S, P.eval x = 0 := by
  have hne : S.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨x₀, hx₀⟩ := hne
  have h0 : (0 : F) ∈ S := by simpa using hsub x₀ hx₀ x₀ hx₀
  set c := ∏ d ∈ S.erase 0, d
  have hc : ∀ x ∈ S, ∏ y ∈ S.erase x, (x - y) = c := by
    intro x hx
    refine Finset.prod_nbij' (fun y ↦ x - y) (fun d ↦ x - d) ?_ ?_ ?_ ?_ ?_
    · intro y hy
      simp only [Finset.mem_erase] at hy ⊢
      exact ⟨sub_ne_zero.mpr (Ne.symm hy.1), hsub x hx y hy.2⟩
    · intro d hd
      simp only [Finset.mem_erase] at hd ⊢
      exact ⟨fun h ↦ hd.1 (by rw [sub_eq_self] at h; exact h), hsub x hx d hd.2⟩
    · intro y _; simp
    · intro d _; simp
    · intro y _; rfl
  have hc0 : c ≠ 0 := Finset.prod_ne_zero_iff.mpr fun d hd ↦ Finset.ne_of_mem_erase hd
  have hdeg : P.degree < S.card := by
    refine lt_of_le_of_lt degree_le_natDegree ?_
    exact_mod_cast (by omega : P.natDegree < S.card)
  have hcoeff := Lagrange.coeff_eq_sum (s := S) (v := id) (Set.injOn_id _) hdeg
  rw [coeff_eq_zero_of_natDegree_lt (by omega)] at hcoeff
  simp only [id] at hcoeff
  rw [Finset.sum_congr rfl fun x hx ↦ by rw [hc x hx], ← Finset.sum_div] at hcoeff
  exact (div_eq_zero_iff.mp hcoeff.symm).resolve_right hc0

/-! ## The code -/

/-- Evaluation on the domain, in domain order. -/
noncomputable def evalDomain : E[X] →ₗ[E] Row where
  toFun P b := P.eval (ι (point b))
  map_add' P Q := by ext b; simp
  map_smul' a P := by ext b; simp

/-- **The Reed-Solomon code** `RS[E, S_14, 2^13]`: the values of the polynomials of degree below
`2^13` on the domain. -/
noncomputable def rsCode : Submodule E Row :=
  LinearMap.range (evalDomain.domRestrict (degreeLT E (2 ^ 13)))

theorem mem_rsCode {w : Row} : w ∈ rsCode ↔ ∃ P ∈ degreeLT E (2 ^ 13), evalDomain P = w := by
  simp [rsCode]

/-- The dot product of rows. -/
noncomputable def dotForm : LinearMap.BilinForm E Row := dotProductBilin E E

theorem dotForm_apply (u v : Row) : dotForm u v = ∑ b, u b * v b := by
  simp only [dotForm, dotProductBilin_apply_apply, dotProduct]

theorem dotForm_nondegenerate : dotForm.Nondegenerate := by
  refine ⟨fun u hu ↦ funext fun b ↦ ?_, fun u hu ↦ funext fun b ↦ ?_⟩
  · simpa [dotForm_apply, Pi.single_apply] using hu (Pi.single b 1)
  · simpa [dotForm_apply, Pi.single_apply] using hu (Pi.single b 1)

theorem evalDomain_injOn {P : E[X]} (hP : P ∈ degreeLT E (2 ^ 13)) (h : evalDomain P = 0) :
    P = 0 := by
  rw [mem_degreeLT] at hP
  refine Polynomial.eq_zero_of_degree_lt_of_eval_finset_eq_zero domain ?_ ?_
  · rw [card_domain]; exact lt_of_lt_of_le hP (by norm_num)
  · intro x hx
    simp only [domain, Finset.mem_image, Finset.mem_univ, true_and] at hx
    obtain ⟨b, rfl⟩ := hx
    exact congrFun h b

theorem finrank_rsCode : finrank E rsCode = 2 ^ 13 := by
  rw [rsCode, LinearMap.finrank_range_of_inj]
  · rw [(degreeLTEquiv E (2 ^ 13)).finrank_eq, finrank_fin_fun]
  · intro P Q h
    have hPQ : evalDomain ((P : E[X]) - Q) = 0 := by
      rw [map_sub, sub_eq_zero]; exact h
    exact Subtype.ext (sub_eq_zero.mp (evalDomain_injOn (Submodule.sub_mem _ P.2 Q.2) hPQ))

theorem dotForm_evalDomain (P Q : E[X]) :
    dotForm (evalDomain P) (evalDomain Q) = ∑ x ∈ domain, (P * Q).eval x := by
  rw [dotForm_apply, sum_domain]
  simp [evalDomain]

/-- Two codewords are orthogonal. -/
theorem rsCode_le_orthogonal : rsCode ≤ dotForm.orthogonal rsCode := by
  intro v hv
  rw [LinearMap.BilinForm.mem_orthogonal_iff]
  intro u hu
  obtain ⟨P, hP, rfl⟩ := mem_rsCode.mp hu
  obtain ⟨Q, hQ, rfl⟩ := mem_rsCode.mp hv
  change dotForm (evalDomain P) (evalDomain Q) = 0
  rw [dotForm_evalDomain]
  refine sum_eval_eq_zero domain (fun x hx y hy ↦ sub_mem_domain hx hy) ?_
  rw [card_domain]
  have hP' : P.natDegree < 2 ^ 13 := by
    rcases eq_or_ne P 0 with rfl | h
    · simp
    · exact (natDegree_lt_iff_degree_lt h).mpr (mem_degreeLT.mp hP)
  have hQ' : Q.natDegree < 2 ^ 13 := by
    rcases eq_or_ne Q 0 with rfl | h
    · simp
    · exact (natDegree_lt_iff_degree_lt h).mpr (mem_degreeLT.mp hQ)
  have := natDegree_mul_le (p := P) (q := Q)
  omega

/-- **Corollary cor:rs-dual**: at rate one half the code is its own dual. -/
theorem orthogonal_rsCode : dotForm.orthogonal rsCode = rsCode := by
  refine (Submodule.eq_of_le_of_finrank_eq rsCode_le_orthogonal ?_).symm
  rw [LinearMap.BilinForm.finrank_orthogonal dotForm_nondegenerate, finrank_rsCode,
    finrank_fin_fun]
  norm_num

/-! ## The novel basis -/

/-- The novel basis polynomial `Xⱼ = ∏_i Ŵ_i^(j_i)` (Annex D, Definition def:enc). -/
noncomputable abbrev novelX (u : Fin (2 ^ 13)) : K[X] :=
  AdditiveNTT.Xⱼ (ZMod 2) basis 13 (by norm_num) u

/-- A word's products with a polynomial of `K[X]` on the domain. -/
noncomputable def pairingSum (w : Row) (Q : K[X]) : E := ∑ b : Fin (2 ^ 14), ι (Q.eval (point b)) * w b

/-- `pairingSum`, `K`-linear in the polynomial. -/
noncomputable def pairing (w : Row) : K[X] →ₗ[K] E where
  toFun := pairingSum w
  map_add' P Q := by simp only [pairingSum, eval_add, map_add, add_mul, Finset.sum_add_distrib]
  map_smul' a P := by
    simp only [pairingSum, RingHom.id_apply, Finset.smul_sum]
    refine Finset.sum_congr rfl fun b _ ↦ ?_
    rw [eval_smul, smul_eq_mul, map_mul, Algebra.smul_def, mul_assoc]

theorem pairing_apply (w : Row) (Q : K[X]) : pairing w Q = pairingSum w Q := by
  simp only [pairing, LinearMap.coe_mk, AddHom.coe_mk]

/-- A word orthogonal on the domain to every novel basis polynomial is a codeword: it is then
orthogonal to every monomial below `2^13`, and the polynomials of `E[X]` of degree below `2^13`
are their combinations. -/
theorem mem_rsCode_of_orthogonal {w : Row}
    (h : ∀ u : Fin (2 ^ 13), ∑ b : Fin (2 ^ 14), ι ((novelX u).eval (point b)) * w b = 0) :
    w ∈ rsCode := by
  rw [← orthogonal_rsCode, LinearMap.BilinForm.mem_orthogonal_iff]
  intro v hv
  obtain ⟨P, hP, rfl⟩ := mem_rsCode.mp hv
  have hφ : (pairing w).comp (degreeLT K (2 ^ 13)).subtype = 0 := by
    refine (AdditiveNTT.novelPolynomialBasis (ZMod 2) basis 13 (by norm_num)).ext fun u ↦ ?_
    simp only [AdditiveNTT.novelPolynomialBasis, Basis.coe_mk, LinearMap.zero_apply]
    simpa [pairing_apply, pairingSum, AdditiveNTT.basisVectors] using h u
  have hX : ∀ i < 2 ^ 13, ∑ b : Fin (2 ^ 14), ι (point b) ^ i * w b = 0 := fun i hi ↦ by
    have := LinearMap.congr_fun hφ ⟨X ^ i, mem_degreeLT.mpr (by rw [degree_X_pow]; exact_mod_cast hi)⟩
    rw [LinearMap.comp_apply, Submodule.subtype_apply, LinearMap.zero_apply, pairing_apply,
      pairingSum] at this
    simpa only [eval_pow, eval_X, map_pow] using this
  have hP' : P.natDegree < 2 ^ 13 := by
    rcases eq_or_ne P 0 with rfl | hne
    · simp
    · exact (natDegree_lt_iff_degree_lt hne).mpr (mem_degreeLT.mp hP)
  change dotForm (evalDomain P) w = 0
  rw [dotForm_apply]
  simp only [evalDomain, LinearMap.coe_mk, AddHom.coe_mk, eval_eq_sum_range' hP', Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero fun i hi ↦ ?_
  simp only [mul_assoc, ← Finset.mul_sum, hX i (Finset.mem_range.mp hi), mul_zero]

/-! ## The systematic encoder -/

theorem point_injOn :
    Set.InjOn (fun a : Fin (2 ^ 13) ↦ ι (point a)) ↑(Finset.univ : Finset (Fin (2 ^ 13))) := by
  intro a _ b _ h
  exact Fin.ext (ofBits_inj (by omega) (by omega) (ι.injective h))

theorem interpolate_mem (p : Payload) : interpolate p ∈ degreeLT E (2 ^ 13) := by
  rw [mem_degreeLT]
  refine (Lagrange.degree_interpolate_lt (s := Finset.univ) (r := p) point_injOn).trans_eq ?_
  rw [Finset.card_univ, Fintype.card_fin]

theorem encodeRow_mem (p : Payload) : encodeRow p ∈ rsCode :=
  mem_rsCode.mpr ⟨interpolate p, interpolate_mem p, rfl⟩

/-- The payload is the codeword's first half. -/
theorem encodeRow_systematic (p : Payload) (a : Fin (2 ^ 13)) :
    encodeRow p (Fin.castLE (by norm_num) a) = p a := by
  simp only [encodeRow, interpolate, Fin.val_castLE]
  exact Lagrange.eval_interpolate_at_node p point_injOn (Finset.mem_univ a)

/-- A codeword is the encoding of its first half. -/
theorem encodeRow_firstHalf {w : Row} (hw : w ∈ rsCode) :
    encodeRow (fun a ↦ w (Fin.castLE (by norm_num) a)) = w := by
  obtain ⟨P, hP, rfl⟩ := mem_rsCode.mp hw
  have hint : interpolate (fun a ↦ evalDomain P (Fin.castLE (by norm_num) a)) = P := by
    refine (Lagrange.eq_interpolate_of_eval_eq _ point_injOn ?_ fun a _ ↦ rfl).symm
    simpa using mem_degreeLT.mp hP
  funext b
  rw [encodeRow, hint]
  rfl

/-- **The code is the image of the encoder.** -/
theorem range_encodeRow : Set.range encodeRow = rsCode := by
  ext w
  constructor
  · rintro ⟨p, rfl⟩; exact encodeRow_mem p
  · intro hw; exact ⟨_, encodeRow_firstHalf hw⟩

end

end LeanDa
