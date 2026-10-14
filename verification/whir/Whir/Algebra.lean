import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.CharP.Two
import Mathlib.Data.Fintype.Pi
import Mathlib.Tactic

/-! Algebraic specification of Annex B's honest sumcheck and Annex D's column
weights. These results do not assert that the concrete machine fields satisfy
ring laws, or that an NTT implementation realizes the specified encoder. -/
namespace Whir

open scoped BigOperators

abbrev Cube (n : ℕ) := Fin n → Bool

def cubeConsEquiv (n : ℕ) : Bool × Cube n ≃ Cube (n + 1) where
  toFun p := Fin.cons p.1 p.2
  invFun u := (u 0, fun i => u i.succ)
  left_inv p := by cases p; rfl
  right_inv u := by ext i; exact Fin.cases rfl (fun _ => rfl) i

section Ring
variable {R : Type*} [CommRing R]

lemma sum_cube_succ {n : ℕ} (f : Cube (n + 1) → R) :
    ∑ u, f u = (∑ u, f (Fin.cons false u)) + ∑ u, f (Fin.cons true u) := by
  rw [← Equiv.sum_comp (cubeConsEquiv n)]
  simp [Fintype.sum_prod_type, cubeConsEquiv, add_comm]

def eqWeight {n : ℕ} (r : Fin n → R) (u : Cube n) : R :=
  ∏ i, if u i then r i else 1 - r i

def innerProduct {ι : Type*} [Fintype ι] (w f : ι → R) : R := ∑ i, w i * f i

def mle {n : ℕ} (f : Cube n → R) (r : Fin n → R) : R :=
  innerProduct (eqWeight r) f

def foldFirst {n : ℕ} (f : Cube (n + 1) → R) (r : R) : Cube n → R :=
  fun u => (1 - r) * f (Fin.cons false u) + r * f (Fin.cons true u)

lemma eqWeight_cons {n : ℕ} (r : R) (rs : Fin n → R) (b : Bool) (u : Cube n) :
    eqWeight (Fin.cons r rs) (Fin.cons b u) =
      (if b then r else 1 - r) * eqWeight rs u := by
  simp [eqWeight, Fin.prod_univ_succ]

lemma mle_foldFirst {n : ℕ} (f : Cube (n + 1) → R) (r : R) (rs : Fin n → R) :
    mle (foldFirst f r) rs = mle f (Fin.cons r rs) := by
  unfold mle innerProduct
  rw [sum_cube_succ]
  simp only [eqWeight_cons, Bool.false_eq_true, ↓reduceIte, foldFirst]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro u _
  ring

lemma eqWeight_sum {n : ℕ} (r : Fin n → R) : ∑ u, eqWeight r u = 1 := by
  induction n with
  | zero => simp [eqWeight, Cube]
  | succ n ih =>
    conv_lhs => rw [show r = Fin.cons (r 0) (fun i => r i.succ) by ext i; exact Fin.cases rfl (fun _ => rfl) i]
    rw [sum_cube_succ]
    simp only [eqWeight_cons, Bool.false_eq_true, ↓reduceIte, ← Finset.mul_sum, ih]
    ring

lemma mle_const {n : ℕ} (c : R) (r : Fin n → R) : mle (fun _ => c) r = c := by
  simp [mle, innerProduct, ← Finset.sum_mul, eqWeight_sum]

lemma mle_boolean {n : ℕ} (f : Cube n → R) (u : Cube n) :
    mle f (fun i => if u i then 1 else 0) = f u := by
  induction n with
  | zero =>
    simp only [mle, innerProduct, eqWeight, Finset.univ_eq_empty, Finset.prod_empty, one_mul]
    simp only [Fintype.sum_unique]
    exact congrArg f (Subsingleton.elim _ _)
  | succ n ih =>
    let tail : Cube n := fun i => u i.succ
    have hu : u = Fin.cons (u 0) tail := by ext i; exact Fin.cases rfl (fun _ => rfl) i
    rw [hu]
    have hp : (fun i : Fin (n + 1) => if (Fin.cons (u 0) tail : Cube (n + 1)) i = true then (1 : R) else 0) =
        Fin.cons (if u 0 then 1 else 0) (fun i => if tail i then 1 else 0) := by
      ext i
      exact Fin.cases rfl (fun _ => rfl) i
    rw [hp]
    rw [← mle_foldFirst, ih]
    cases u 0 <;> simp [foldFirst]

def batchWeights {ι τ : Type*} [Fintype τ] (a : τ → R) (w : τ → ι → R) : ι → R :=
  fun i => ∑ t, a t * w t i

lemma innerProduct_batch {ι τ : Type*} [Fintype ι] [Fintype τ]
    (a : τ → R) (w : τ → ι → R) (f : ι → R) :
    innerProduct (batchWeights a w) f = ∑ t, a t * innerProduct (w t) f := by
  simp only [innerProduct, batchWeights, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro t _
  apply Finset.sum_congr rfl
  intro i _
  ring

lemma mle_batch {n : ℕ} {τ : Type*} [Fintype τ]
    (a : τ → R) (w : τ → Cube n → R) (r : Fin n → R) :
    mle (batchWeights a w) r = ∑ t, a t * mle (w t) r := by
  simp only [mle, innerProduct, batchWeights, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro t _
  apply Finset.sum_congr rfl
  intro u _
  ring

/-- Any matrix encoder, hence the novel-basis encoder, commutes with an
arbitrary multilinear fold of its rows. -/
theorem fold_encode_commute {n : ℕ} {ι κ : Type*} [Fintype ι]
    (matrix : κ → ι → R) (f : Cube n → ι → R) (r : Fin n → R) (x : κ) :
    mle (fun u => innerProduct (matrix x) (f u)) r =
      innerProduct (matrix x) (fun i => mle (fun u => f u i) r) := by
  simp only [mle, innerProduct, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro u _
  ring

/-- A column of the novel-basis encoder, parameterized by the normalized
subspace-polynomial values at that column. -/
def tensorWeight {n : ℕ} (s : Fin n → R) (u : Cube n) : R :=
  ∏ i, if u i then s i else 1

def novelEncode {n : ℕ} (s : Fin n → R) (f : Cube n → R) : R :=
  ∑ u, f u * tensorWeight s u

lemma novelEncode_eq_innerProduct {n : ℕ} (s : Fin n → R) (f : Cube n → R) :
    novelEncode s f = innerProduct (tensorWeight s) f := by
  simp [novelEncode, innerProduct, mul_comm]

lemma tensorWeight_cons {n : ℕ} (s : R) (ss : Fin n → R) (b : Bool) (u : Cube n) :
    tensorWeight (Fin.cons s ss) (Fin.cons b u) =
      (if b then s else 1) * tensorWeight ss u := by
  simp [tensorWeight, Fin.prod_univ_succ]

/-- Annex D's column-weight factorization, without a characteristic assumption. -/
theorem mle_tensorWeight {n : ℕ} (s r : Fin n → R) :
    mle (tensorWeight s) r = ∏ i, ((1 - r i) + r i * s i) := by
  induction n with
  | zero => simp [mle, innerProduct, eqWeight, tensorWeight, Cube]
  | succ n ih =>
    have hs : s = Fin.cons (s 0) (fun i => s i.succ) := by ext i; exact Fin.cases rfl (fun _ => rfl) i
    have hr : r = Fin.cons (r 0) (fun i => r i.succ) := by ext i; exact Fin.cases rfl (fun _ => rfl) i
    rw [hs, hr]
    unfold mle innerProduct
    rw [sum_cube_succ, Fin.prod_univ_succ]
    simp only [eqWeight_cons, tensorWeight_cons, Bool.false_eq_true, ↓reduceIte, Fin.cons_zero, Fin.cons_succ, one_mul]
    simp_rw [mul_assoc, ← Finset.mul_sum]
    simp_rw [mul_left_comm (eqWeight _ _) (s 0), ← Finset.mul_sum]
    have h := ih (fun i => s i.succ) (fun i => r i.succ)
    unfold mle innerProduct at h
    rw [h]
    ring

def inducedWeight {n q : ℕ} (a : Fin q → R) (s : Fin q → Fin n → R) : Cube n → R :=
  batchWeights a (fun t => tensorWeight (s t))

theorem inducedWeight_claim {n q : ℕ} (a : Fin q → R) (s : Fin q → Fin n → R)
    (f : Cube n → R) :
    innerProduct (inducedWeight a s) f = ∑ t, a t * novelEncode (s t) f := by
  simp [inducedWeight, innerProduct_batch, novelEncode_eq_innerProduct]

theorem inducedWeight_mle {n q : ℕ} (a : Fin q → R) (s : Fin q → Fin n → R)
    (r : Fin n → R) :
    mle (inducedWeight a s) r = ∑ t, a t * ∏ i, ((1 - r i) + r i * s t i) := by
  simp [inducedWeight, mle_batch, mle_tensorWeight]

/-- The batched claim computed from opened columns is exactly the induced
weight's claim on the folded message, provided those rows are encoded honestly. -/
theorem inducedWeight_opened_columns {lanes n q : ℕ}
    (a : Fin q → R) (s : Fin q → Fin n → R)
    (f : Cube lanes → Cube n → R) (r : Fin lanes → R) :
    (∑ t, a t * mle (fun u => novelEncode (s t) (f u)) r) =
      innerProduct (inducedWeight a s) (fun v => mle (fun u => f u v) r) := by
  rw [inducedWeight_claim]
  apply Finset.sum_congr rfl
  intro t _
  simp only [novelEncode_eq_innerProduct]
  rw [fold_encode_commute]

end Ring

section CharacteristicTwo
variable {R : Type*} [CommRing R] [CharP R 2]

/-- The two scalars sent by `sumcheck::pair_terms`. -/
def roundConstant {n : ℕ} (w f : Cube (n + 1) → R) : R :=
  ∑ u, w (Fin.cons false u) * f (Fin.cons false u)

def roundQuadratic {n : ℕ} (w f : Cube (n + 1) → R) : R :=
  ∑ u, (w (Fin.cons false u) + w (Fin.cons true u)) *
    (f (Fin.cons false u) + f (Fin.cons true u))

/-- Rust's `(a * r + b) * r + c`, where `b = claim + a`. -/
def compactRound (claim u₀ u₂ r : R) : R := (u₂ * r + (claim + u₂)) * r + u₀

lemma compactRound_endpoints (claim u₀ u₂ : R) :
    compactRound claim u₀ u₂ 0 + compactRound claim u₀ u₂ 1 = claim := by
  simp [compactRound, add_assoc]
  ring_nf
  simp [CharTwo.two_eq_zero]

/-- Every degree-at-most-two polynomial satisfying the round sum has exactly
this reconstruction; characteristic two, rather than division by two, is used. -/
theorem compactRound_reconstruct (c b a claim : R)
    (h : c + (c + b + a) = claim) (r : R) :
    compactRound claim c a r = c + b * r + a * r ^ 2 := by
  have hb : claim = b + a := by
    rw [← h]
    rw [← add_assoc, ← add_assoc, CharTwo.add_self_eq_zero, zero_add]
  rw [hb]
  simp only [compactRound, CharTwo.add_cancel_right]
  ring

lemma foldFirst_charTwo {n : ℕ} (f : Cube (n + 1) → R) (r : R) (u : Cube n) :
    foldFirst f r u = f (Fin.cons false u) + r *
      (f (Fin.cons false u) + f (Fin.cons true u)) := by
  rw [foldFirst, CharTwo.sub_eq_add]
  ring

private lemma honest_pair (w₀ w₁ f₀ f₁ r : R) :
    ((w₀ + w₁) * (f₀ + f₁) * r +
      (w₀ * f₀ + w₁ * f₁ + (w₀ + w₁) * (f₀ + f₁))) * r + w₀ * f₀ =
    (w₀ + r * (w₀ + w₁)) * (f₀ + r * (f₀ + f₁)) := by
  have h : w₀ * f₀ + w₁ * f₁ + (w₀ + w₁) * (f₀ + f₁) = w₀ * f₁ + w₁ * f₀ := by
    linear_combination (f₀ * CharTwo.add_self_eq_zero w₀) + (f₁ * CharTwo.add_self_eq_zero w₁)
  rw [h]
  ring_nf
  simp [CharTwo.two_eq_zero]

/-- One honest round preserves the weighted-claim invariant for every challenge. -/
theorem honest_round {n : ℕ} (w f : Cube (n + 1) → R) (r : R) :
    compactRound (innerProduct w f) (roundConstant w f) (roundQuadratic w f) r =
      innerProduct (foldFirst w r) (foldFirst f r) := by
  unfold compactRound innerProduct roundConstant roundQuadratic
  rw [sum_cube_succ]
  simp only [← Finset.sum_add_distrib, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro u _
  rw [foldFirst_charTwo, foldFirst_charTwo]
  exact honest_pair _ _ _ _ _

/-- Execute all compact verifier updates using honest prover messages. The
starting claim is an input, so completeness is not built into the evaluator. -/
def honestSumcheck : (n : ℕ) → (Cube n → R) → (Cube n → R) → (Fin n → R) → R → R
  | 0, _, _, _, claim => claim
  | n + 1, w, f, r, claim =>
    honestSumcheck n (foldFirst w (r 0)) (foldFirst f (r 0)) (fun i => r i.succ)
      (compactRound claim (roundConstant w f) (roundQuadratic w f) (r 0))

/-- All-round honest sumcheck completeness, including zero rounds. -/
theorem honestSumcheck_complete (n : ℕ) (w f : Cube n → R) (r : Fin n → R) :
    honestSumcheck n w f r (innerProduct w f) = mle w r * mle f r := by
  induction n with
  | zero => simp [honestSumcheck, innerProduct, mle, eqWeight, Cube]
  | succ n ih =>
    rw [honestSumcheck, honest_round, ih, mle_foldFirst, mle_foldFirst]
    have hr : Fin.cons (r 0) (fun i => r i.succ) = r := by ext i; exact Fin.cases rfl (fun _ => rfl) i
    rw [hr]

/-- Batching honest claims and then running every sumcheck round closes with
the verifier's terminal product, for arbitrary batch coefficients. Powers of
the transcript challenge are a special case. -/
theorem honestSumcheck_batched_complete {n q : ℕ} (a : Fin q → R)
    (w : Fin q → Cube n → R) (f : Cube n → R) (c : Fin q → R)
    (honest : ∀ t, c t = innerProduct (w t) f) (r : Fin n → R) :
    honestSumcheck n (batchWeights a w) f r (∑ t, a t * c t) =
      (∑ t, a t * mle (w t) r) * mle f r := by
  simp_rw [honest]
  rw [← innerProduct_batch, honestSumcheck_complete, mle_batch]

theorem inducedWeight_mle_charTwo {n q : ℕ} (a : Fin q → R)
    (s : Fin q → Fin n → R) (r : Fin n → R) :
    mle (inducedWeight a s) r = ∑ t, a t * ∏ i, (1 + r i * (1 + s t i)) := by
  rw [inducedWeight_mle]
  apply Finset.sum_congr rfl
  intro t _
  congr 1
  apply Finset.prod_congr rfl
  intro i _
  rw [CharTwo.sub_eq_add]
  ring

end CharacteristicTwo

section Embedding
variable {K E : Type*} [CommRing K] [CommRing E]

/-- The mixed K/E path needs a ring homomorphism. This is a typed hypothesis,
not an unproved assertion about the concrete bitfield implementation. -/
theorem novelEncode_lift (embed : K →+* E) {n : ℕ} (s : Fin n → K) (f : Cube n → K) :
    novelEncode (fun i => embed (s i)) (fun u => embed (f u)) = embed (novelEncode s f) := by
  simp only [novelEncode, map_sum, map_mul, tensorWeight, map_prod]
  apply Finset.sum_congr rfl
  intro u _
  congr 1
  apply Finset.prod_congr rfl
  intro i _
  cases u i <;> simp

end Embedding

end Whir

#print axioms Whir.mle_boolean
#print axioms Whir.mle_foldFirst
#print axioms Whir.innerProduct_batch
#print axioms Whir.fold_encode_commute
#print axioms Whir.mle_tensorWeight
#print axioms Whir.inducedWeight_claim
#print axioms Whir.inducedWeight_mle_charTwo
#print axioms Whir.inducedWeight_opened_columns
#print axioms Whir.compactRound_reconstruct
#print axioms Whir.honest_round
#print axioms Whir.honestSumcheck_complete
#print axioms Whir.honestSumcheck_batched_complete
#print axioms Whir.novelEncode_lift
