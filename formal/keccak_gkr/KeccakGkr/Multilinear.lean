import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Data.Fintype.Pi

/-!
# Cubes, equality tables and multilinear extensions

A point of the Boolean cube `Cube n` is `Fin n → Bool`, and `toPt` reads it in the field.
`eqPoly r z` is the multilinear equality polynomial, `mle f` the multilinear extension of a
table `f` on the cube. `IndivDeg d f` says that `f` is a polynomial of degree at most `d` in each
variable separately, which is what a sumcheck's soundness needs of its summand.
-/

open Polynomial

namespace KeccakGkr

variable {E : Type} [Field E]

/-- A point of the Boolean cube. -/
abbrev Cube (n : ℕ) := Fin n → Bool

/-- A bit, in the field. -/
def bit (b : Bool) : E := if b then 1 else 0

@[simp] theorem bit_true : (bit true : E) = 1 := rfl
@[simp] theorem bit_false : (bit false : E) = 0 := rfl

/-- A cube point, in the field. -/
def toPt {n : ℕ} (x : Cube n) : Fin n → E := fun i => bit (x i)

/-- The multilinear equality polynomial. -/
def eqPoly {n : ℕ} (r z : Fin n → E) : E := ∏ i, (r i * z i + (1 - r i) * (1 - z i))

/-- The multilinear extension of a table on the cube. -/
def mle {n : ℕ} (f : Cube n → E) (r : Fin n → E) : E := ∑ x, eqPoly r (toPt x) * f x

theorem eqPoly_comm {n : ℕ} (r z : Fin n → E) : eqPoly r z = eqPoly z r := by
  unfold eqPoly
  refine Finset.prod_congr rfl fun i _ => by ring

@[simp] theorem toPt_cons {n : ℕ} (b : Bool) (x : Cube n) :
    (toPt (Fin.cons b x : Cube (n + 1)) : Fin (n + 1) → E) = Fin.cons (bit b) (toPt x) := by
  funext i
  refine Fin.cases rfl (fun j => rfl) i

@[simp] theorem toPt_snoc {n : ℕ} (b : Bool) (x : Cube n) :
    (toPt (Fin.snoc x b : Cube (n + 1)) : Fin (n + 1) → E) = Fin.snoc (toPt x) (bit b) := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i <;> simp [toPt]

theorem eqPoly_cons {n : ℕ} (r₀ z₀ : E) (r z : Fin n → E) :
    eqPoly (Fin.cons r₀ r : Fin (n + 1) → E) (Fin.cons z₀ z) =
      (r₀ * z₀ + (1 - r₀) * (1 - z₀)) * eqPoly r z := by
  simp [eqPoly, Fin.prod_univ_succ]

theorem eqPoly_snoc {n : ℕ} (r₀ z₀ : E) (r z : Fin n → E) :
    eqPoly (Fin.snoc r r₀ : Fin (n + 1) → E) (Fin.snoc z z₀) =
      eqPoly r z * (r₀ * z₀ + (1 - r₀) * (1 - z₀)) := by
  simp [eqPoly, Fin.prod_univ_castSucc]

@[simp] theorem eqPoly_zero (r z : Fin 0 → E) : eqPoly r z = 1 := by simp [eqPoly]

theorem bit_eq_one_sub (b : Bool) : (1 - bit b : E) = bit (!b) := by cases b <;> simp [bit]

theorem eqPoly_toPt_toPt {n : ℕ} (x y : Cube n) :
    eqPoly (toPt x : Fin n → E) (toPt y) = if x = y then 1 else 0 := by
  induction n with
  | zero => simp [Subsingleton.elim x y]
  | succ n ih =>
    rw [← Fin.cons_self_tail x, ← Fin.cons_self_tail y, toPt_cons, toPt_cons, eqPoly_cons, ih]
    simp only [Fin.cons_inj]
    cases x 0 <;> cases y 0 <;> by_cases h : Fin.tail x = Fin.tail y <;> simp [h]

theorem sum_cube_cons {M : Type} [AddCommMonoid M] {n : ℕ} (g : Cube (n + 1) → M) :
    ∑ x, g x = ∑ b, ∑ x' : Cube n, g (Fin.cons b x') := by
  rw [← (Fin.consEquiv fun _ => Bool).sum_comp, Fintype.sum_prod_type]
  rfl

theorem sum_cube_snoc {M : Type} [AddCommMonoid M] {n : ℕ} (g : Cube (n + 1) → M) :
    ∑ x, g x = ∑ b, ∑ x' : Cube n, g (Fin.snoc x' b) := by
  rw [← (Fin.snocEquiv fun _ => Bool).sum_comp, Fintype.sum_prod_type]
  rfl

theorem sum_eqPoly {n : ℕ} (r : Fin n → E) : ∑ x : Cube n, eqPoly r (toPt x) = 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_cube_cons]
    rw [← Fin.cons_self_tail r]
    simp only [toPt_cons, eqPoly_cons, ← Finset.mul_sum, ih, Fintype.sum_bool, bit_true,
      bit_false]
    ring

theorem mle_toPt {n : ℕ} (f : Cube n → E) (x : Cube n) : mle f (toPt x) = f x := by
  simp [mle, eqPoly_toPt_toPt]

/-! ## Degree in each variable -/

/-- `f` has degree at most `d` in each variable. -/
def IndivDeg {n : ℕ} (d : ℕ) (f : (Fin n → E) → E) : Prop :=
  ∀ (i : Fin n) (x : Fin n → E), ∃ p : E[X], p.natDegree ≤ d ∧
    ∀ t, f (Function.update x i t) = p.eval t

namespace IndivDeg

variable {n : ℕ}

theorem const (c : E) : IndivDeg (n := n) 0 fun _ => c :=
  fun _ _ => ⟨C c, by simp, by simp⟩

theorem mono {d d' : ℕ} {f : (Fin n → E) → E} (h : IndivDeg d f) (hd : d ≤ d') :
    IndivDeg d' f := fun i x => by
  obtain ⟨p, hp, hf⟩ := h i x
  exact ⟨p, hp.trans hd, hf⟩

theorem add {d₁ d₂ : ℕ} {f g : (Fin n → E) → E} (hf : IndivDeg d₁ f) (hg : IndivDeg d₂ g) :
    IndivDeg (max d₁ d₂) (f + g) := fun i x => by
  obtain ⟨p, hp, hp'⟩ := hf i x
  obtain ⟨q, hq, hq'⟩ := hg i x
  exact ⟨p + q, (natDegree_add_le _ _).trans (max_le_max hp hq), fun t => by simp [hp', hq']⟩

theorem mul {d₁ d₂ : ℕ} {f g : (Fin n → E) → E} (hf : IndivDeg d₁ f) (hg : IndivDeg d₂ g) :
    IndivDeg (d₁ + d₂) (f * g) := fun i x => by
  obtain ⟨p, hp, hp'⟩ := hf i x
  obtain ⟨q, hq, hq'⟩ := hg i x
  exact ⟨p * q, (natDegree_mul_le).trans (add_le_add hp hq), fun t => by simp [hp', hq']⟩

theorem sum {ι : Type} (s : Finset ι) {d : ℕ} {f : ι → (Fin n → E) → E}
    (hf : ∀ k ∈ s, IndivDeg d (f k)) : IndivDeg d fun x => ∑ k ∈ s, f k x := by
  intro i x
  have h := fun k (hk : k ∈ s) => hf k hk i x
  choose p hp hp' using h
  refine ⟨∑ k ∈ s.attach, p k.1 k.2, natDegree_sum_le_of_forall_le _ _ fun k _ => hp k.1 k.2,
    fun t => ?_⟩
  show ∑ k ∈ s, f k (Function.update x i t) = _
  rw [eval_finsetSum, ← Finset.sum_attach s]
  exact Finset.sum_congr rfl fun k _ => hp' k.1 k.2 t

theorem smul {d : ℕ} (c : E) {f : (Fin n → E) → E} (hf : IndivDeg d f) :
    IndivDeg d fun x => c * f x := by
  have h := (const (n := n) c).mul hf
  rw [zero_add] at h
  exact h

theorem mul_const {d : ℕ} (c : E) {f : (Fin n → E) → E} (hf : IndivDeg d f) :
    IndivDeg d fun x => f x * c := by
  simpa [mul_comm] using smul c hf

theorem eqPoly_left (r : Fin n → E) : IndivDeg 1 fun z => eqPoly z r := fun i x => by
  refine ⟨C (∏ j ∈ Finset.univ.erase i, (x j * r j + (1 - x j) * (1 - r j))) *
    (X * C (r i) + (1 - X) * (1 - C (r i))), ?_, fun t => ?_⟩
  · refine (natDegree_C_mul_le _ _).trans ?_
    refine (natDegree_add_le _ _).trans (max_le ?_ ?_)
    · exact (natDegree_mul_C_le _ _).trans natDegree_X_le
    · refine natDegree_mul_le.trans ?_
      have h1 : (1 - X : E[X]).natDegree ≤ 1 :=
        (natDegree_sub_le _ _).trans (max_le (by simp) natDegree_X_le)
      have h2 : (1 - C (r i) : E[X]).natDegree ≤ 0 := by
        rw [← C_1, ← C_sub]; simp
      omega
  · simp only [eqPoly, eval_mul, eval_C, eval_add, eval_sub, eval_one, eval_X]
    rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i), mul_comm]
    congr 1
    · refine Finset.prod_congr rfl fun j hj => ?_
      rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]
    · simp

theorem eqPoly_right (r : Fin n → E) : IndivDeg 1 fun z => eqPoly r z := by
  simpa [eqPoly_comm] using eqPoly_left r

theorem mle (f : Cube n → E) : IndivDeg 1 fun r => KeccakGkr.mle f r := by
  unfold KeccakGkr.mle
  exact sum _ fun x _ => by simpa [mul_comm] using smul (f x) (eqPoly_left (toPt x))

/-- Fixing the first variable keeps the degree in the others. -/
theorem cons {d : ℕ} {f : (Fin (n + 1) → E) → E} (hf : IndivDeg d f) (r : E) :
    IndivDeg d fun x : Fin n → E => f (Fin.cons r x) := fun i x => by
  obtain ⟨p, hp, hp'⟩ := hf i.succ (Fin.cons r x)
  exact ⟨p, hp, fun t => by
    show f (Fin.cons r (Function.update x i t)) = _
    rw [Fin.cons_update, hp']⟩

/-- The round polynomial of a sumcheck: summing out all but the first variable. -/
theorem round {d : ℕ} {f : (Fin (n + 1) → E) → E} (hf : IndivDeg d f) :
    ∃ q : E[X], q.natDegree ≤ d ∧
      ∀ t, ∑ x : Cube n, f (Fin.cons t (toPt x)) = q.eval t := by
  have h := sum (n := n + 1) (Finset.univ : Finset (Cube n)) (d := d)
    (f := fun x z => f (Fin.cons (z 0) (toPt x))) fun x _ => fun i z => by
      refine Fin.cases ?_ (fun j => ?_) i
      · obtain ⟨p, hp, hp'⟩ := hf 0 (Fin.cons (z 0) (toPt x))
        exact ⟨p, hp, fun t => by simp [← hp', Fin.update_cons_zero]⟩
      · exact ⟨C (f (Fin.cons (z 0) (toPt x))), by simp, fun t => by
          simp [Function.update_of_ne (Fin.succ_ne_zero j).symm]⟩
  obtain ⟨q, hq, hq'⟩ := h 0 0
  exact ⟨q, hq, fun t => by simpa using hq' t⟩

end IndivDeg

end KeccakGkr
