/-
  LeanVM.Protocol.Relation.Link.GroupPoly

  Functions of the drawn challenges that are polynomials of bounded total degree, and their zeros
  counted (Schwartz-Zippel), for the link's drawn group.
-/

module

public import LeanVM.Protocol.Link.Sample
public import LeanVM.Protocol.Hotwire.Mirror
public import LeanVM.Facts.Hotwire
public import LeanVM.Protocol.Relation.Stack

/-!
# Polynomial functions of the challenges

`PolyFn n D f`: `f : (Fin n → E) → E` is a polynomial of total degree at most `D`, with its closure
under the ring's operations. `PolyFn.card_zero_le`: such an `f` nonzero somewhere vanishes at no
more than `D·|E|^(n−1)` of the `|E|^n` points. `polyFn_eqAt`: `eq(pt, j)` at a point whose
coordinates are of degree at most one is of degree at most its length.

Also the Boolean points of the cube (`boolL`), where `rowMle` and `eqAt` select one row.
-/

namespace LeanVM.Protocol.Relation

open LeanVM.Parameters LeanVM.Protocol.Hotwire Finset MvPolynomial

@[expose] public section

/-- `f` is a polynomial of total degree at most `D` in its `n` arguments. -/
def PolyFn (n D : ℕ) (f : (Fin n → E) → E) : Prop :=
  ∃ P : MvPolynomial (Fin n) E, P.totalDegree ≤ D ∧ ∀ x, eval x P = f x

namespace PolyFn

variable {n : ℕ}

theorem const (a : E) : PolyFn n 0 fun _ ↦ a := ⟨C a, by simp, fun _ ↦ by simp⟩

theorem var (i : Fin n) : PolyFn n 1 fun x ↦ x i :=
  ⟨X i, (totalDegree_X i).le, fun _ ↦ by simp⟩

theorem mono {f : (Fin n → E) → E} {D D' : ℕ} (h : PolyFn n D f) (hD : D ≤ D') : PolyFn n D' f := by
  obtain ⟨P, hP, hv⟩ := h
  exact ⟨P, hP.trans hD, hv⟩

theorem congr {f g : (Fin n → E) → E} {D : ℕ} (h : PolyFn n D f) (hfg : ∀ x, f x = g x) :
    PolyFn n D g := by
  obtain ⟨P, hP, hv⟩ := h
  exact ⟨P, hP, fun x ↦ (hv x).trans (hfg x)⟩

theorem add {f g : (Fin n → E) → E} {D e : ℕ} (hf : PolyFn n D f) (hg : PolyFn n e g) :
    PolyFn n (max D e) fun x ↦ f x + g x := by
  obtain ⟨P, hP, hPv⟩ := hf
  obtain ⟨Q, hQ, hQv⟩ := hg
  exact ⟨P + Q, (totalDegree_add P Q).trans (max_le_max hP hQ), fun x ↦ by simp [hPv, hQv]⟩

theorem sub {f g : (Fin n → E) → E} {D e : ℕ} (hf : PolyFn n D f) (hg : PolyFn n e g) :
    PolyFn n (max D e) fun x ↦ f x - g x := by
  obtain ⟨P, hP, hPv⟩ := hf
  obtain ⟨Q, hQ, hQv⟩ := hg
  exact ⟨P - Q, (totalDegree_sub P Q).trans (max_le_max hP hQ), fun x ↦ by simp [hPv, hQv]⟩

theorem mul {f g : (Fin n → E) → E} {D e : ℕ} (hf : PolyFn n D f) (hg : PolyFn n e g) :
    PolyFn n (D + e) fun x ↦ f x * g x := by
  obtain ⟨P, hP, hPv⟩ := hf
  obtain ⟨Q, hQ, hQv⟩ := hg
  exact ⟨P * Q, (totalDegree_mul P Q).trans (add_le_add hP hQ), fun x ↦ by simp [hPv, hQv]⟩

theorem add_le {f g : (Fin n → E) → E} {D : ℕ} (hf : PolyFn n D f) (hg : PolyFn n D g) :
    PolyFn n D fun x ↦ f x + g x :=
  (hf.add hg).mono (max_le le_rfl le_rfl)

theorem mul_le {f g : (Fin n → E) → E} {D e N : ℕ} (hf : PolyFn n D f) (hg : PolyFn n e g)
    (h : D + e ≤ N) : PolyFn n N fun x ↦ f x * g x :=
  (hf.mul hg).mono h

theorem const_mul (a : E) {f : (Fin n → E) → E} {D : ℕ} (hf : PolyFn n D f) :
    PolyFn n D fun x ↦ a * f x :=
  ((const a).mul hf).mono (by omega)

theorem finsetSum {ι : Type} (s : Finset ι) {f : ι → (Fin n → E) → E} {D : ℕ}
    (h : ∀ i ∈ s, PolyFn n D (f i)) : PolyFn n D fun x ↦ ∑ i ∈ s, f i x := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ((const 0).mono (Nat.zero_le _)).congr fun x ↦ by simp
  | insert a s ha ih =>
    refine ((h a (mem_insert_self a s)).add_le (ih fun i hi ↦ h i (mem_insert_of_mem hi))).congr
      fun x ↦ ?_
    rw [sum_insert ha]

/-- **Schwartz-Zippel**: a polynomial function nonzero somewhere vanishes at no more than
`D·|E|^(n−1)` of the points. -/
theorem card_zero_le {f : (Fin n → E) → E} {D : ℕ} (h : PolyFn n D f) {x0 : Fin n → E}
    (hx0 : f x0 ≠ 0) : (univ.filter fun x ↦ f x = 0).card ≤ D * Fintype.card E ^ (n - 1) := by
  obtain ⟨P, hP, hv⟩ := h
  have hP0 : P ≠ 0 := by
    rintro rfl
    exact hx0 (by rw [← hv]; simp)
  have hc := Protocol.Link.card_eval_comp_le (σ := Fin n) id Function.injective_id P hP0 hP
  refine le_of_eq_of_le (congrArg card (filter_congr fun x _ ↦ ?_)) hc
  rw [← hv]
  rfl

end PolyFn

/-- **`eq(pt, j)` is of degree at most `|pt|`** when each coordinate is of degree at most one. -/
theorem polyFn_eqAt {n : ℕ} : ∀ (L : ℕ) (pt : (Fin n → E) → List E), (∀ x, (pt x).length = L) →
    (∀ k < L, PolyFn n 1 fun x ↦ (pt x).getD k 0) → ∀ j, PolyFn n L fun x ↦ eqAt (pt x) j
  | 0, pt, hl, _, j => (PolyFn.const 1).congr fun x ↦ by
      rw [List.eq_nil_of_length_eq_zero (hl x)]; rfl
  | L + 1, pt, hl, hc, j => by
    have hcons : ∀ x, pt x = (pt x).getD 0 0 :: (pt x).tail := fun x ↦ by
      obtain ⟨a, l, h⟩ := List.exists_cons_of_length_eq_add_one (hl x)
      rw [h]; rfl
    have ht := polyFn_eqAt L (fun x ↦ (pt x).tail) (fun x ↦ by simp [hl x])
      (fun k hk ↦ (hc (k + 1) (by omega)).congr fun x ↦ by
        rw [hcons x]; simp) (j / 2)
    have h0 := hc 0 (by omega)
    have hhead : PolyFn n 1 fun x ↦ if j % 2 = 1 then (pt x).getD 0 0 else 1 - (pt x).getD 0 0 := by
      split_ifs
      · exact h0
      · exact ((PolyFn.const 1).sub h0).mono (by omega)
    refine (hhead.mul_le ht (by omega)).congr fun x ↦ ?_
    conv_rhs => rw [hcons x]
    rw [eqAt_cons]

/-! ## Boolean points -/

/-- The Boolean point of `j` over `n` coordinates, the first coordinate the lowest bit. -/
def boolL (n j : ℕ) : List E := List.ofFn (boolPt (R := E) n j)

theorem length_boolL (n j : ℕ) : (boolL n j).length = n := List.length_ofFn

theorem eqAt_boolL {n j v : ℕ} (hj : j < 2 ^ n) (hv : v < 2 ^ n) :
    eqAt (boolL n v) j = if j = v then 1 else 0 :=
  eqAt_ofFn_boolPt n hj hv

/-- `rowMle` is `mle`. -/
theorem rowMle_eq_mle (pt : List E) (f : ℕ → E) : rowMle pt f = mle pt f := by
  unfold rowMle
  rw [multilinearEval_eq_mle pt _ (by simp)]
  refine sum_congr rfl fun j hj ↦ ?_
  have hj' := mem_range.mp hj
  simp [hj']

/-- **`rowMle` at a Boolean point** is the row. -/
theorem rowMle_boolL {n v : ℕ} (hv : v < 2 ^ n) (f : ℕ → E) : rowMle (boolL n v) f = f v := by
  rw [rowMle_eq_mle, mle, length_boolL, sum_eq_single v]
  · simp [eqAt_boolL hv hv]
  · intro j hj hne
    simp [eqAt_boolL (mem_range.mp hj) hv, hne]
  · intro h
    exact absurd (mem_range.mpr hv) h

end

end LeanVM.Protocol.Relation
