/-
  LeanVM.Protocol.Whir.Sound.Sumcheck

  Weighted claims about messages on a cube, multiaffine weight functions on lists of field
  elements, and the sumcheck step of WHIR's round-by-round soundness: binding the first
  coordinate of a violated claim at a challenge keeps it violated except at two challenges.
-/

module

public import LeanVM.Protocol.Verifier
public import LeanVM.Protocol.ToArkLib.Whir.Counting

/-!
# Weighted claims and the sumcheck step

The deployed verifier (`LeanVM.Protocol.Verifier.verifyWhir`, a transcription of
`verify_whir`, `python-verifier/verifier.py:1008-1086` at leanVM
`127510d14c98ade4e8a97646c44fa7f1ff5e752d`) holds its weights as functions `List E → E`,
evaluated at points of the remaining variables (`GluedClaim.weightAt`, `evaluate_basis`), and its
running claim as a value. This module gives these the meaning of Annex B
(`doc/leanvm/body/b-polynomial-commitment-scheme.tex`, Theorem `thm:rbr`):

* `bitsL p` is the cube point `p : Fin n → Bool` as a list of `0`/`1` elements of `E`, coordinate
  `0` first.
* `IsMultiaffine n Φ`: on lists of length `n`, `Φ` is affine in each coordinate. This is what the
  sumcheck needs of a weight: its extension in one variable at a time.
* `claimSum Φ g`: the inner product of the weight `Φ` with a message `g` whose variables are split
  into `m` *lane* variables (rows of an interleaved word, bound first) and `κ` *message* variables:
  `Σ_u Σ_x Φ(u ++ x)·g(u, x)`. A claim `(Φ, σ)` holds of `g` when `claimSum Φ g = σ`.
* `foldRows s g`: the message with its first lane variable bound to `s`,
  `(1 − s)·g(0, ·) + s·g(1, ·)`, the decoded form of folding an interleaved word.

The sumcheck step (`card_sumcheck_bad_le`): if `g` violates `(Φ, σ)` and the prover's round
polynomial `h = [c₀, c₁, c₂]` satisfies `h(0) + h(1) = σ`, then at most `2` challenges `s` give
`h(s) = claimSum Φ(s, ·) (foldRows s g)`, i.e. let the folded message satisfy the folded claim
`(Φ(s, ·), h(s))`. The honest round polynomial `H` of `g` is quadratic (`honest`), has
`H(0) + H(1) = claimSum Φ g` and `H(s) = claimSum Φ(s, ·) (foldRows s g)`, so it differs from `h`,
and two distinct quadratics agree at at most two points.
-/

namespace LeanVM.Protocol.Whir.Sound

open LeanVM.Parameters LeanVM.Protocol.Verifier Finset

@[expose] public section

/-! ## Cube points as lists -/

/-- A bit as an element of `E`. -/
def bitE (b : Bool) : E := if b then 1 else 0

/-- The cube point `p` as a list of `0`/`1` elements, coordinate `0` first. -/
def bitsL {n : ℕ} (p : Fin n → Bool) : List E := List.ofFn fun i ↦ bitE (p i)

@[simp] theorem length_bitsL {n : ℕ} (p : Fin n → Bool) : (bitsL p).length = n := by
  simp [bitsL]

@[simp] theorem bitsL_cons {n : ℕ} (b : Bool) (p : Fin n → Bool) :
    bitsL (Fin.cons b p : Fin (n + 1) → Bool) = bitE b :: bitsL p := by
  simp [bitsL, List.ofFn_succ]

@[simp] theorem bitsL_zero (p : Fin 0 → Bool) : bitsL p = [] := by
  simp [bitsL]

@[simp] theorem bitE_false : bitE false = 0 := rfl

@[simp] theorem bitE_true : bitE true = 1 := rfl

/-! ## Multiaffine weights -/

/-- `Φ` is affine in each coordinate on lists of length `n`. -/
def IsMultiaffine (n : ℕ) (Φ : List E → E) : Prop :=
  ∀ l : List E, l.length = n → ∀ k < n, ∀ X : E,
    Φ (l.set k X) = (1 - X) * Φ (l.set k 0) + X * Φ (l.set k 1)

namespace IsMultiaffine

variable {n : ℕ} {Φ Ψ : List E → E}

/-- Affine in the first coordinate. -/
theorem head (hΦ : IsMultiaffine (n + 1) Φ) (r : List E) (hr : r.length = n) (X : E) :
    Φ (X :: r) = (1 - X) * Φ (0 :: r) + X * Φ (1 :: r) := by
  have := hΦ (0 :: r) (by simp [hr]) 0 (Nat.succ_pos n) X
  simpa using this

/-- Binding the first coordinate keeps the weight multiaffine. -/
theorem cons (hΦ : IsMultiaffine (n + 1) Φ) (s : E) : IsMultiaffine n fun r ↦ Φ (s :: r) := by
  intro l hl k hk X
  have := hΦ (s :: l) (by simp [hl]) (k + 1) (by omega) X
  simpa using this

/-- Binding a prefix keeps the weight multiaffine. -/
theorem append {m : ℕ} (hΦ : IsMultiaffine (m + n) Φ) (pre : List E) (hpre : pre.length = m) :
    IsMultiaffine n fun r ↦ Φ (pre ++ r) := by
  intro l hl k hk X
  have h := hΦ (pre ++ l) (by simp [hl, hpre]) (pre.length + k) (by omega) X
  simpa [List.set_append_right _ _ (Nat.le_add_right _ _)] using h

/-- Sums of multiaffine weights are multiaffine. -/
theorem add (hΦ : IsMultiaffine n Φ) (hΨ : IsMultiaffine n Ψ) :
    IsMultiaffine n fun r ↦ Φ r + Ψ r := by
  intro l hl k hk X
  simp only [hΦ l hl k hk X, hΨ l hl k hk X]
  ring

/-- Scalar multiples of multiaffine weights are multiaffine. -/
theorem const_mul (hΦ : IsMultiaffine n Φ) (c : E) : IsMultiaffine n fun r ↦ c * Φ r := by
  intro l hl k hk X
  simp only [hΦ l hl k hk X]
  ring

/-- Constants are multiaffine. -/
theorem const (c : E) : IsMultiaffine n fun _ ↦ c := by
  intro l _ k _ X
  ring

/-- Zero is multiaffine. -/
theorem zero : IsMultiaffine n fun _ ↦ 0 := const 0

/-- Finite sums of multiaffine weights are multiaffine. -/
theorem sum {ι : Type*} (s : Finset ι) (Φs : ι → List E → E)
    (h : ∀ i ∈ s, IsMultiaffine n (Φs i)) : IsMultiaffine n fun r ↦ ∑ i ∈ s, Φs i r := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (zero (n := n))
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self a s)).add (ih fun i hi ↦ h i (Finset.mem_insert_of_mem hi))

end IsMultiaffine

/-! ## Claims -/

/-- The inner product of the weight `Φ` with a message on `m` lane variables and `κ` message
variables: `Σ_u Σ_x Φ(u ++ x)·g(u, x)`. -/
def claimSum {m κ : ℕ} (Φ : List E → E) (g : (Fin m → Bool) → (Fin κ → Bool) → E) : E :=
  ∑ u, ∑ x, Φ (bitsL u ++ bitsL x) * g u x

/-- The message with its first lane variable bound to `s`: `(1 − s)·g(0, ·) + s·g(1, ·)`. -/
def foldRows {m κ : ℕ} (s : E) (g : (Fin (m + 1) → Bool) → (Fin κ → Bool) → E) :
    (Fin m → Bool) → (Fin κ → Bool) → E :=
  fun u x ↦ (1 - s) * g (Fin.cons false u) x + s * g (Fin.cons true u) x

/-- A sum over the cube `Fin (m + 1) → Bool` splits on the first coordinate. -/
theorem sum_cube_succ {m : ℕ} {M : Type*} [AddCommMonoid M] (f : (Fin (m + 1) → Bool) → M) :
    ∑ u, f u = ∑ u : Fin m → Bool, (f (Fin.cons false u) + f (Fin.cons true u)) := by
  rw [← Fintype.sum_equiv (Fin.consEquiv fun _ : Fin (m + 1) ↦ Bool)
    (fun p ↦ f (Fin.cons p.1 p.2)) f (fun _ ↦ rfl), Fintype.sum_prod_type, Fintype.sum_bool,
    ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun _ _ ↦ add_comm _ _

/-! ## The honest round polynomial -/

section Honest

variable {m κ : ℕ} (Φ : List E → E) (g : (Fin (m + 1) → Bool) → (Fin κ → Bool) → E)

/-- The coefficients `H₀, H₁, H₂` of the honest round polynomial of `g` for the weight `Φ`:
`H(X) = Σ_{u,x} Φ(X, u, x)·((1 − X) g(0, u, x) + X g(1, u, x))` with `Φ` affine in `X`. -/
def honest : Fin 3 → E :=
  let a : (Fin m → Bool) → (Fin κ → Bool) → E := fun u x ↦ Φ (0 :: (bitsL u ++ bitsL x))
  let b : (Fin m → Bool) → (Fin κ → Bool) → E := fun u x ↦ Φ (1 :: (bitsL u ++ bitsL x))
  let c : (Fin m → Bool) → (Fin κ → Bool) → E := fun u x ↦ g (Fin.cons false u) x
  let d : (Fin m → Bool) → (Fin κ → Bool) → E := fun u x ↦ g (Fin.cons true u) x
  ![∑ u, ∑ x, a u x * c u x,
    ∑ u, ∑ x, (a u x * (d u x - c u x) + c u x * (b u x - a u x)),
    ∑ u, ∑ x, (b u x - a u x) * (d u x - c u x)]

/-- The honest polynomial at `s` is the folded claim: `H(s) = claimSum Φ(s, ·) (foldRows s g)`. -/
theorem honest_eval (hΦ : IsMultiaffine (m + 1 + κ) Φ) (s : E) :
    honest Φ g 0 + s * (honest Φ g 1 + s * honest Φ g 2) =
      claimSum (fun r ↦ Φ (s :: r)) (foldRows s g) := by
  simp only [honest, claimSum, foldRows, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Finset.mul_sum,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun u _ ↦ Finset.sum_congr rfl fun x _ ↦ ?_
  have hΦ' : IsMultiaffine (m + κ + 1) Φ := by rwa [show m + κ + 1 = m + 1 + κ by omega]
  rw [hΦ'.head (bitsL u ++ bitsL x) (by simp) s]
  ring

/-- The honest polynomial sums to the claim: `H(0) + H(1) = claimSum Φ g`. -/
theorem honest_sum (hΦ : IsMultiaffine (m + 1 + κ) Φ) :
    honest Φ g 0 + (honest Φ g 0 + 1 * (honest Φ g 1 + 1 * honest Φ g 2)) = claimSum Φ g := by
  have h1 := honest_eval Φ g hΦ 1
  rw [h1]
  simp only [honest, claimSum, Matrix.cons_val_zero, foldRows, sum_cube_succ, bitsL_cons,
    bitE_false, bitE_true, List.cons_append, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun u _ ↦ Finset.sum_congr rfl fun x _ ↦ ?_
  ring

end Honest

/-! ## The sumcheck step -/

/-- The prover's quadratic `[c₀, c₁, c₂]` evaluated by `polyEval` is `c₀ + s (c₁ + s c₂)`. -/
theorem polyEval_three (c₀ c₁ c₂ s : E) :
    polyEval [c₀, c₁, c₂] s = c₀ + s * (c₁ + s * c₂) := by
  simp [polyEval]
  ring

/-- **The sumcheck step.** If the message `g` violates the claim `(Φ, σ)` and the prover's
quadratic `h = [c₀, c₁, c₂]` has `h(0) + h(1) = σ`, at most two challenges `s` let the folded
message satisfy the folded claim `(Φ(s, ·), h(s))`. -/
theorem card_sumcheck_bad_le {m κ : ℕ} (Φ : List E → E) (hΦ : IsMultiaffine (m + 1 + κ) Φ)
    (g : (Fin (m + 1) → Bool) → (Fin κ → Bool) → E) (σ c₀ c₁ c₂ : E)
    (hσ : polyEval [c₀, c₁, c₂] 0 + polyEval [c₀, c₁, c₂] 1 = σ) (hviol : claimSum Φ g ≠ σ) :
    (univ.filter fun s : E ↦
        polyEval [c₀, c₁, c₂] s = claimSum (fun r ↦ Φ (s :: r)) (foldRows s g)).card ≤ 2 := by
  have hne : ![c₀, c₁, c₂] ≠ honest Φ g := by
    intro heq
    apply hviol
    rw [← honest_sum Φ g hΦ, ← hσ, polyEval_three, polyEval_three, ← heq]
    simp
  refine le_of_eq_of_le ?_ (card_quadratic_eq_le _ _ hne)
  congr 1
  ext s
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, polyEval_three, ← honest_eval Φ g hΦ]
  simp

end
end LeanVM.Protocol.Whir.Sound
