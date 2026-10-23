/-
  LeanVM.Protocol.ToArkLib.Flock.FrobeniusMap

  The staged additive map of Frobenius-map ring switching: a composition of stages
  `a ↦ a + f · a ^ 2 ^ s`, its expansion as a sum of Frobenius powers, its additivity, and the
  stage-by-stage bound that one challenge cancels a nonzero family at one value at most.
  Candidate for ArkLib.
-/

module

public import Mathlib.Algebra.CharP.Lemmas
public import Mathlib.Algebra.CharP.Reduced
public import Mathlib.Algebra.Field.Basic
public import Mathlib.Data.Fintype.Card

/-!
# The staged Frobenius map

In a commutative ring of characteristic two, `a ↦ a + f · a ^ 2 ^ s` is additive, and so is any
composition of such stages. `frobMap st a` applies the stages of the list `st`, a stage being a
shift `s` and a coefficient `f`, in order. Ring switching from `GF(2)` to a field `E` draws the
coefficients as challenges: the composed map is a random `GF(2)`-linear map cheap to apply.

* `frobMap_eq_sum`: the map is the Frobenius sum `Σ_{(c, e)} c · a ^ 2 ^ e` over the terms
  `frobTerms st`, two terms per term of the later stages; with `m` stages there are `2 ^ m`.
* `frobMapHom`: the map as an additive homomorphism, so it commutes with sums and differences.
* `frobPair_stage`, `card_stage_zero_le_one`: for weights `w` and a family `b`, write
  `π_k(b) = Σ_i w_i · b_i ^ 2 ^ k`. One stage with shift `M` sends `π_k` to
  `π_k + f ^ 2 ^ k · π_{M + k}`, so a family with some `π_k ≠ 0`, `k < 2M`, keeps some
  `π_k ≠ 0`, `k < M`, for every coefficient `f` but at most one: `a + f ^ 2 ^ k · b = 0` with
  `(a, b) ≠ (0, 0)` has at most one root, the Frobenius being injective.

Nothing here transcribes a source.
-/

namespace LeanVM.Protocol

@[expose] public section

variable {R : Type*} [CommRing R]

/-! ## The map and its terms -/

/-- The staged map: each stage `(s, f)` sends `a` to `a + f · a ^ 2 ^ s`, in order. -/
def frobMap : List (ℕ × R) → R → R
  | [], a => a
  | (s, f) :: st, a => frobMap st (a + f * a ^ 2 ^ s)

/-- The terms `(c, e)` of the staged map as a sum of Frobenius powers `c · a ^ 2 ^ e`. -/
def frobTerms : List (ℕ × R) → List (R × ℕ)
  | [] => [(1, 0)]
  | (s, f) :: st => (frobTerms st).flatMap fun t ↦ [(t.1, t.2), (t.1 * f ^ 2 ^ t.2, s + t.2)]

variable [CharP R 2]

/-- The staged map is the sum of its terms: `frobMap st a = Σ_{(c, e)} c · a ^ 2 ^ e`. -/
theorem frobMap_eq_sum (st : List (ℕ × R)) (a : R) :
    frobMap st a = ((frobTerms st).map fun t ↦ t.1 * a ^ 2 ^ t.2).sum := by
  induction st generalizing a with
  | nil => simp [frobMap, frobTerms]
  | cons p st ih =>
    obtain ⟨s, f⟩ := p
    rw [frobMap, ih, frobTerms]
    generalize frobTerms st = L
    induction L with
    | nil => simp
    | cons t L ihL =>
      simp only [List.flatMap_cons, List.map_append, List.sum_append, List.map_cons,
        List.sum_cons, List.map_nil, List.sum_nil, add_zero, ihL]
      rw [add_pow_char_pow, mul_pow, ← pow_mul, ← pow_add]
      ring

omit [CharP R 2] in
/-- Stages in sequence: the later list applies after the earlier. -/
theorem frobMap_append (st₁ st₂ : List (ℕ × R)) (a : R) :
    frobMap (st₁ ++ st₂) a = frobMap st₂ (frobMap st₁ a) := by
  induction st₁ generalizing a with
  | nil => rfl
  | cons p st ih =>
    obtain ⟨s, f⟩ := p
    exact ih _


/-- The staged map is additive. -/
theorem frobMap_add (st : List (ℕ × R)) (a b : R) :
    frobMap st (a + b) = frobMap st a + frobMap st b := by
  induction st generalizing a b with
  | nil => rfl
  | cons p st ih =>
    obtain ⟨s, f⟩ := p
    simp only [frobMap]
    rw [← ih, add_pow_char_pow]
    congr 1
    ring

omit [CharP R 2] in
/-- The staged map sends `0` to `0`. -/
theorem frobMap_zero (st : List (ℕ × R)) : frobMap st 0 = 0 := by
  induction st with
  | nil => rfl
  | cons p st ih =>
    obtain ⟨s, f⟩ := p
    simp only [frobMap]
    rw [zero_pow (pow_ne_zero _ two_ne_zero), mul_zero, add_zero, ih]

/-- The staged map as an additive homomorphism. -/
def frobMapHom (st : List (ℕ × R)) : R →+ R where
  toFun := frobMap st
  map_zero' := frobMap_zero st
  map_add' := frobMap_add st

/-! ## One stage on a family -/

/-- `π_k(b) = Σ_i w_i · b_i ^ 2 ^ k`. -/
def frobPair {ι : Type*} (s : Finset ι) (w b : ι → R) (k : ℕ) : R :=
  ∑ i ∈ s, w i * b i ^ 2 ^ k

/-- One stage with shift `M` and coefficient `f` sends `π_k` to `π_k + f ^ 2 ^ k · π_{M + k}`. -/
theorem frobPair_stage {ι : Type*} (s : Finset ι) (w b : ι → R) (M : ℕ) (f : R) (k : ℕ) :
    frobPair s w (fun i ↦ b i + f * b i ^ 2 ^ M) k =
      frobPair s w b k + f ^ 2 ^ k * frobPair s w b (M + k) := by
  simp only [frobPair, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [add_pow_char_pow, mul_pow, ← pow_mul, ← pow_add]
  ring

/-- `a + f ^ 2 ^ k · b = 0` with `(a, b) ≠ (0, 0)` has one root `f` at most, in a field of
characteristic two. -/
theorem card_frob_root_le_one {F : Type*} [Field F] [CharP F 2] [Fintype F] [DecidableEq F]
    (k : ℕ) {a b : F} (hab : a ≠ 0 ∨ b ≠ 0) :
    (Finset.univ.filter fun f : F ↦ a + f ^ 2 ^ k * b = 0).card ≤ 1 := by
  refine Finset.card_le_one.mpr fun f₁ h₁ f₂ h₂ ↦ ?_
  rw [Finset.mem_filter] at h₁ h₂
  have hb : b ≠ 0 := by
    rintro rfl
    simp only [mul_zero, add_zero] at h₁
    exact hab.elim (· h₁.2) (· rfl)
  have heq : f₁ ^ 2 ^ k = f₂ ^ 2 ^ k :=
    mul_right_cancel₀ hb (add_left_cancel (h₁.2.trans h₂.2.symm))
  exact iterateFrobenius_inj F 2 k heq

/-- **One bad coefficient at most.** If some `π_k`, `k < 2M`, of the family is nonzero, then after
one stage with shift `M` every `π_k`, `k < M`, vanishes for one coefficient at most. -/
theorem card_stage_zero_le_one {F : Type*} [Field F] [CharP F 2] [Fintype F] [DecidableEq F]
    {ι : Type*} (s : Finset ι) (w b : ι → F) (M : ℕ) (h : ∃ k < 2 * M, frobPair s w b k ≠ 0) :
    (Finset.univ.filter fun f : F ↦
      ∀ k < M, frobPair s w (fun i ↦ b i + f * b i ^ 2 ^ M) k = 0).card ≤ 1 := by
  obtain ⟨k₀, hk₀, hne⟩ := h
  -- The index below `M` whose pair of values is nonzero.
  obtain ⟨k, hk, hab⟩ : ∃ k < M, frobPair s w b k ≠ 0 ∨ frobPair s w b (M + k) ≠ 0 := by
    by_cases hlt : k₀ < M
    · exact ⟨k₀, hlt, Or.inl hne⟩
    · refine ⟨k₀ - M, by omega, Or.inr ?_⟩
      rwa [show M + (k₀ - M) = k₀ by omega]
  refine (Finset.card_le_card fun f hf ↦ ?_).trans (card_frob_root_le_one k hab)
  rw [Finset.mem_filter] at hf ⊢
  refine ⟨Finset.mem_univ _, ?_⟩
  rw [← frobPair_stage]
  exact hf.2 k hk

end
end LeanVM.Protocol
