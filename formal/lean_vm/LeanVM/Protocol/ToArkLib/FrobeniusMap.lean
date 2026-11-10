/-
  LeanVM.Protocol.ToArkLib.FrobeniusMap

  The two-stage additive map of Frobenius-map ring switching: an inner stage
  `Ψ(a) = Σ_b g_b · a^(2^b)` and an outer stage `Φ(a) = Σ_p f_p · Ψ(a)^(2^(s·p))`, its expansion
  as a sum of Frobenius powers, its additivity, and the count of the challenges `(f, g)` at which it
  cancels a family whose Frobenius pairings are not all zero. Candidate for ArkLib.
-/

module

public import Mathlib.Algebra.CharP.Lemmas
public import Mathlib.Algebra.CharP.Reduced
public import Mathlib.Algebra.Field.Basic
public import Mathlib.Data.Fintype.BigOperators
public import ArkLib.Data.MvPolynomial.SchwartzZippelCounting

/-!
# The two-stage Frobenius map

In a commutative ring of characteristic two, `a ↦ a^(2^k)` is additive, so for coefficients
`g : Fin m → R` and `f : Fin n → R` and a shift `s`, the maps

```text
Ψ(a) = Σ_{b < m} g_b · a^(2^b)                         frobPsi
Φ(a) = Σ_{p < n} f_p · Ψ(a)^(2^(s·p))                  frobPhi
```

are additive (`frobPhiHom`), and `Φ` is the Frobenius sum
`Φ(a) = Σ_{p, b} f_p g_b^(2^(s·p)) · a^(2^(s·p + b))` (`frobPhi_eq_sum`). Ring switching draws
`f` and `g` as challenges: with `s = m` the exponents `s·p + b` run once over `[0, n·m)`.

**Soundness, by stage.** For weights `w` and a family `δ`, write `π_k(δ) = Σ_i w_i · δ_i^(2^k)`
(`frobPair`). Then `Σ_i w_i Φ(δ_i) = Σ_p f_p · M_p(g)` with
`M_p(g) = Σ_b g_b^(2^(s·p)) · π_{s·p + b}(δ)` (`sum_frobPhi`). Over a finite field `F` of
characteristic two:

* if `π_{s·p + b} ≠ 0` for some `p, b`, then `M_p(g)` is a nonzero linear form in
  `(g_b^(2^(s·p)))_b`, and the Frobenius permutes `F`, so it vanishes at `|F|^(m-1)` of the `g` at
  most (`card_frob_linear_zero_le`);
* when `M(g) ≠ 0`, `Σ_p f_p M_p(g)` is a nonzero linear form in `f`, which vanishes at
  `|F|^(n-1)` of the `f` at most (`card_linear_zero_le`).

So `Σ_i w_i Φ(δ_i) = 0` at no more than `2·|F|^(n+m-1)` of the `|F|^(n+m)` challenges `(f, g)`
(`card_frobPhi_zero_le`), an error `2/|F|`, though the `g_b` enter `Φ` with degree up to
`2^(s·(n-1))`: each stage is linear in its own challenges. Nothing here transcribes a source.
-/

namespace LeanVM.Protocol.Ring

open Finset

@[expose] public section

variable {R : Type*} [CommRing R]

/-! ## The map -/

/-- The inner stage, `Ψ(a) = Σ_{b < m} g_b · a^(2^b)`. -/
def frobPsi {m : ℕ} (g : Fin m → R) (a : R) : R := ∑ b : Fin m, g b * a ^ 2 ^ (b : ℕ)

/-- The two-stage map, `Φ(a) = Σ_{p < n} f_p · Ψ(a)^(2^(s·p))`. -/
def frobPhi (s : ℕ) {n m : ℕ} (f : Fin n → R) (g : Fin m → R) (a : R) : R :=
  ∑ p : Fin n, f p * frobPsi g a ^ 2 ^ (s * p)

/-- The Frobenius pairing `π_k(δ) = Σ_{i ∈ S} w_i · δ_i^(2^k)`. -/
def frobPair {ι : Type*} (S : Finset ι) (w δ : ι → R) (k : ℕ) : R :=
  ∑ i ∈ S, w i * δ i ^ 2 ^ k

variable [CharP R 2]

/-- The inner stage is additive. -/
theorem frobPsi_add {m : ℕ} (g : Fin m → R) (a b : R) :
    frobPsi g (a + b) = frobPsi g a + frobPsi g b := by
  simp only [frobPsi, add_pow_char_pow, mul_add, Finset.sum_add_distrib]

/-- The two-stage map is additive. -/
theorem frobPhi_add (s : ℕ) {n m : ℕ} (f : Fin n → R) (g : Fin m → R) (a b : R) :
    frobPhi s f g (a + b) = frobPhi s f g a + frobPhi s f g b := by
  simp only [frobPhi, frobPsi_add, add_pow_char_pow, mul_add, Finset.sum_add_distrib]

/-- The two-stage map sends `0` to `0`. -/
theorem frobPhi_zero (s : ℕ) {n m : ℕ} (f : Fin n → R) (g : Fin m → R) :
    frobPhi s f g 0 = 0 := by
  have h := frobPhi_add s f g 0 0
  rw [add_zero] at h
  exact left_eq_add.mp h

/-- The two-stage map as an additive homomorphism. -/
def frobPhiHom (s : ℕ) {n m : ℕ} (f : Fin n → R) (g : Fin m → R) : R →+ R where
  toFun := frobPhi s f g
  map_zero' := frobPhi_zero s f g
  map_add' := frobPhi_add s f g

/-- The two-stage map sends differences to differences. -/
theorem frobPhi_sub (s : ℕ) {n m : ℕ} (f : Fin n → R) (g : Fin m → R) (a b : R) :
    frobPhi s f g (a - b) = frobPhi s f g a - frobPhi s f g b :=
  map_sub (frobPhiHom s f g) a b

/-- The two-stage map commutes with finite sums. -/
theorem frobPhi_sum (s : ℕ) {n m : ℕ} (f : Fin n → R) (g : Fin m → R) {ι : Type*}
    (S : Finset ι) (a : ι → R) :
    frobPhi s f g (∑ i ∈ S, a i) = ∑ i ∈ S, frobPhi s f g (a i) :=
  map_sum (frobPhiHom s f g) a S

/-- A Frobenius power of the inner stage: `Ψ(a)^(2^t) = Σ_b g_b^(2^t) · a^(2^(t + b))`. -/
theorem frobPsi_pow {m : ℕ} (g : Fin m → R) (a : R) (t : ℕ) :
    frobPsi g a ^ 2 ^ t = ∑ b : Fin m, g b ^ 2 ^ t * a ^ 2 ^ (t + (b : ℕ)) := by
  rw [frobPsi, sum_pow_char_pow]
  refine Finset.sum_congr rfl fun b _ ↦ ?_
  rw [mul_pow, ← pow_mul, ← pow_add, Nat.add_comm (b : ℕ) t]

/-- **The Frobenius sum**: `Φ(a) = Σ_{p, b} f_p g_b^(2^(s·p)) · a^(2^(s·p + b))`. -/
theorem frobPhi_eq_sum (s : ℕ) {n m : ℕ} (f : Fin n → R) (g : Fin m → R) (a : R) :
    frobPhi s f g a =
      ∑ p : Fin n, ∑ b : Fin m, f p * g b ^ 2 ^ (s * p) * a ^ 2 ^ (s * p + (b : ℕ)) := by
  simp only [frobPhi, frobPsi_pow, Finset.mul_sum, mul_assoc]

/-- **The map through a family**: `Σ_i w_i Φ(δ_i) = Σ_p f_p Σ_b g_b^(2^(s·p)) π_{s·p + b}(δ)`. -/
theorem sum_frobPhi (s : ℕ) {n m : ℕ} (f : Fin n → R) (g : Fin m → R) {ι : Type*}
    (S : Finset ι) (w δ : ι → R) :
    ∑ i ∈ S, w i * frobPhi s f g (δ i) =
      ∑ p : Fin n, f p * ∑ b : Fin m, g b ^ 2 ^ (s * p) * frobPair S w δ (s * p + b) := by
  simp only [frobPhi_eq_sum, frobPair, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun p _ ↦ ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ ↦ ?_
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  ring

/-! ## Counting the bad challenges -/

section Count

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- **A nonzero linear form vanishes on `|F|^(m-1)` points at most.** -/
theorem card_linear_zero_le {m : ℕ} {c : Fin m → F} (hc : c ≠ 0) :
    #{h : Fin m → F | ∑ b, h b * c b = 0} ≤ Fintype.card F ^ (m - 1) := by
  classical
  obtain ⟨b₀, hb₀⟩ := Function.ne_iff.mp hc
  let P : MvPolynomial (Fin m) F := ∑ b, MvPolynomial.X b * MvPolynomial.C (c b)
  have hev : ∀ h : Fin m → F, MvPolynomial.eval h P = ∑ b, h b * c b := fun h ↦ by
    simp [P]
  have hP : P ≠ 0 := by
    intro h0
    have h1 := hev (Pi.single b₀ 1)
    rw [h0, map_zero] at h1
    have h2 : ∑ b, (Pi.single b₀ (1 : F) : Fin m → F) b * c b = c b₀ := by
      rw [Finset.sum_eq_single b₀ (fun b _ hb ↦ by simp [hb])
        (fun h ↦ absurd (Finset.mem_univ _) h)]
      simp
    exact hb₀ (by rw [← h2, ← h1]; rfl)
  have hdeg : P.totalDegree ≤ 1 := by
    refine (MvPolynomial.totalDegree_finsetSum _ _).trans (Finset.sup_le fun b _ ↦ ?_)
    refine (MvPolynomial.totalDegree_mul _ _).trans ?_
    rw [MvPolynomial.totalDegree_C, add_zero]
    exact (MvPolynomial.totalDegree_X b).le
  have h := MvPolynomial.card_zeros_le_of_totalDegree_le_fin P hP hdeg
  simp only [hev, one_mul] at h
  exact h

/-- **Twisted by a Frobenius power**: `Σ_b g_b^(2^t) · c_b`, `c ≠ 0`, vanishes on `|F|^(m-1)` of
the `g` at most, the Frobenius permuting `F`. -/
theorem card_frob_linear_zero_le [CharP F 2] {m : ℕ} (t : ℕ) {c : Fin m → F} (hc : c ≠ 0) :
    #{g : Fin m → F | ∑ b, g b ^ 2 ^ t * c b = 0} ≤ Fintype.card F ^ (m - 1) := by
  refine (Finset.card_le_card_of_injOn (fun g b ↦ g b ^ 2 ^ t) ?_ ?_).trans
    (card_linear_zero_le hc)
  · intro g hg
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hg ⊢
    exact hg
  · intro g₁ _ g₂ _ h
    funext b
    exact iterateFrobenius_inj F 2 t (congrFun h b)

/-- The challenges of a product split by the second coordinate. -/
private theorem card_filter_prod {α β : Type*} [Fintype α] [Fintype β] (P : α → β → Prop)
    [∀ a b, Decidable (P a b)] :
    #{x : α × β | P x.1 x.2} = ∑ b : β, #{a : α | P a b} := by
  rw [Finset.card_filter, Fintype.sum_prod_type_right]
  refine Finset.sum_congr rfl fun b _ ↦ ?_
  rw [Finset.card_filter]

/-- **The two-stage map cancels a family at few challenges.** If some pairing `π_{s·p + b}(δ)`,
`p < n`, `b < m`, is nonzero, then `Σ_i w_i Φ(δ_i) = 0` at no more than `2·|F|^(n+m-1)` of the
challenges `(f, g)`. -/
theorem card_frobPhi_zero_le [CharP F 2] {ι : Type*} (S : Finset ι) (w δ : ι → F) (s : ℕ)
    {n m : ℕ} (h : ∃ p : Fin n, ∃ b : Fin m, frobPair S w δ (s * p + b) ≠ 0) :
    #{fg : (Fin n → F) × (Fin m → F) | ∑ i ∈ S, w i * frobPhi s fg.1 fg.2 (δ i) = 0} ≤
      2 * Fintype.card F ^ (n + m - 1) := by
  obtain ⟨p₀, b₀, hne⟩ := h
  let M : (Fin m → F) → Fin n → F := fun g p ↦
    ∑ b : Fin m, g b ^ 2 ^ (s * p) * frobPair S w δ (s * p + b)
  have hn : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr fun h ↦ by subst h; exact p₀.elim0
  have hm : 1 ≤ m := Nat.one_le_iff_ne_zero.mpr fun h ↦ by subst h; exact b₀.elim0
  -- The outer stage at a fixed `g`.
  have hf : ∀ g : Fin m → F, #{f : Fin n → F | ∑ p, f p * M g p = 0} ≤
      Fintype.card F ^ (n - 1) + (if M g p₀ = 0 then Fintype.card F ^ n else 0) := by
    intro g
    by_cases h0 : M g p₀ = 0
    · simp only [h0, ↓reduceIte]
      refine (Finset.card_le_univ _).trans ?_
      rw [Fintype.card_fun, Fintype.card_fin]
      exact Nat.le_add_left _ _
    · simp only [h0, ↓reduceIte, add_zero]
      exact card_linear_zero_le fun hM ↦ h0 (congrFun hM p₀)
  -- The inner stage at `p₀`.
  have hg : #{g : Fin m → F | M g p₀ = 0} ≤ Fintype.card F ^ (m - 1) :=
    card_frob_linear_zero_le (s * p₀) fun hc ↦ hne (congrFun hc b₀)
  have hset : (Finset.univ.filter fun fg : (Fin n → F) × (Fin m → F) ↦
      ∑ i ∈ S, w i * frobPhi s fg.1 fg.2 (δ i) = 0) =
      Finset.univ.filter fun fg : (Fin n → F) × (Fin m → F) ↦ ∑ p, fg.1 p * M fg.2 p = 0 :=
    Finset.filter_congr fun fg _ ↦ by rw [sum_frobPhi s fg.1 fg.2 S w δ]
  have hsplit : #{fg : (Fin n → F) × (Fin m → F) | ∑ p, fg.1 p * M fg.2 p = 0} =
      ∑ g : Fin m → F, #{f : Fin n → F | ∑ p, f p * M g p = 0} :=
    card_filter_prod (fun (f : Fin n → F) (g : Fin m → F) ↦ ∑ p, f p * M g p = 0)
  have hite : ∑ g : Fin m → F, (if M g p₀ = 0 then Fintype.card F ^ n else 0) =
      #{g : Fin m → F | M g p₀ = 0} * Fintype.card F ^ n := by
    rw [← Finset.sum_filter, Finset.sum_const, smul_eq_mul]
  have hconst : ∑ _g : Fin m → F, Fintype.card F ^ (n - 1) =
      Fintype.card F ^ m * Fintype.card F ^ (n - 1) := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin, smul_eq_mul]
  rw [hset, hsplit]
  refine (Finset.sum_le_sum fun g _ ↦ hf g).trans ?_
  rw [Finset.sum_add_distrib, hite, hconst]
  calc Fintype.card F ^ m * Fintype.card F ^ (n - 1) + #{g : Fin m → F | M g p₀ = 0} *
        Fintype.card F ^ n
      ≤ Fintype.card F ^ m * Fintype.card F ^ (n - 1) + Fintype.card F ^ (m - 1) *
        Fintype.card F ^ n := Nat.add_le_add_left (Nat.mul_le_mul_right _ hg) _
    _ = 2 * Fintype.card F ^ (n + m - 1) := by
        rw [← pow_add, ← pow_add, two_mul]
        congr 2 <;> omega

end Count

end
end LeanVM.Protocol.Ring
