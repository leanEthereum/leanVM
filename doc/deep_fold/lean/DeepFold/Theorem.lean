/-
The DEEP fold theorem, single lane: Theorem 4.9 of the paper and, with Lemma 4.7, the first half
of the proof of Lemma 4.10(2).
-/
import DeepFold.Class
import DeepFold.Agreement
import DeepFold.Counting

open Polynomial Finset
open scoped Classical

namespace DeepFold

variable {K : Type*} [Field K] [Fintype K]

local notation "φ" => algebraMap K[X] (RatFunc K)

/-- Three candidates are dependent: if their challenges are pairwise different, then
`Delta = 0`. So "not dependent" is "pairwise different challenges and `Delta ≠ 0`", the triples
that `N(z)` counts in Definition 4.8 of the paper. -/
def Dep (e₁ e₂ e₃ : Cand K) : Prop :=
  (e₁.1 ≠ e₂.1 ∧ e₁.1 ≠ e₃.1 ∧ e₂.1 ≠ e₃.1) → Delta e₁ e₂ e₃ = 0

/-- The exceptional set of the single-lane DEEP fold: the vectors `z` of `s` points of `K` for
which at least `B` ordered triples of `T` have pairwise different challenges, `Delta ≠ 0` and
`Delta(z_i) = 0` for all `i`. -/
noncomputable def ExcD (T : Finset (Cand K)) (s B : ℕ) : Finset (Fin s → K) :=
  Exc T Dep (fun e₁ e₂ e₃ z => (Delta e₁ e₂ e₃).eval z = 0) s B

theorem delta_roots_le {T : Finset (Cand K)} {d : ℕ} (hT : ∀ e ∈ T, e.2.natDegree ≤ d) :
    ∀ t₁ ∈ T, ∀ t₂ ∈ T, ∀ t₃ ∈ T, ¬ Dep t₁ t₂ t₃ →
      (univ.filter (fun z : K => (Delta t₁ t₂ t₃).eval z = 0)).card ≤ d + 1 :=
  fun t₁ h₁ t₂ h₂ t₃ h₃ hnd =>
    (card_roots_le (Classical.not_imp.mp hnd).2).trans
      (Delta_natDegree_le (hT t₁ h₁) (hT t₂ h₂) (hT t₃ h₃))

/-- Theorem 4.9(1) of the paper, single lane, counting form:
`|Exc| · B ≤ |T|^3 (d + 1)^s`. -/
theorem card_ExcD_mul_le {T : Finset (Cand K)} {d : ℕ} (hT : ∀ e ∈ T, e.2.natDegree ≤ d)
    (s B : ℕ) : (ExcD T s B).card * B ≤ T.card ^ 3 * (d + 1) ^ s :=
  card_Exc_mul_le T _ _ (delta_roots_le hT) s B

/-- Theorem 4.9(1) of the paper, single lane, as a probability over `s` independent uniform
points: at most `|T|^3 ε^s / B` with `ε = (d + 1) / q`. In the paper `B = K₀ (K₀ - 1) (K₀ - M)`. -/
theorem density_ExcD_le {T : Finset (Cand K)} {d : ℕ} (hT : ∀ e ∈ T, e.2.natDegree ≤ d)
    (s : ℕ) {B : ℕ} (hB : 0 < B) :
    ((ExcD T s B).card : ℚ) / (Fintype.card (Fin s → K) : ℚ) ≤
      (T.card : ℚ) ^ 3 * (((d + 1 : ℕ) : ℚ) / Fintype.card K) ^ s / B :=
  density_Exc_le T _ _ (delta_roots_le hT) s hB

omit [Field K] in
/-- `|T| ≤ Λ q^2` when every challenge has at most `Λ` candidates. -/
theorem card_T_le {α : Type*} (T : Finset α) (ch : α → K × K) (Λ : ℕ)
    (hΛ : ∀ c : K × K, (T.filter (fun e => ch e = c)).card ≤ Λ) :
    T.card ≤ Λ * Fintype.card K ^ 2 := by
  have h1 := card_le_mul_card_image (f := ch) T Λ (fun c _ => hΛ c)
  have h2 : (T.image ch).card ≤ Fintype.card K ^ 2 := by
    calc (T.image ch).card ≤ Fintype.card (K × K) := card_le_univ _
      _ = Fintype.card K ^ 2 := by rw [Fintype.card_prod, sq]
  exact h1.trans (Nat.mul_le_mul_left Λ h2)

/-- Theorem 4.9(2) of the paper, single lane. For `z` outside the exceptional set with threshold
`K₀ (K₀ - 1) (K₀ - M)` and every answer vector `m`: every set `W ⊆ T` of at least `K₀` candidates
with pairwise different challenges, all consistent with `m` at all points, contains more than `M`
folds of one rational pair, the pair of two of its elements. -/
theorem deepFold_class {T : Finset (Cand K)} {s K₀ M : ℕ} {z : Fin s → K}
    (hz : z ∉ ExcD T s (K₀ * (K₀ - 1) * (K₀ - M)))
    (m : Fin s → K × K) {W : Finset (Cand K)} (hWT : W ⊆ T)
    (hWc : ∀ e ∈ W, ∀ e' ∈ W, e.1 = e'.1 → e = e')
    (hW : ∀ e ∈ W, ∀ i, Cons e (z i) (m i).1 (m i).2) (hK : K₀ ≤ W.card) :
    ∃ e₁ ∈ W, ∃ e₂ ∈ W, e₁.1 ≠ e₂.1 ∧
      M < (W.filter (fun e => IsFold (pairF e₁ e₂) (pairG e₁ e₂) e)).card := by
  obtain ⟨e₁, he₁, e₂, he₂, hne, hbig⟩ := exists_big_class T
    Dep (fun e₁ e₂ e₃ z => (Delta e₁ e₂ e₃).eval z = 0)
    (fun (e : Cand K) (z : K) (m : K × K) => Cons e z m.1 m.2)
    (fun _ _ _ _ _ h₁ h₂ h₃ => Delta_eval_eq_zero h₁ h₂ h₃) hz m hWT hW hK
  have hc : e₁.1 ≠ e₂.1 := fun h => hne (hWc e₁ he₁ e₂ he₂ h)
  refine ⟨e₁, he₁, e₂, he₂, hc, lt_of_lt_of_le hbig (card_le_card ?_)⟩
  intro e he
  obtain ⟨heW, hdep⟩ := mem_filter.mp he
  refine mem_filter.mpr ⟨heW, ?_⟩
  by_cases h1 : e₁.1 = e.1
  · rw [← hWc e₁ he₁ e heW h1]
    exact isFold_pair_left e₁ e₂
  · by_cases h2 : e₂.1 = e.1
    · rw [← hWc e₂ he₂ e heW h2]
      exact isFold_pair_right hc
    · exact (Delta_eq_zero_iff hc e).mp (hdep ⟨hc, h1, h2⟩)

/-- Theorem 4.9(2) of the paper joined with Lemma 4.7, single lane.

`D` is the domain, `f₀, f₁` the two halves of the word, `T` a set of candidates `(c, P)` with
`deg P ≤ d` and `P` agreeing with `f₁ + a_c f₀` on at least `A` points of `D`. Let
`M ≥ max(q, C(n, 2))`. For `z` outside the exceptional set of `T` and every answer vector
`m = (y^F_i, y^G_i)`: every `W ⊆ T` with pairwise different challenges, at least `K₀` elements,
all consistent with `m`, contains more than `M` folds `G₀ + a_c F₀` of one polynomial pair with
`deg F₀ < d`, `deg G₀ ≤ d`, which agrees with `(f₀, f₁)` on at least `A - 1` common points and
has `F₀(z_i) = y^F_i`, `G₀(z_i) = y^G_i` for all `i`. -/
theorem deepFold_theorem3 (D : Finset K) (f₀ f₁ : K → K) {d A : ℕ}
    {T : Finset (Cand K)} (hTd : ∀ e ∈ T, e.2.natDegree ≤ d)
    (hTA : ∀ e ∈ T, A ≤ (agr D f₀ f₁ e).card)
    {s K₀ M : ℕ} (hMq : Fintype.card K ≤ M) (hMn : D.card.choose 2 ≤ M)
    {z : Fin s → K} (hz : z ∉ ExcD T s (K₀ * (K₀ - 1) * (K₀ - M)))
    (m : Fin s → K × K) {W : Finset (Cand K)} (hWT : W ⊆ T)
    (hWc : ∀ e ∈ W, ∀ e' ∈ W, e.1 = e'.1 → e = e')
    (hW : ∀ e ∈ W, ∀ i, Cons e (z i) (m i).1 (m i).2) (hK : K₀ ≤ W.card) :
    ∃ F₀ G₀ : K[X], F₀.degree < (d : WithBot ℕ) ∧ G₀.natDegree ≤ d ∧
      A ≤ (agrPair D f₀ f₁ F₀ G₀).card + 1 ∧
      M < (W.filter (fun e => e.2 = G₀ + aff e.1 * F₀)).card ∧
      ∀ i, F₀.eval (z i) = (m i).1 ∧ G₀.eval (z i) = (m i).2 := by
  obtain ⟨e₁, he₁, e₂, he₂, hc, hbig⟩ := deepFold_class hz m hWT hWc hW hK
  set Cl := W.filter (fun e => IsFold (pairF e₁ e₂) (pairG e₁ e₂) e) with hCl
  have hClW : ∀ e ∈ Cl, e ∈ W := fun e he => (mem_filter.mp he).1
  have hClfold : ∀ e ∈ Cl, IsFold (pairF e₁ e₂) (pairG e₁ e₂) e ∧ e.2.natDegree ≤ d :=
    fun e he => ⟨(mem_filter.mp he).2, hTd e (hWT (hClW e he))⟩
  have hqC : Fintype.card K < Cl.card := lt_of_le_of_lt hMq hbig
  obtain ⟨F₀, G₀, hF, hG, hFd, hGd⟩ := class_poly_of_card_gt hClfold hqC
  have hCleq : ∀ e ∈ Cl, e.2 = G₀ + aff e.1 * F₀ := by
    intro e he
    have h1 := (hClfold e he).1
    unfold IsFold at h1
    rw [hF, hG, ← map_mul, ← map_add] at h1
    exact phi_injective h1
  have hinjC : ∀ e ∈ Cl, ∀ e' ∈ Cl, e.1 = e'.1 → e = e' := fun e he e' he' h =>
    hWc e (hClW e he) e' (hClW e' he') h
  refine ⟨F₀, G₀, hFd, hGd, ?_, ?_, ?_⟩
  · exact agrPair_card_ge D f₀ f₁ F₀ G₀ Cl hCleq (fun e he => hTA e (hWT (hClW e he)))
      (lt_of_le_of_lt hMn hbig)
  · refine lt_of_lt_of_le hbig (card_le_card ?_)
    intro e he
    exact mem_filter.mpr ⟨hClW e he, hCleq e he⟩
  · intro i
    by_contra hcon
    have hF' : F₀.eval (z i) ≠ (m i).1 := by
      intro hFeq
      apply hcon
      refine ⟨hFeq, ?_⟩
      obtain ⟨e, he⟩ : Cl.Nonempty := card_pos.mp (by omega)
      have h1 := hW e (hClW e he) i
      unfold Cons at h1
      rw [hCleq e he] at h1
      simp only [eval_add, eval_mul, aff_eval, hFeq] at h1
      linear_combination h1
    have hline : ∀ e ∈ Cl, e.1.1 + z i * e.1.2 =
        ((m i).2 - G₀.eval (z i)) / (F₀.eval (z i) - (m i).1) := by
      intro e he
      have h1 := hW e (hClW e he) i
      unfold Cons at h1
      rw [hCleq e he] at h1
      simp only [eval_add, eval_mul, aff_eval] at h1
      rw [eq_div_iff (sub_ne_zero.mpr hF')]
      linear_combination h1
    exact absurd (card_le_of_line (ch := fun e : Cand K => e.1) hinjC hline) (not_le.mpr hqC)

end DeepFold
