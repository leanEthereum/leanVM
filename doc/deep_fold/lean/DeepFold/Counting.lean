/-
The probabilistic step of the DEEP fold lemma, as counting statements over finite sets:
Lemma 4.6(d), Definition 4.8 and Theorem 4.9 of the paper, in abstract form.

The abstract part knows nothing of polynomials: candidates are elements of a type `τ`, a ternary
relation `dep` says when three of them are in one class, `van t₁ t₂ t₃ z` says that the
determinant of the triple vanishes at the point `z`, and `cons t z m` says that the candidate is
consistent with the answer `m` at `z`.
-/
import Mathlib

open Polynomial Finset
open scoped Classical

namespace DeepFold

section Points

variable {Pt : Type*} [Fintype Pt]

/-- The vectors of `s` points that all lie in `R` number `|R|^s`. -/
theorem card_forall_mem (s : ℕ) (R : Finset Pt) :
    (univ.filter (fun z : Fin s → Pt => ∀ i, z i ∈ R)).card = R.card ^ s := by
  have h : (univ.filter (fun z : Fin s → Pt => ∀ i, z i ∈ R)) =
      Fintype.piFinset (fun _ : Fin s => R) := by
    ext z
    simp [Fintype.mem_piFinset]
  rw [h, Fintype.card_piFinset]
  simp

/-- If at most `D` points satisfy `p`, at most `D^s` vectors of `s` points satisfy it at every
coordinate (independence of the points, in counting form). -/
theorem card_forall_pred_le (s : ℕ) (p : Pt → Prop) {D : ℕ} (hD : (univ.filter p).card ≤ D) :
    (univ.filter (fun z : Fin s → Pt => ∀ i, p (z i))).card ≤ D ^ s := by
  have h := card_forall_mem s (univ.filter p)
  simp only [mem_filter, mem_univ, true_and] at h
  rw [h]
  exact Nat.pow_le_pow_left hD s

end Points

section SchwartzZippel

variable {K : Type*} [Field K] [Fintype K]

/-- A nonzero polynomial has at most `natDegree` roots in the field. -/
theorem card_roots_le {p : K[X]} (hp : p ≠ 0) :
    (univ.filter (fun x : K => p.eval x = 0)).card ≤ p.natDegree := by
  calc (univ.filter (fun x : K => p.eval x = 0)).card ≤ p.roots.toFinset.card := by
        apply Finset.card_le_card
        intro x hx
        simp only [mem_filter, mem_univ, true_and] at hx
        simp [mem_roots hp, IsRoot.def, hx]
    _ ≤ Multiset.card p.roots := Multiset.toFinset_card_le _
    _ ≤ p.natDegree := card_roots' p

/-- A fixed nonzero polynomial of degree at most `D` vanishes at all of `s` points for at most
`D^s` of the `q^s` point vectors. -/
theorem card_vanish_all_le {p : K[X]} (hp : p ≠ 0) {D : ℕ} (hD : p.natDegree ≤ D) (s : ℕ) :
    (univ.filter (fun z : Fin s → K => ∀ i, p.eval (z i) = 0)).card ≤ D ^ s :=
  card_forall_pred_le s _ ((card_roots_le hp).trans hD)

/-- The same as a probability over `s` independent uniform points: at most `(D/q)^s`. -/
theorem prob_vanish_all_le {p : K[X]} (hp : p ≠ 0) {D : ℕ} (hD : p.natDegree ≤ D) (s : ℕ) :
    ((univ.filter (fun z : Fin s → K => ∀ i, p.eval (z i) = 0)).card : ℚ) /
        (Fintype.card (Fin s → K) : ℚ) ≤ ((D : ℚ) / Fintype.card K) ^ s := by
  have hcard : (Fintype.card (Fin s → K) : ℚ) = (Fintype.card K : ℚ) ^ s := by
    simp
  rw [hcard, div_pow]
  gcongr
  exact_mod_cast card_vanish_all_le hp hD s

end SchwartzZippel

section Abstract

variable {τ Pt Ans : Type*} [Fintype Pt]

/-- `N(z)`: the number of ordered triples of `T` that are not dependent and whose determinant
vanishes at every point of `z`. -/
noncomputable def Ncount (T : Finset τ) (dep : τ → τ → τ → Prop) (van : τ → τ → τ → Pt → Prop)
    {s : ℕ} (z : Fin s → Pt) : ℕ :=
  (((T ×ˢ T) ×ˢ T).filter
    (fun t => ¬ dep t.1.1 t.1.2 t.2 ∧ ∀ i, van t.1.1 t.1.2 t.2 (z i))).card

/-- The exceptional set of point vectors: `N(z) ≥ B`. It depends on `T` only, not on answers. -/
noncomputable def Exc (T : Finset τ) (dep : τ → τ → τ → Prop) (van : τ → τ → τ → Pt → Prop)
    (s B : ℕ) : Finset (Fin s → Pt) :=
  univ.filter (fun z => B ≤ Ncount T dep van z)

/-- `∑_z N(z) ≤ |T|^3 D^s` when every non-dependent triple vanishes at no more than `D` points:
the expectation of `N`, times `|Pt|^s`. -/
theorem sum_Ncount_le (T : Finset τ) (dep : τ → τ → τ → Prop) (van : τ → τ → τ → Pt → Prop)
    {D : ℕ}
    (hSZ : ∀ t₁ ∈ T, ∀ t₂ ∈ T, ∀ t₃ ∈ T, ¬ dep t₁ t₂ t₃ →
      (univ.filter (fun z => van t₁ t₂ t₃ z)).card ≤ D) (s : ℕ) :
    ∑ z : Fin s → Pt, Ncount T dep van z ≤ T.card ^ 3 * D ^ s := by
  simp only [Ncount, card_filter]
  rw [sum_comm]
  calc ∑ t ∈ (T ×ˢ T) ×ˢ T, ∑ z : Fin s → Pt,
          (if ¬ dep t.1.1 t.1.2 t.2 ∧ ∀ i, van t.1.1 t.1.2 t.2 (z i) then 1 else 0)
      ≤ ∑ _t ∈ (T ×ˢ T) ×ˢ T, D ^ s := by
        apply sum_le_sum
        intro t ht
        simp only [mem_product] at ht
        rw [← card_filter]
        by_cases hdep : dep t.1.1 t.1.2 t.2
        · simp [hdep]
        · simp only [hdep, not_false_eq_true, true_and]
          exact card_forall_pred_le s _ (hSZ _ ht.1.1 _ ht.1.2 _ ht.2 hdep)
    _ = T.card ^ 3 * D ^ s := by
        rw [sum_const, card_product, card_product, smul_eq_mul]
        ring

/-- Markov, in counting form: `|Exc| · B ≤ |T|^3 D^s`. -/
theorem card_Exc_mul_le (T : Finset τ) (dep : τ → τ → τ → Prop) (van : τ → τ → τ → Pt → Prop)
    {D : ℕ}
    (hSZ : ∀ t₁ ∈ T, ∀ t₂ ∈ T, ∀ t₃ ∈ T, ¬ dep t₁ t₂ t₃ →
      (univ.filter (fun z => van t₁ t₂ t₃ z)).card ≤ D) (s B : ℕ) :
    (Exc T dep van s B).card * B ≤ T.card ^ 3 * D ^ s := by
  calc (Exc T dep van s B).card * B = ∑ _z ∈ Exc T dep van s B, B := by simp
    _ ≤ ∑ z ∈ Exc T dep van s B, Ncount T dep van z :=
        sum_le_sum (fun z hz => (mem_filter.mp hz).2)
    _ ≤ ∑ z, Ncount T dep van z := sum_le_sum_of_subset (subset_univ _)
    _ ≤ _ := sum_Ncount_le T dep van hSZ s

/-- The density of the exceptional set among the `|Pt|^s` point vectors is at most
`|T|^3 ε^s / B` with `ε = D / |Pt|`. -/
theorem density_Exc_le [Nonempty Pt] (T : Finset τ) (dep : τ → τ → τ → Prop)
    (van : τ → τ → τ → Pt → Prop) {D : ℕ}
    (hSZ : ∀ t₁ ∈ T, ∀ t₂ ∈ T, ∀ t₃ ∈ T, ¬ dep t₁ t₂ t₃ →
      (univ.filter (fun z => van t₁ t₂ t₃ z)).card ≤ D) (s : ℕ) {B : ℕ} (hB : 0 < B) :
    ((Exc T dep van s B).card : ℚ) / (Fintype.card (Fin s → Pt) : ℚ) ≤
      (T.card : ℚ) ^ 3 * ((D : ℚ) / Fintype.card Pt) ^ s / B := by
  have h : ((Exc T dep van s B).card : ℚ) * B ≤ (T.card : ℚ) ^ 3 * (D : ℚ) ^ s := by
    exact_mod_cast card_Exc_mul_le T dep van hSZ s B
  have hq0 : (0 : ℚ) < Fintype.card Pt := by exact_mod_cast Fintype.card_pos
  have hq : (0 : ℚ) < (Fintype.card Pt : ℚ) ^ s := pow_pos hq0 s
  have hB' : (0 : ℚ) < B := by exact_mod_cast hB
  have hcard : (Fintype.card (Fin s → Pt) : ℚ) = (Fintype.card Pt : ℚ) ^ s := by
    simp
  have hrhs : (T.card : ℚ) ^ 3 * ((D : ℚ) / Fintype.card Pt) ^ s / B =
      (T.card : ℚ) ^ 3 * (D : ℚ) ^ s / B / (Fintype.card Pt : ℚ) ^ s := by
    rw [div_pow]
    field_simp
  rw [hcard, hrhs]
  gcongr
  rw [le_div_iff₀ hB']
  exact h

/-- The exceptional set shrinks as the threshold grows. -/
theorem not_mem_Exc_of_le (T : Finset τ) (dep : τ → τ → τ → Prop) (van : τ → τ → τ → Pt → Prop)
    {s B B' : ℕ} (hBB : B ≤ B') {z : Fin s → Pt} (hz : z ∉ Exc T dep van s B) :
    z ∉ Exc T dep van s B' := by
  intro h
  apply hz
  simp only [Exc, mem_filter, mem_univ, true_and] at h ⊢
  exact hBB.trans h

/-- Lemma 4.6(d) of the paper. Let `W` have `K` elements and suppose that
for any two distinct elements at most `M` elements of `W` are dependent with them (every class
holds at most `M` elements of `W`). Then at least `K (K - 1) (K - M)` ordered triples of `W`,
with distinct first two entries, are not dependent. -/
theorem card_nondep_triples_ge (dep : τ → τ → τ → Prop) (W : Finset τ) {M : ℕ}
    (hM : ∀ t₁ ∈ W, ∀ t₂ ∈ W, t₁ ≠ t₂ → (W.filter (fun t₃ => dep t₁ t₂ t₃)).card ≤ M) :
    W.card * (W.card - 1) * (W.card - M) ≤
      ((W.offDiag ×ˢ W).filter (fun t => ¬ dep t.1.1 t.1.2 t.2)).card := by
  rw [card_filter, sum_product]
  calc W.card * (W.card - 1) * (W.card - M) = ∑ _p ∈ W.offDiag, (W.card - M) := by
        rw [sum_const, offDiag_card, smul_eq_mul, Nat.mul_sub_one]
    _ ≤ _ := by
        apply sum_le_sum
        intro p hp
        rw [mem_offDiag] at hp
        rw [← card_filter]
        dsimp only
        have hle := hM p.1 hp.1 p.2 hp.2.1 hp.2.2
        have hsplit := card_filter_add_card_filter_not (s := W) (fun t₃ => dep p.1 p.2 t₃)
        omega

/-- Theorem 4.9(2) of the paper, abstract form. Let `z` be outside the exceptional set with
threshold `K₀ (K₀ - 1) (K₀ - M)`. Then for every answer vector `m`, every set `W ⊆ T` of at least
`K₀` candidates that are all consistent with `m` at every point contains two distinct candidates
whose class (the candidates of `W` dependent with them) has more than `M` elements. -/
theorem exists_big_class (T : Finset τ) (dep : τ → τ → τ → Prop) (van : τ → τ → τ → Pt → Prop)
    (cons : τ → Pt → Ans → Prop)
    (hcons : ∀ t₁ t₂ t₃ z m, cons t₁ z m → cons t₂ z m → cons t₃ z m → van t₁ t₂ t₃ z)
    {s K₀ M : ℕ} {z : Fin s → Pt} (hz : z ∉ Exc T dep van s (K₀ * (K₀ - 1) * (K₀ - M)))
    (m : Fin s → Ans) {W : Finset τ} (hWT : W ⊆ T)
    (hW : ∀ t ∈ W, ∀ i, cons t (z i) (m i)) (hK : K₀ ≤ W.card) :
    ∃ t₁ ∈ W, ∃ t₂ ∈ W, t₁ ≠ t₂ ∧ M < (W.filter (fun t₃ => dep t₁ t₂ t₃)).card := by
  by_contra hcon
  push Not at hcon
  apply hz
  simp only [Exc, mem_filter, mem_univ, true_and]
  have h1 := card_nondep_triples_ge dep W hcon
  have h2 : ((W.offDiag ×ˢ W).filter (fun t => ¬ dep t.1.1 t.1.2 t.2)).card ≤
      Ncount T dep van z := by
    unfold Ncount
    apply card_le_card
    intro t ht
    rw [mem_filter, mem_product, mem_offDiag] at ht
    obtain ⟨⟨⟨h1, h2, -⟩, h3⟩, hnd⟩ := ht
    simp only [mem_filter, mem_product]
    exact ⟨⟨⟨hWT h1, hWT h2⟩, hWT h3⟩, hnd,
      fun i => hcons _ _ _ _ _ (hW _ h1 i) (hW _ h2 i) (hW _ h3 i)⟩
  have h3 : K₀ * (K₀ - 1) * (K₀ - M) ≤ W.card * (W.card - 1) * (W.card - M) :=
    Nat.mul_le_mul (Nat.mul_le_mul hK (Nat.sub_le_sub_right hK 1)) (Nat.sub_le_sub_right hK M)
  exact h3.trans (h1.trans h2)

end Abstract

/-- A simpler threshold: for `K₀ ≥ 26` and `M ≤ 0.74 K₀`, the threshold `K₀^3 / 4` is at most the
threshold `K₀ (K₀ - 1) (K₀ - M)` of Definition 4.8 of the paper. -/
theorem quarter_cube_le {K₀ M : ℕ} (hK : 26 ≤ K₀) (hM : 100 * M ≤ 74 * K₀) :
    K₀ ^ 3 ≤ 4 * (K₀ * (K₀ - 1) * (K₀ - M)) := by
  obtain ⟨k, rfl⟩ : ∃ k, K₀ = k + 1 := ⟨K₀ - 1, by omega⟩
  obtain ⟨a, ha⟩ : ∃ a, a = k + 1 - M := ⟨_, rfl⟩
  have h1 : 26 * (k + 1) ≤ 100 * a := by omega
  have h2 : 100 * (k + 1) ≤ 104 * k := by omega
  rw [← ha, Nat.add_sub_cancel]
  have h3 : 100 * (k + 1) ^ 3 ≤ 100 * (4 * ((k + 1) * k * a)) := by
    calc 100 * (k + 1) ^ 3 = (100 * (k + 1)) * (k + 1) ^ 2 := by ring
      _ ≤ (104 * k) * (k + 1) ^ 2 := Nat.mul_le_mul_right _ h2
      _ = 4 * ((k + 1) * k) * (26 * (k + 1)) := by ring
      _ ≤ 4 * ((k + 1) * k) * (100 * a) := Nat.mul_le_mul_left _ h1
      _ = 100 * (4 * ((k + 1) * k * a)) := by ring
  exact Nat.le_of_mul_le_mul_left h3 (by norm_num)

/-- Theorem 4.9(2) of the paper with the simpler threshold, abstractly: outside the exceptional set
with threshold `⌈K₀^3 / 4⌉`, with `K₀ ≥ 26`, every set `W ⊆ T` of at least `K₀` candidates
consistent with one answer vector has two distinct elements whose class holds at least
`0.74 |W|` elements of `W`. -/
theorem exists_big_class_quarter {τ Pt Ans : Type*} [Fintype Pt] (T : Finset τ)
    (dep : τ → τ → τ → Prop) (van : τ → τ → τ → Pt → Prop) (cons : τ → Pt → Ans → Prop)
    (hcons : ∀ t₁ t₂ t₃ z m, cons t₁ z m → cons t₂ z m → cons t₃ z m → van t₁ t₂ t₃ z)
    {s K₀ : ℕ} (hK₀ : 26 ≤ K₀) {z : Fin s → Pt} (hz : z ∉ Exc T dep van s ((K₀ ^ 3 + 3) / 4))
    (m : Fin s → Ans) {W : Finset τ} (hWT : W ⊆ T)
    (hW : ∀ t ∈ W, ∀ i, cons t (z i) (m i)) (hK : K₀ ≤ W.card) :
    ∃ t₁ ∈ W, ∃ t₂ ∈ W, t₁ ≠ t₂ ∧
      74 * W.card ≤ 100 * (W.filter (fun t₃ => dep t₁ t₂ t₃)).card := by
  have h1 := quarter_cube_le (K₀ := W.card) (M := 74 * W.card / 100) (hK₀.trans hK) (by omega)
  have h2 : (K₀ ^ 3 + 3) / 4 ≤ (W.card ^ 3 + 3) / 4 :=
    Nat.div_le_div_right (Nat.add_le_add_right (Nat.pow_le_pow_left hK 3) 3)
  have h3 : (W.card ^ 3 + 3) / 4 ≤
      W.card * (W.card - 1) * (W.card - 74 * W.card / 100) := by
    generalize W.card * (W.card - 1) * (W.card - 74 * W.card / 100) = x at h1
    generalize W.card ^ 3 = y at h1
    omega
  obtain ⟨t₁, ht₁, t₂, ht₂, hne, hbig⟩ := exists_big_class T dep van cons hcons
    (not_mem_Exc_of_le T dep van (h2.trans h3) hz) m hWT hW le_rfl
  exact ⟨t₁, ht₁, t₂, ht₂, hne, by omega⟩


end DeepFold
