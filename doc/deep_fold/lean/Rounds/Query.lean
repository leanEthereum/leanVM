/-
The query message of a level that is not the last: transition M3 of Theorem 5.2 of the paper
(Section 5.4) and of Theorem 5.6 (Section 5.5).

At the end of level `i` the fold is one lane, a word `w = O^{(i,ℓ_i)} : D → K`, and the point
claims are plain evaluations at `ζ_m`. The prover has committed the next word `O'`, sent the high
part (here the polynomial `C = V̂_κ H`), received the new points and answered them. The verifier's
message is `t` query positions in `D` and the batching scalar `λ`.

The map `low` sends a tuple `U` of the next level to `𝒫_{g_U}`, the polynomial whose novel-basis
coefficients are the message of `U`; it is linear, and that is all this file uses of it. So
`P^*_U = low U + C`, a column weight is `⟨W_{i,x}, g_U⟩ = (low U)(x)`, and the residual weight is
`U ↦ ⟨W, low U⟩`.
-/
import Rounds.Batch

open Polynomial Finset
open scoped Classical

namespace Rounds

open DeepFold

variable {K : Type*} [Field K] [Fintype K]

omit [Field K] [Fintype K] in
/-- A filter of a product whose fibres have at most `N` elements has at most `|X| N` elements. -/
theorem card_filter_prod_le {α β : Type*} [Fintype β] (X : Finset α) (Q : α → β → Prop) (N : ℕ)
    (h : ∀ a ∈ X, (univ.filter (fun b : β => Q a b)).card ≤ N) :
    ((X ×ˢ (univ : Finset β)).filter (fun p => Q p.1 p.2)).card ≤ X.card * N := by
  rw [Finset.card_filter, Finset.sum_product]
  calc ∑ a ∈ X, ∑ b : β, (if Q a b then 1 else 0)
      = ∑ a ∈ X, (univ.filter (fun b : β => Q a b)).card :=
        sum_congr rfl (fun a _ => (Finset.card_filter _ _).symm)
    _ ≤ ∑ _a ∈ X, N := sum_le_sum h
    _ = X.card * N := by rw [sum_const, smul_eq_mul]

omit [Field K] [Fintype K] in
/-- Of the `n^t` vectors of `t` query positions in `D`, at most `|S|^t` have all positions in
`S`. -/
theorem card_queries_in_le (D S : Finset K) (t : ℕ) :
    ((Fintype.piFinset (fun _ : Fin t => D)).filter (fun x => ∀ q, x q ∈ S)).card ≤
      S.card ^ t := by
  have hsub : (Fintype.piFinset (fun _ : Fin t => D)).filter (fun x => ∀ q, x q ∈ S) ⊆
      Fintype.piFinset (fun _ : Fin t => S) := fun x hx =>
    Fintype.mem_piFinset.mpr (mem_filter.mp hx).2
  refine (card_le_card hsub).trans (le_of_eq ?_)
  rw [Fintype.card_piFinset, prod_const, card_univ, Fintype.card_fin]

omit [Fintype K] in
/-- **The query count of M3 and M4** (Section 5.4 of the paper, M3, Case 2). If a polynomial `P`
agrees with the word `w` on fewer than `A` columns of `D`, then at most `(A - 1)^t` of the `n^t`
vectors of `t` query positions see no disagreement. -/
theorem card_queries_agree_le (D : Finset K) (w : K → K) (P : K[X]) {A : ℕ}
    (hA : (D.filter (fun x => P.eval x = w x)).card < A) (t : ℕ) :
    ((Fintype.piFinset (fun _ : Fin t => D)).filter
      (fun x => ∀ q, P.eval (x q) = w (x q))).card ≤ (A - 1) ^ t := by
  have hsub : (Fintype.piFinset (fun _ : Fin t => D)).filter
      (fun x => ∀ q, P.eval (x q) = w (x q)) ⊆
      (Fintype.piFinset (fun _ : Fin t => D)).filter
        (fun x => ∀ q, x q ∈ D.filter (fun x => P.eval x = w x)) := by
    intro x hx
    obtain ⟨hxD, hxq⟩ := mem_filter.mp hx
    exact mem_filter.mpr ⟨hxD, fun q => mem_filter.mpr ⟨Fintype.mem_piFinset.mp hxD q, hxq q⟩⟩
  refine (card_le_card hsub).trans ((card_queries_in_le D _ t).trans ?_)
  exact Nat.pow_le_pow_left (by omega) t

omit [Fintype K] in
/-- The query count as a density over `t` independent uniform positions: at most
`((A - 1)/n)^t`, the first term of rows M3 and M4 of Theorem 5.2 of the paper. -/
theorem density_queries_agree_le (D : Finset K) (w : K → K) (P : K[X]) {A : ℕ}
    (hA : (D.filter (fun x => P.eval x = w x)).card < A) (t : ℕ) :
    (((Fintype.piFinset (fun _ : Fin t => D)).filter
      (fun x => ∀ q, P.eval (x q) = w (x q))).card : ℚ) /
        ((Fintype.piFinset (fun _ : Fin t => D)).card : ℚ) ≤
      (((A - 1 : ℕ) : ℚ) / (D.card : ℚ)) ^ t := by
  have h := card_queries_agree_le D w P hA t
  have hcard : (Fintype.piFinset (fun _ : Fin t => D)).card = D.card ^ t := by
    rw [Fintype.card_piFinset, prod_const, card_univ, Fintype.card_fin]
  rw [hcard, div_pow]
  push_cast
  refine div_le_div_of_nonneg_right ?_ (by positivity)
  exact_mod_cast h

/-- The root count for the batching of Protocol 4.2 of the paper, step 2: a residual term with the
power `0`, `s` terms with the powers `1, ..., s` and `t` terms with the powers `s + 1, ..., s + t`.
If one term is nonzero, at most `s + t` values of `λ` are roots. -/
theorem card_batch3_zero_le {s t : ℕ} (a0 : K) (a : Fin s → K) (b : Fin t → K)
    (h : a0 ≠ 0 ∨ (∃ m, a m ≠ 0) ∨ ∃ q, b q ≠ 0) :
    (univ.filter (fun l : K => a0 + ∑ m : Fin s, l ^ ((m : ℕ) + 1) * a m +
      ∑ q : Fin t, l ^ (s + 1 + (q : ℕ)) * b q = 0)).card ≤ s + t := by
  let e : Unit ⊕ (Fin s ⊕ Fin t) → ℕ :=
    Sum.elim (fun _ => 0) (Sum.elim (fun m => (m : ℕ) + 1) (fun q => s + 1 + (q : ℕ)))
  let δ : Unit ⊕ (Fin s ⊕ Fin t) → K := Sum.elim (fun _ => a0) (Sum.elim a b)
  have he : Function.Injective e := by
    rintro (u | m | q) (u' | m' | q') h <;> simp only [e, Sum.elim_inl, Sum.elim_inr] at h
    · rfl
    · omega
    · omega
    · omega
    · rw [Fin.ext (by omega : (m : ℕ) = m')]
    · have := m.isLt
      omega
    · omega
    · have := m'.isLt
      omega
    · rw [Fin.ext (by omega : (q : ℕ) = q')]
  have hN : ∀ k, e k ≤ s + t := by
    rintro (u | m | q) <;> simp only [e, Sum.elim_inl, Sum.elim_inr]
    · omega
    · have := m.isLt
      omega
    · have := q.isLt
      omega
  have hδ : ∃ k, δ k ≠ 0 := by
    rcases h with h | ⟨m, hm⟩ | ⟨q, hq⟩
    · exact ⟨Sum.inl (), h⟩
    · exact ⟨Sum.inr (Sum.inl m), hm⟩
    · exact ⟨Sum.inr (Sum.inr q), hq⟩
  have hsum : ∀ l : K, ∑ k, l ^ e k * δ k = a0 + ∑ m : Fin s, l ^ ((m : ℕ) + 1) * a m +
      ∑ q : Fin t, l ^ (s + 1 + (q : ℕ)) * b q := by
    intro l
    simp [e, δ, Fintype.sum_sum_type, add_assoc]
  have := card_powsum_zero_le e he hN δ hδ
  simp only [hsum] at this
  exact this

/-- The invariant `(I^B_{i,ℓ_i})` at the end of a level, where the fold is one lane `w` and a
point claim is the plain evaluation `P(ζ_m) = v_m` (Section 5.3 of the paper with `j = ℓ_i`). -/
def Doomed₁ (D : Finset K) (w : K → K) (d A : ℕ) {s : ℕ} (ζ v : Fin s → K) (W : K[X] →ₗ[K] K)
    (σ : K) (B : K[X] → Prop) : Prop :=
  ∀ P : K[X], P.natDegree ≤ d → A ≤ (D.filter (fun x => P.eval x = w x)).card → B P →
    (∀ m, P.eval (ζ m) = v m) → W P ≠ σ

/-- A polynomial as a tuple with one lane. -/
noncomputable def constL (ι : Type*) : K[X] →ₗ[K] (ι → K[X]) where
  toFun P := fun _ => P
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

omit [Fintype K] in
/-- `Doomed` for a word with one lane and exponent zero is `Doomed₁`: the state that the last
fold round of a level leaves (`fold_transition` with a one-element lane type) is the state that
the query message starts from. -/
theorem Doomed.one_lane {ι : Type*} [Fintype ι] [Unique ι] {D : Finset K} {O : K → ι → K}
    {d A : ℕ} {s : ℕ} {z : Fin s → K × K} {v : Fin s → K} {W : (ι → K[X]) →ₗ[K] K} {σ : K}
    {B : (ι → K[X]) → Prop} (h : Doomed D O d A (fun _ => 0) z v W σ B) :
    Doomed₁ D (fun x => O x default) d A (fun m => (z m).2) v (W ∘ₗ constL ι) σ
      (fun P => B (fun _ => P)) := by
  intro P hP hA hB hpt
  refine h (fun _ => P) ⟨fun _ => hP, ?_⟩ hB ?_
  · refine hA.trans (card_le_card ?_)
    intro x hx
    obtain ⟨hxD, hxP⟩ := mem_filter.mp hx
    refine mem_filter.mpr ⟨hxD, fun u => ?_⟩
    rw [Unique.eq_default u]
    exact hxP
  · intro m
    rw [← hpt m]
    simp [evL]

variable {ι' : Type*} [Fintype ι']

/-- The weight of the next level (Protocol 4.2 of the paper, step 2, the batching): the residual
weight, the weights of the `s` converted point claims with the powers `λ^1, ..., λ^s`, and the
weights of the `t` query claims with the powers `λ^(s+1), ..., λ^(s+t)`. -/
noncomputable def nextW (W : K[X] →ₗ[K] K) (low : (ι' → K[X]) →ₗ[K] K[X]) {s t : ℕ}
    (ζ : Fin s → K) (x : Fin t → K) (l : K) : (ι' → K[X]) →ₗ[K] K :=
  W ∘ₗ low + ∑ m : Fin s, l ^ ((m : ℕ) + 1) • (leval (ζ m) ∘ₗ low) +
    ∑ q : Fin t, l ^ (s + 1 + (q : ℕ)) • (leval (x q) ∘ₗ low)

/-- The claim of the next level (Protocol 4.2 of the paper, step 2, the conversion (5) and the
batching): the residual value, the converted point values `c'_m = v_m + V̂_κ(ζ_m) H(ζ_m)` and the
query values `c_q = w(x_q) + V̂_κ(x_q) H(x_q)`, with the same powers. -/
noncomputable def nextC (σ : K) (C : K[X]) (w : K → K) {s t : ℕ} (ζ v : Fin s → K)
    (x : Fin t → K) (l : K) : K :=
  σ + ∑ m : Fin s, l ^ ((m : ℕ) + 1) * (v m + C.eval (ζ m)) +
    ∑ q : Fin t, l ^ (s + 1 + (q : ℕ)) * (w (x q) + C.eval (x q))

/-- **Transition M3 of Theorem 5.2 and of Theorem 5.6 of the paper** (Sections 5.4 and 5.5),
counting form, in characteristic two.

Level `i` at its end: domain `D` of size `n`, folded word `w`, degree bound `d = d^{(i)}`,
agreement `A = A_i`, points `ζ` with carried values `v`, running claim `(W, σ)`, predicate `B`,
and `(I^B_{i,ℓ_i})` holds (`hI`). Level `i + 1`: word `O'` with its list at `(A', d')`, points
`z'` with answers `y'`, separating (`hsep`: at most one list member matches all answers, the
conclusion of Lemma 4.11). The link: `low U = 𝒫_{g_U}` (linear), `C = V̂_κ H` with
`deg(low U + C) ≤ d` for list members (`hdeg`, from (S1)), and the running weight ignores the high
part (`hWC`). The predicate of the next level is `B_{i+1,0}(U) = B(low U + C)` (`nextPred`).

Conclusion: among the `n^t q` messages (`t` positions in `D` and `λ`), at most
`(A - 1)^t q + n^t (s + t)` leave a state that is not doomed, that is, for which
`(I^B_{i+1,0})` fails for the batched claim of step 2 and the carried values `y'`. -/
theorem query_transition [CharP K 2] (D : Finset K) (w : K → K) (d A : ℕ) {s : ℕ}
    (ζ v : Fin s → K) (W : K[X] →ₗ[K] K) (σ : K) (B : K[X] → Prop)
    (hI : Doomed₁ D w d A ζ v W σ B)
    (D' : Finset K) (O' : K → ι' → K) (d' A' : ℕ) (ex' : ι' → ℕ) {s' : ℕ}
    (z' : Fin s' → K × K) (y' : Fin s' → K)
    (hsep : ∀ U U' : ι' → K[X], InList D' O' d' A' U → InList D' O' d' A' U' →
      (∀ m, evL ex' (z' m) U = y' m) → (∀ m, evL ex' (z' m) U' = y' m) → U = U')
    (low : (ι' → K[X]) →ₗ[K] K[X]) (C : K[X])
    (hdeg : ∀ U : ι' → K[X], InList D' O' d' A' U → (low U + C).natDegree ≤ d)
    (hWC : W C = 0) (t : ℕ) :
    (((Fintype.piFinset (fun _ : Fin t => D)) ×ˢ (univ : Finset K)).filter
      (fun xl : (Fin t → K) × K =>
        ¬ Doomed D' O' d' A' ex' z' y' (nextW W low ζ xl.1 xl.2) (nextC σ C w ζ v xl.1 xl.2)
          (fun U => B (low U + C)))).card ≤
      (A - 1) ^ t * Fintype.card K + D.card ^ t * (s + t) := by
  by_cases hex : ∃ U : ι' → K[X], InList D' O' d' A' U ∧ B (low U + C) ∧
      ∀ m, evL ex' (z' m) U = y' m
  swap
  · have hempty : ((Fintype.piFinset (fun _ : Fin t => D)) ×ˢ (univ : Finset K)).filter
        (fun xl : (Fin t → K) × K =>
          ¬ Doomed D' O' d' A' ex' z' y' (nextW W low ζ xl.1 xl.2) (nextC σ C w ζ v xl.1 xl.2)
            (fun U => B (low U + C))) = ∅ :=
      filter_eq_empty_iff.mpr (fun xl _ hnd => hnd (fun U hU hB hpt _ => hex ⟨U, hU, hB, hpt⟩))
    rw [hempty, card_empty]
    exact Nat.zero_le _
  obtain ⟨Us, hUs, hBs, hpts⟩ := hex
  have hPd : (low Us + C).natDegree ≤ d := hdeg Us hUs
  -- the root equation of a message after which the state is not doomed
  let Q : (Fin t → K) → K → Prop := fun x l =>
    (W (low Us + C) - σ) + ∑ m : Fin s, l ^ ((m : ℕ) + 1) * ((low Us + C).eval (ζ m) - v m) +
      ∑ q : Fin t, l ^ (s + 1 + (q : ℕ)) * ((low Us + C).eval (x q) - w (x q)) = 0
  have hc2 : ∀ a b : K, (low Us + C).eval a - b = (low Us).eval a - (b + C.eval a) := by
    intro a b
    rw [eval_add]
    have h2 : C.eval a + C.eval a = 0 := CharTwo.add_self_eq_zero _
    linear_combination h2
  have hbad : ∀ xl : (Fin t → K) × K,
      ¬ Doomed D' O' d' A' ex' z' y' (nextW W low ζ xl.1 xl.2) (nextC σ C w ζ v xl.1 xl.2)
        (fun U => B (low U + C)) → Q xl.1 xl.2 := by
    intro xl hnd
    unfold Doomed at hnd
    push Not at hnd
    obtain ⟨U, hU, _, hpt, hW⟩ := hnd
    rw [hsep U Us hU hUs hpt hpts] at hW
    simp only [nextW, nextC, LinearMap.add_apply, LinearMap.coe_sum, Finset.sum_apply,
      LinearMap.smul_apply, LinearMap.comp_apply, leval_apply, smul_eq_mul] at hW
    simp only [Q, hc2, map_add, hWC, add_zero, mul_sub, sum_sub_distrib]
    linear_combination hW
  have hsubQ : ((Fintype.piFinset (fun _ : Fin t => D)) ×ˢ (univ : Finset K)).filter
      (fun xl : (Fin t → K) × K =>
        ¬ Doomed D' O' d' A' ex' z' y' (nextW W low ζ xl.1 xl.2) (nextC σ C w ζ v xl.1 xl.2)
          (fun U => B (low U + C))) ⊆
      ((Fintype.piFinset (fun _ : Fin t => D)) ×ˢ (univ : Finset K)).filter
        (fun xl => Q xl.1 xl.2) := fun xl hxl =>
    mem_filter.mpr ⟨(mem_filter.mp hxl).1, hbad xl (mem_filter.mp hxl).2⟩
  refine (card_le_card hsubQ).trans ?_
  have hcardD : (Fintype.piFinset (fun _ : Fin t => D)).card = D.card ^ t := by
    rw [Fintype.card_piFinset, prod_const, card_univ, Fintype.card_fin]
  by_cases hA : A ≤ (D.filter (fun x => (low Us + C).eval x = w x)).card
  · -- Case 1: `P^*` is in the list of the level that ends, so it violates a carried claim
    have hviol : W (low Us + C) - σ ≠ 0 ∨
        (∃ m, (low Us + C).eval (ζ m) - v m ≠ 0) ∨ False := by
      by_cases hpt : ∀ m, (low Us + C).eval (ζ m) = v m
      · exact Or.inl (sub_ne_zero.mpr (hI _ hPd hA hBs hpt))
      · push Not at hpt
        obtain ⟨m, hm⟩ := hpt
        exact Or.inr (Or.inl ⟨m, sub_ne_zero.mpr hm⟩)
    have h1 := card_filter_prod_le (Fintype.piFinset (fun _ : Fin t => D)) Q (s + t)
      (fun x _ => card_batch3_zero_le _ _ _
        (hviol.imp_right (Or.imp_right (fun hf => hf.elim))))
    rw [hcardD] at h1
    exact h1.trans (Nat.le_add_left _ _)
  · -- Case 2: `P^*` is not in the list, so a query sees a disagreement or all land in agreement
    have hsplit : ((Fintype.piFinset (fun _ : Fin t => D)) ×ˢ (univ : Finset K)).filter
        (fun xl => Q xl.1 xl.2) ⊆
        ((Fintype.piFinset (fun _ : Fin t => D)).filter
          (fun x => ∀ q, (low Us + C).eval (x q) = w (x q))) ×ˢ (univ : Finset K) ∪
        (((Fintype.piFinset (fun _ : Fin t => D)).filter
          (fun x => ¬ ∀ q, (low Us + C).eval (x q) = w (x q))) ×ˢ (univ : Finset K)).filter
            (fun xl => Q xl.1 xl.2) := by
      intro xl hxl
      obtain ⟨hmem, hQ⟩ := mem_filter.mp hxl
      obtain ⟨hx, _⟩ := mem_product.mp hmem
      by_cases hall : ∀ q, (low Us + C).eval (xl.1 q) = w (xl.1 q)
      · exact mem_union_left _ (mem_product.mpr ⟨mem_filter.mpr ⟨hx, hall⟩, mem_univ _⟩)
      · exact mem_union_right _
          (mem_filter.mpr ⟨mem_product.mpr ⟨mem_filter.mpr ⟨hx, hall⟩, mem_univ _⟩, hQ⟩)
    refine (card_le_card hsplit).trans ((card_union_le _ _).trans (Nat.add_le_add ?_ ?_))
    · rw [card_product, card_univ]
      exact Nat.mul_le_mul_right _ (card_queries_agree_le D w _ (not_le.mp hA) t)
    · have h2 := card_filter_prod_le ((Fintype.piFinset (fun _ : Fin t => D)).filter
        (fun x => ¬ ∀ q, (low Us + C).eval (x q) = w (x q))) Q (s + t) (fun x hx => by
          have hnall := (mem_filter.mp hx).2
          push Not at hnall
          obtain ⟨q, hq⟩ := hnall
          exact card_batch3_zero_le _ _ _ (Or.inr (Or.inr ⟨q, sub_ne_zero.mpr hq⟩)))
      refine h2.trans (Nat.mul_le_mul_right _ ?_)
      rw [← hcardD]
      exact card_filter_le _ _

/-- Transition M3 as a density over `t` independent uniform positions in a nonempty `D` and a
uniform `λ`: at most `((A - 1)/n)^t + (s + t)/q`, row M3 of Theorem 5.2 of the paper. -/
theorem query_transition_density [CharP K 2] (D : Finset K) (hD : D.Nonempty) (w : K → K)
    (d A : ℕ) {s : ℕ} (ζ v : Fin s → K) (W : K[X] →ₗ[K] K) (σ : K) (B : K[X] → Prop)
    (hI : Doomed₁ D w d A ζ v W σ B)
    (D' : Finset K) (O' : K → ι' → K) (d' A' : ℕ) (ex' : ι' → ℕ) {s' : ℕ}
    (z' : Fin s' → K × K) (y' : Fin s' → K)
    (hsep : ∀ U U' : ι' → K[X], InList D' O' d' A' U → InList D' O' d' A' U' →
      (∀ m, evL ex' (z' m) U = y' m) → (∀ m, evL ex' (z' m) U' = y' m) → U = U')
    (low : (ι' → K[X]) →ₗ[K] K[X]) (C : K[X])
    (hdeg : ∀ U : ι' → K[X], InList D' O' d' A' U → (low U + C).natDegree ≤ d)
    (hWC : W C = 0) (t : ℕ) :
    ((((Fintype.piFinset (fun _ : Fin t => D)) ×ˢ (univ : Finset K)).filter
      (fun xl : (Fin t → K) × K =>
        ¬ Doomed D' O' d' A' ex' z' y' (nextW W low ζ xl.1 xl.2) (nextC σ C w ζ v xl.1 xl.2)
          (fun U => B (low U + C)))).card : ℚ) /
        ((D.card : ℚ) ^ t * (Fintype.card K : ℚ)) ≤
      (((A - 1 : ℕ) : ℚ) / (D.card : ℚ)) ^ t + ((s + t : ℕ) : ℚ) / (Fintype.card K : ℚ) := by
  have h := query_transition D w d A ζ v W σ B hI D' O' d' A' ex' z' y' hsep low C hdeg hWC t
  have hq : (0 : ℚ) < (Fintype.card K : ℚ) := by exact_mod_cast Fintype.card_pos
  have hn : (0 : ℚ) < (D.card : ℚ) ^ t := by
    have : (0 : ℚ) < (D.card : ℚ) := by exact_mod_cast hD.card_pos
    positivity
  have h' : ((((Fintype.piFinset (fun _ : Fin t => D)) ×ˢ (univ : Finset K)).filter
      (fun xl : (Fin t → K) × K =>
        ¬ Doomed D' O' d' A' ex' z' y' (nextW W low ζ xl.1 xl.2) (nextC σ C w ζ v xl.1 xl.2)
          (fun U => B (low U + C)))).card : ℚ) ≤
      ((A - 1 : ℕ) : ℚ) ^ t * (Fintype.card K : ℚ) + (D.card : ℚ) ^ t * ((s + t : ℕ) : ℚ) := by
    exact_mod_cast h
  rw [div_le_iff₀ (mul_pos hn hq), div_pow]
  refine h'.trans (le_of_eq ?_)
  field_simp

end Rounds
