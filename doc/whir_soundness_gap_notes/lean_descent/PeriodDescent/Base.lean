/-
The base bound: Lemma 3.2 of note 37 (`37-dimension-induction.md`), which is the argument of
note 04 Theorem 1.2 for the whole code, in the form used by Theorem R of note 46 (the number
`B_{j_0}`).

A level problem: `n` points `D`, a map `ℓ` on them whose fibres have at most `m` points, a word
`v` that may be blank, and polynomials `P` of degree at most `κ` with
`#{x ∈ D : v(x) = P(ℓ(x))} ≥ A`. Then the number `L` of such polynomials satisfies
`L ∏_{i ≤ κ} (A - m i) ≤ ∏_{i ≤ κ} (n - m i)`.

* `pinned_bound`, `list_bound_nat`: the same for any family of functions on the quotient two of
  which never agree on `κ + 1` points (no linearity is used), by the induction of the note: pin the
  members at one more point of the quotient at each step. The affine spaces of the note are the sets
  of members with prescribed values at `s` points.
* `base_bound_nat`, `base_bound`: for polynomials, in `ℕ` and as the product of the note in `ℚ`.
* `ordinary_bound`: the case `ℓ = X`, `m = 1`: at most `∏_{i < k} (n - i) / (T - i)` polynomials of
  degree `< k` agree with a word on `T` of `n` points. This is note 04 Theorem 1.2 for the whole
  code (`r = k`).
* `collinear_bound`: note 04 Theorem 1.2 for `r = 1`: at most `(n - k + 1) / (T - k + 1)` members
  on a line. The general `r` (an affine space of dimension `r` of the code) is in `Affine.lean`.
-/
import Mathlib

open Finset Polynomial
open scoped Classical

namespace PeriodDescent

/-! ### The arithmetic of one step -/

/-- `(n - z) / (A - z)` increases with `z`, cross-multiplied, with truncated subtraction. -/
theorem step_arith (L A n z z' P Q : ℕ) (hz : z ≤ z') (hAn : A ≤ n)
    (h : L * (A - z) * P ≤ (n - z) * Q) : L * (A - z') * P ≤ (n - z') * Q := by
  rcases Nat.lt_or_ge z' A with hlt | hge
  · obtain ⟨d, rfl⟩ : ∃ d, z' = z + d := ⟨z' - z, by omega⟩
    obtain ⟨a, rfl⟩ : ∃ a, A = z + d + a := ⟨A - (z + d), by omega⟩
    obtain ⟨b, rfl⟩ : ∃ b, n = z + d + a + b := ⟨n - (z + d + a), by omega⟩
    have e1 : z + d + a - z = a + d := by omega
    have e2 : z + d + a - (z + d) = a := by omega
    have e3 : z + d + a + b - z = a + b + d := by omega
    have e4 : z + d + a + b - (z + d) = a + b := by omega
    rw [e1, e3] at h
    rw [e2, e4]
    have hpos : 0 < a + b + d := by omega
    refine Nat.le_of_mul_le_mul_left ?_ hpos
    have h1 : (a + b + d) * a ≤ (a + b) * (a + d) := by
      have : (a + b) * (a + d) = (a + b + d) * a + b * d := by ring
      omega
    calc (a + b + d) * (L * a * P) = (L * P) * ((a + b + d) * a) := by ring
      _ ≤ (L * P) * ((a + b) * (a + d)) := Nat.mul_le_mul_left _ h1
      _ = (a + b) * (L * (a + d) * P) := by ring
      _ ≤ (a + b) * ((a + b + d) * Q) := Nat.mul_le_mul_left _ h
      _ = (a + b + d) * ((a + b) * Q) := by ring
  · rw [Nat.sub_eq_zero_of_le hge]
    simp

/-! ### The pinning induction, for any family with the interpolation property -/

section Abstract

variable {α β γ V : Type*}

/-- The number of points of `X` where the word `v` is defined and equal to the value of the member
`c` at the image point. -/
noncomputable def agr (X : Finset α) (π : α → β) (val : γ → β → V) (v : α → Option V) (c : γ) : ℕ :=
  (X.filter (fun x => v x = some (val c (π x)))).card

theorem agr_le_card (X : Finset α) (π : α → β) (val : γ → β → V) (v : α → Option V) (c : γ) :
    agr X π val v c ≤ X.card :=
  Finset.card_filter_le _ _

/-- The induction of note 37 Lemma 3.2. The members of `S` take the same values at the `s` points
of `Y0`; two members that agree at `κ + 1` points of the quotient are equal; the fibres of `π`
have at most `m` points; every member agrees with the word at `A` points or more. -/
theorem pinned_bound (X : Finset α) (π : α → β) (val : γ → β → V) (v : α → Option V)
    (κ m A : ℕ) (hfib : ∀ y, (X.filter (fun x => π x = y)).card ≤ m) :
    ∀ (r s : ℕ), s + r = κ + 1 → ∀ (Y0 : Finset β) (S : Finset γ), Y0.card = s →
      Y0 ⊆ X.image π →
      (∀ c ∈ S, ∀ c' ∈ S, ∀ Y : Finset β, Y ⊆ X.image π → κ + 1 ≤ Y.card →
        (∀ y ∈ Y, val c y = val c' y) → c = c') →
      (∀ c ∈ S, A ≤ agr X π val v c) →
      (∀ c ∈ S, ∀ c' ∈ S, ∀ y ∈ Y0, val c y = val c' y) →
      S.card * ∏ i ∈ Finset.Ico s (κ + 1), (A - m * i)
        ≤ ∏ i ∈ Finset.Ico s (κ + 1), (X.card - m * i) := by
  intro r
  induction r with
  | zero =>
    intro s hs Y0 S hY0 hY0X hdet _ hpin
    have hs' : s = κ + 1 := by omega
    subst hs'
    have h1 : S.card ≤ 1 :=
      Finset.card_le_one.mpr fun c hc c' hc' =>
        hdet c hc c' hc' Y0 hY0X (by omega) (hpin c hc c' hc')
    simpa using h1
  | succ r ih =>
    intro s hs Y0 S hY0 hY0X hdet hagr hpin
    have hsκ : s < κ + 1 := by omega
    rcases S.eq_empty_or_nonempty with hS | ⟨c0, hc0⟩
    · subst hS
      simp
    have hAn : A ≤ X.card := (hagr c0 hc0).trans (agr_le_card X π val v c0)
    -- the points over `Y0`
    set Z : Finset α := X.filter (fun x => π x ∈ Y0) with hZ
    have hZX : Z ⊆ X := Finset.filter_subset _ _
    have hz : Z.card ≤ m * s := by
      have h1 : Z.card = ∑ y ∈ Y0, (Z.filter (fun x => π x = y)).card :=
        Finset.card_eq_sum_card_fiberwise fun x hx => (Finset.mem_filter.mp hx).2
      have h2 : ∀ y ∈ Y0, (Z.filter (fun x => π x = y)).card ≤ m := fun y _ =>
        (Finset.card_le_card (Finset.filter_subset_filter _ hZX)).trans (hfib y)
      have h3 := Finset.sum_le_card_nsmul Y0 _ m h2
      rw [h1]
      calc ∑ y ∈ Y0, (Z.filter (fun x => π x = y)).card ≤ Y0.card • m := h3
        _ = m * s := by rw [hY0, smul_eq_mul, mul_comm]
    have hcardXZ : (X \ Z).card = X.card - Z.card := by
      have := Finset.card_sdiff_add_card_eq_card hZX
      omega
    -- one more pin at every point off `Z`
    have hx : ∀ x ∈ X \ Z,
        (S.filter (fun c => v x = some (val c (π x)))).card
          * ∏ i ∈ Finset.Ico (s + 1) (κ + 1), (A - m * i)
          ≤ ∏ i ∈ Finset.Ico (s + 1) (κ + 1), (X.card - m * i) := by
      intro x hx
      have hxZ : π x ∉ Y0 := by
        intro h
        exact (Finset.mem_sdiff.mp hx).2 (Finset.mem_filter.mpr ⟨(Finset.mem_sdiff.mp hx).1, h⟩)
      refine ih (s + 1) (by omega) (insert (π x) Y0) _ ?_ ?_ ?_ ?_ ?_
      · rw [Finset.card_insert_of_notMem hxZ, hY0]
      · exact Finset.insert_subset
          (Finset.mem_image_of_mem π (Finset.mem_sdiff.mp hx).1) hY0X
      · intro c hc c' hc'
        exact hdet c (Finset.mem_filter.mp hc).1 c' (Finset.mem_filter.mp hc').1
      · intro c hc
        exact hagr c (Finset.mem_filter.mp hc).1
      · intro c hc c' hc' y hy
        rcases Finset.mem_insert.mp hy with rfl | hy'
        · have h1 := (Finset.mem_filter.mp hc).2
          have h2 := (Finset.mem_filter.mp hc').2
          exact Option.some.inj (h1.symm.trans h2)
        · exact hpin c (Finset.mem_filter.mp hc).1 c' (Finset.mem_filter.mp hc').1 y hy'
    -- double counting
    have hdc : ∑ x ∈ X \ Z, (S.filter (fun c => v x = some (val c (π x)))).card
        = ∑ c ∈ S, ((X \ Z).filter (fun x => v x = some (val c (π x)))).card := by
      simp only [Finset.card_filter]
      exact Finset.sum_comm
    have hmem : ∀ c ∈ S,
        A - Z.card ≤ ((X \ Z).filter (fun x => v x = some (val c (π x)))).card := by
      intro c hc
      have hsub : X.filter (fun x => v x = some (val c (π x)))
          ⊆ (X \ Z).filter (fun x => v x = some (val c (π x))) ∪ Z := by
        intro x hx
        by_cases hxz : x ∈ Z
        · exact Finset.mem_union_right _ hxz
        · exact Finset.mem_union_left _ (Finset.mem_filter.mpr
            ⟨Finset.mem_sdiff.mpr ⟨(Finset.mem_filter.mp hx).1, hxz⟩, (Finset.mem_filter.mp hx).2⟩)
      have h1 := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
      have h2 := hagr c hc
      unfold agr at h2
      omega
    have hcount : S.card * (A - Z.card)
        ≤ ∑ x ∈ X \ Z, (S.filter (fun c => v x = some (val c (π x)))).card := by
      rw [hdc]
      calc S.card * (A - Z.card) = ∑ _c ∈ S, (A - Z.card) := by
            rw [Finset.sum_const, smul_eq_mul]
        _ ≤ _ := Finset.sum_le_sum hmem
    have hkey : S.card * (A - Z.card) * ∏ i ∈ Finset.Ico (s + 1) (κ + 1), (A - m * i)
        ≤ (X.card - Z.card) * ∏ i ∈ Finset.Ico (s + 1) (κ + 1), (X.card - m * i) := by
      calc S.card * (A - Z.card) * ∏ i ∈ Finset.Ico (s + 1) (κ + 1), (A - m * i)
          ≤ (∑ x ∈ X \ Z, (S.filter (fun c => v x = some (val c (π x)))).card)
              * ∏ i ∈ Finset.Ico (s + 1) (κ + 1), (A - m * i) := Nat.mul_le_mul_right _ hcount
        _ = ∑ x ∈ X \ Z, (S.filter (fun c => v x = some (val c (π x)))).card
              * ∏ i ∈ Finset.Ico (s + 1) (κ + 1), (A - m * i) := Finset.sum_mul _ _ _
        _ ≤ ∑ _x ∈ X \ Z, ∏ i ∈ Finset.Ico (s + 1) (κ + 1), (X.card - m * i) :=
            Finset.sum_le_sum hx
        _ = (X.card - Z.card) * ∏ i ∈ Finset.Ico (s + 1) (κ + 1), (X.card - m * i) := by
            rw [Finset.sum_const, smul_eq_mul, hcardXZ]
    have hfinal := step_arith S.card A X.card Z.card (m * s) _ _ hz hAn hkey
    rw [Finset.prod_eq_prod_Ico_succ_bot hsκ, Finset.prod_eq_prod_Ico_succ_bot hsκ, ← mul_assoc]
    exact hfinal

/-- **Note 37 Lemma 3.2, for any family with the interpolation property**: two members that agree
at `κ + 1` points of the quotient `π(X)` are equal. -/
theorem list_bound_nat (X : Finset α) (π : α → β) (val : γ → β → V) (v : α → Option V)
    (κ m A : ℕ) (hfib : ∀ y, (X.filter (fun x => π x = y)).card ≤ m) (S : Finset γ)
    (hdet : ∀ c ∈ S, ∀ c' ∈ S, ∀ Y : Finset β, Y ⊆ X.image π → κ + 1 ≤ Y.card →
      (∀ y ∈ Y, val c y = val c' y) → c = c')
    (hagr : ∀ c ∈ S, A ≤ agr X π val v c) :
    S.card * ∏ i ∈ Finset.range (κ + 1), (A - m * i)
      ≤ ∏ i ∈ Finset.range (κ + 1), (X.card - m * i) := by
  have h := pinned_bound X π val v κ m A hfib (κ + 1) 0 (by omega) ∅ S rfl
    (Finset.empty_subset _) hdet hagr
    (fun _ _ _ _ y hy => absurd hy (Finset.notMem_empty y))
  rwa [← Finset.range_eq_Ico] at h

end Abstract

/-! ### Polynomials -/

variable {F : Type*} [Field F]

/-- The agreement of `P ∘ ℓ` with the word `v` on `D`: the number of `x ∈ D` at which `v` is
defined and equal to `P(ℓ(x))`. -/
noncomputable def polyAgr (D : Finset F) (ℓ : F[X]) (v : F → Option F) (P : F[X]) : ℕ :=
  (D.filter (fun x => v x = some (P.eval (ℓ.eval x)))).card

theorem polyAgr_le_card (D : Finset F) (ℓ : F[X]) (v : F → Option F) (P : F[X]) :
    polyAgr D ℓ v P ≤ D.card :=
  Finset.card_filter_le _ _

/-- Two polynomials of degree at most `κ` that agree at `κ + 1` points are equal. -/
theorem eq_of_natDegree_le_of_eval_eq {P Q : F[X]} {κ : ℕ} (hP : P.natDegree ≤ κ)
    (hQ : Q.natDegree ≤ κ) (Y : Finset F) (hY : κ + 1 ≤ Y.card)
    (h : ∀ y ∈ Y, P.eval y = Q.eval y) : P = Q := by
  refine Polynomial.eq_of_degree_sub_lt_of_eval_finset_eq Y ?_ h
  have h1 : (P - Q).natDegree ≤ κ := (Polynomial.natDegree_sub_le P Q).trans (max_le hP hQ)
  have h2 : (P - Q).degree ≤ (κ : WithBot ℕ) := Polynomial.degree_le_of_natDegree_le h1
  have h3 : (κ : WithBot ℕ) < (Y.card : WithBot ℕ) := by exact_mod_cast hY
  exact lt_of_le_of_lt h2 h3

/-- **Note 37 Lemma 3.2**, cross-multiplied in `ℕ` (truncated subtraction): a level problem with
fibres of at most `m` points has `L` members with `L ∏_{i ≤ κ} (A - m i) ≤ ∏_{i ≤ κ} (n - m i)`. -/
theorem base_bound_nat (D : Finset F) (ℓ : F[X]) (v : F → Option F) (κ m A : ℕ)
    (hfib : ∀ y, (D.filter (fun x => ℓ.eval x = y)).card ≤ m)
    (S : Finset F[X]) (hdeg : ∀ P ∈ S, P.natDegree ≤ κ) (hagr : ∀ P ∈ S, A ≤ polyAgr D ℓ v P) :
    S.card * ∏ i ∈ Finset.range (κ + 1), (A - m * i)
      ≤ ∏ i ∈ Finset.range (κ + 1), (D.card - m * i) :=
  list_bound_nat D (fun x => ℓ.eval x) (fun (P : F[X]) y => P.eval y) v κ m A hfib S
    (fun P hP Q hQ Y _ hY h => eq_of_natDegree_le_of_eval_eq (hdeg P hP) (hdeg Q hQ) Y hY h) hagr

/-- **Note 37 Lemma 3.2**, as stated: if `A > m κ`, a level problem has at most
`∏_{i = 0}^{κ} (n - m i) / (A - m i)` members. -/
theorem base_bound (D : Finset F) (ℓ : F[X]) (v : F → Option F) (κ m A : ℕ)
    (hfib : ∀ y, (D.filter (fun x => ℓ.eval x = y)).card ≤ m)
    (S : Finset F[X]) (hdeg : ∀ P ∈ S, P.natDegree ≤ κ) (hagr : ∀ P ∈ S, A ≤ polyAgr D ℓ v P)
    (hA : m * κ < A) (hn : m * κ ≤ D.card) :
    (S.card : ℚ) ≤ ∏ i ∈ Finset.range (κ + 1), (((D.card : ℚ) - m * i) / ((A : ℚ) - m * i)) := by
  have h := base_bound_nat D ℓ v κ m A hfib S hdeg hagr
  have hi : ∀ i ∈ Finset.range (κ + 1), m * i ≤ m * κ := fun i hi =>
    Nat.mul_le_mul_left m (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi))
  have hden : ∀ i ∈ Finset.range (κ + 1), (0 : ℚ) < (A : ℚ) - m * i := by
    intro i hi'
    have h1 : m * i < A := lt_of_le_of_lt (hi i hi') hA
    have h2 : ((m * i : ℕ) : ℚ) < (A : ℚ) := by exact_mod_cast h1
    push_cast at h2
    linarith
  have e1 : ∏ i ∈ Finset.range (κ + 1), ((A : ℚ) - m * i)
      = ((∏ i ∈ Finset.range (κ + 1), (A - m * i) : ℕ) : ℚ) := by
    rw [Nat.cast_prod]
    refine Finset.prod_congr rfl fun i hi' => ?_
    rw [Nat.cast_sub ((hi i hi').trans hA.le)]
    push_cast
    rfl
  have e2 : ∏ i ∈ Finset.range (κ + 1), ((D.card : ℚ) - m * i)
      = ((∏ i ∈ Finset.range (κ + 1), (D.card - m * i) : ℕ) : ℚ) := by
    rw [Nat.cast_prod]
    refine Finset.prod_congr rfl fun i hi' => ?_
    rw [Nat.cast_sub ((hi i hi').trans hn)]
    push_cast
    rfl
  rw [Finset.prod_div_distrib, le_div_iff₀ (Finset.prod_pos hden), e1, e2]
  exact_mod_cast h

/-- **Note 04 Theorem 1.2 for the whole code** (`r = k`): at most
`∏_{i < k} (n - i) / (T - i)` polynomials of degree `< k` agree with a word on at least `T` of the
`n` points of `D`, for `k ≤ T`. Here `D` is any finite set of points of any field. -/
theorem ordinary_bound (D : Finset F) (w : F → F) (k T : ℕ) (hk : 1 ≤ k) (hkT : k ≤ T)
    (hTn : T ≤ D.card) (S : Finset F[X]) (hdeg : ∀ P ∈ S, P.degree < k)
    (hagr : ∀ P ∈ S, T ≤ (D.filter (fun x => P.eval x = w x)).card) :
    (S.card : ℚ) ≤ ∏ i ∈ Finset.range k, (((D.card : ℚ) - i) / ((T : ℚ) - i)) := by
  obtain ⟨κ, rfl⟩ : ∃ κ, k = κ + 1 := ⟨k - 1, by omega⟩
  have hfib : ∀ y, (D.filter (fun x => (X : F[X]).eval x = y)).card ≤ 1 := by
    intro y
    refine Finset.card_le_one.mpr fun a ha b hb => ?_
    have h1 := (Finset.mem_filter.mp ha).2
    have h2 := (Finset.mem_filter.mp hb).2
    rw [eval_X] at h1 h2
    rw [h1, h2]
  have hdeg' : ∀ P ∈ S, P.natDegree ≤ κ := by
    intro P hP
    have h1 := hdeg P hP
    rcases eq_or_ne P 0 with rfl | hP0
    · simp
    · have h2 := (Polynomial.natDegree_lt_iff_degree_lt hP0).mpr h1
      omega
  have hagr' : ∀ P ∈ S, T ≤ polyAgr D X (fun x => some (w x)) P := by
    intro P hP
    refine (hagr P hP).trans (Finset.card_le_card fun x hx => ?_)
    rw [Finset.mem_filter] at hx ⊢
    refine ⟨hx.1, ?_⟩
    rw [eval_X, hx.2]
  have h := base_bound D X (fun x => some (w x)) κ 1 T hfib S hdeg' hagr' (by omega) (by omega)
  simpa using h

/-- **Note 04 Theorem 1.2 for `r = 1`: collinear members.** The polynomials `c₀ + t u` on a line
(`u ≠ 0` of degree `< k`) that agree with a word on at least `T` of the `n` points of `D` number
at most `(n - k + 1) / (T - k + 1)`, cross-multiplied. -/
theorem collinear_bound (D : Finset F) (w : F → Option F) (k T : ℕ) (c0 u : F[X]) (hu : u ≠ 0)
    (hk : u.natDegree < k) (S : Finset F[X]) (hS : ∀ P ∈ S, ∃ t : F, P = c0 + C t * u)
    (hagr : ∀ P ∈ S, T ≤ polyAgr D X w P) :
    S.card * (T - (k - 1)) ≤ D.card - (k - 1) := by
  rcases S.eq_empty_or_nonempty with hS0 | ⟨P0, hP0⟩
  · subst hS0
    simp
  have hTn : T ≤ D.card := (hagr P0 hP0).trans (polyAgr_le_card D X w P0)
  -- the zeros of the direction
  have hZ : (D.filter (fun x => u.eval x = 0)).card ≤ k - 1 := by
    have h1 : D.filter (fun x => u.eval x = 0) ⊆ u.roots.toFinset := by
      intro x hx
      exact Multiset.mem_toFinset.mpr ((mem_roots hu).mpr (Finset.mem_filter.mp hx).2)
    have h2 := (Finset.card_le_card h1).trans
      ((Multiset.toFinset_card_le _).trans (card_roots' u))
    omega
  have hcard : (D.filter (fun x => u.eval x ≠ 0)).card
      = D.card - (D.filter (fun x => u.eval x = 0)).card := by
    have h3 : (D.filter (fun x => u.eval x = 0)).card + (D.filter (fun x => u.eval x ≠ 0)).card
        = D.card := Finset.card_filter_add_card_filter_not _
    omega
  -- off the zeros, a point pins a member
  have h := list_bound_nat (D.filter (fun x => u.eval x ≠ 0)) (fun x : F => x)
    (fun (P : F[X]) y => P.eval y) w 0 1 (T - (D.filter (fun x => u.eval x = 0)).card)
    (fun y => Finset.card_le_one.mpr fun a ha b hb => by
      rw [(Finset.mem_filter.mp ha).2, (Finset.mem_filter.mp hb).2]) S ?_ ?_
  · simp only [zero_add, Finset.prod_range_one, mul_zero, Nat.sub_zero] at h
    rw [hcard] at h
    have h' := step_arith S.card T D.card _ (k - 1) 1 1 hZ hTn (by simpa using h)
    simpa using h'
  · intro P hP Q hQ Y hY hYc hPQ
    obtain ⟨y, hy⟩ := Finset.card_pos.mp (by omega : 0 < Y.card)
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp (hY hy)
    have hux := (Finset.mem_filter.mp hx).2
    obtain ⟨t, rfl⟩ := hS P hP
    obtain ⟨t', rfl⟩ := hS Q hQ
    have h1 := hPQ x hy
    simp only [eval_add, eval_mul, eval_C] at h1
    have h2 : t = t' := mul_right_cancel₀ hux (add_left_cancel h1)
    rw [h2]
  · intro P hP
    have h1 := hagr P hP
    unfold polyAgr at h1
    show T - (D.filter (fun x => u.eval x = 0)).card
      ≤ ((D.filter (fun x => u.eval x ≠ 0)).filter (fun x => w x = some (P.eval x))).card
    have hsub : D.filter (fun x => w x = some (P.eval ((X : F[X]).eval x)))
        ⊆ (D.filter (fun x => u.eval x ≠ 0)).filter (fun x => w x = some (P.eval x))
          ∪ D.filter (fun x => u.eval x = 0) := by
      intro x hx
      rw [Finset.mem_filter, eval_X] at hx
      by_cases hux : u.eval x = 0
      · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hx.1, hux⟩)
      · exact Finset.mem_union_left _
          (Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨hx.1, hux⟩, hx.2⟩)
    have h2 := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
    omega

end PeriodDescent
