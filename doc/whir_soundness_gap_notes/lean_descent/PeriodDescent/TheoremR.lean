/-
Theorem R of note 46 (`46-referee-notes-37-39.md`, section 1.5), which is note 39 Theorem 1.3 with
the base case of note 37 Lemma 3.2: the period descent, for polynomials over a field of
characteristic two on a subspace domain.

* `BadTriple`: three polynomials whose function `(P_c - P_a) / (P_b - P_a)` is constant or
  unchanged by `Y ↦ Y + a'` for a nonzero value `a'` of the level polynomial on `D`.
* `PLsub`: the hypothesis PL`(f, j₀)` as the referee states it, over the subspaces `U ⊆ D` with
  `2^j` elements, `j < j₀`, and the level polynomial `L_U`. `PL`: the same over the level
  polynomials reached by the descent (`IsLevel`); `PL_of_PLsub`: the first implies the second.
* `baseB`: the number `B_{j₀}`. `baseB_zero`: it is `n / Δ` when the degree bound is `0`.
* `theoremR_gen`: the theorem with any constant `G ≥ C(f, 2)`, `f + 1 ≤ 4 G`.
* `theoremR`: **Theorem R**: under `PLsub`, every word has at most
  `C(f + 1, 3)^{j₀} 2^(N j₀ - j₀ (j₀ - 1) / 2) (B_{j₀} + 1)` polynomials of degree `< k` agreeing
  with it on at least `T` points of `D`.
* `theoremR_top`: the case in which the degree bound of the level `j₀` is `0` (`k ≤ 2^{j₀}`):
  the bound of note 39 Theorem 1.3, `C(f + 1, 3)^{j₀} 2^(N j₀ - j₀ (j₀ - 1) / 2) (n / Δ + 1)`.
* `theoremR_sharp`: the same with `C(f, 2)` in place of `C(f + 1, 3)` (not in the notes).
-/
import PeriodDescent.Step
import PeriodDescent.Induction

open Polynomial Finset
open scoped Classical

namespace PeriodDescent

variable {F : Type*} [Field F]

/-! ### The hypothesis -/

/-- Three polynomials are a bad triple for the level polynomial `ℓ`: the function
`(P_c - P_a) / (P_b - P_a)` is constant (the three are collinear), or it is unchanged by
`Y ↦ Y + a'` for some nonzero value `a'` of `ℓ` on `D`. -/
def BadTriple (D : Finset F) (ℓ : F[X]) (Pa Pb Pc : F[X]) : Prop :=
  (∃ t : F, Pc - Pa = C t * (Pb - Pa)) ∨
    ∃ a' ∈ D.image (fun x => ℓ.eval x), a' ≠ 0 ∧ Periodic a' (Pb - Pa) (Pc - Pa)

/-- The hypothesis PL`(f, j₀)` over the level problems reached by the descent: at every level
`j < j₀`, every list of more than `f` members contains a bad triple. -/
def PL (D : Finset F) (k Δ f j0 : ℕ) : Prop :=
  ∀ p : LevelPb D k, p.j < j0 → ∀ S : Finset F[X], (∀ P ∈ S, p.Mem Δ P) → f < S.card →
    ∃ Pa ∈ S, ∃ Pb ∈ S, ∃ Pc ∈ S, Pa ≠ Pb ∧ Pa ≠ Pc ∧ Pb ≠ Pc ∧ BadTriple D p.ℓ Pa Pb Pc

/-- **The hypothesis PL`(f, j₀)` of Theorem R.** For every `j < j₀`, every subspace `U ⊆ D` with
`2^j` elements, every degree bound `κ ≤ ⌊(k - 1) / 2^j⌋` (`κ = k - 1` if `j = 0`) and every word
`v : D → F ∪ {⊥}`: every set of more than `f` polynomials `P` of degree at most `κ` with
`#{x ∈ D : v(x) = P(L_U(x))} ≥ 2^j κ + Δ` contains a bad triple. -/
def PLsub (D : Finset F) (k Δ f j0 : ℕ) : Prop :=
  ∀ j < j0, ∀ U : Finset F, U ⊆ D → IsSubspace U → U.card = 2 ^ j →
    ∀ κ : ℕ, κ ≤ (k - 1) / 2 ^ j → (j = 0 → κ = k - 1) → ∀ v : F → Option F,
      ∀ S : Finset F[X],
        (∀ P ∈ S, P.natDegree ≤ κ ∧ 2 ^ j * κ + Δ ≤ polyAgr D (subPoly U) v P) → f < S.card →
        ∃ Pa ∈ S, ∃ Pb ∈ S, ∃ Pc ∈ S, Pa ≠ Pb ∧ Pa ≠ Pc ∧ Pb ≠ Pc ∧
          BadTriple D (subPoly U) Pa Pb Pc

theorem PL_of_PLsub [CharP F 2] {D : Finset F} (hD : IsSubspace D) {k Δ f j0 : ℕ}
    (h : PLsub D k Δ f j0) : PL D k Δ f j0 := by
  intro p hp S hS hcard
  obtain ⟨U, hUD, hU, hUc, hℓ⟩ := p.hℓ.exists_subspace hD
  have h1 := h p.j hp U hUD hU hUc p.κ p.hκ p.hκ0 p.v S (by rw [← hℓ]; exact hS) hcard
  rw [← hℓ] at h1
  exact h1

/-! ### The base bound `B_{j₀}` -/

/-- The number `B_{j₀} = max_{0 ≤ κ ≤ κmax} ∏_{i = 0}^{κ} (n - m i) / (Δ + m (κ - i))` of
Theorem R, with `m = 2^{j₀}` and `κmax = ⌊(k - 1) / 2^{j₀}⌋`. -/
noncomputable def baseB (n Δ m κmax : ℕ) : ℚ :=
  (Finset.range (κmax + 1)).sup' ⟨0, Finset.mem_range.mpr (Nat.succ_pos _)⟩
    (fun κ => ∏ i ∈ Finset.range (κ + 1),
      (((n : ℚ) - (m : ℚ) * i) / ((Δ : ℚ) + (m : ℚ) * ((κ : ℚ) - i))))

/-- For the degree bound `0`, `B = n / Δ`. -/
theorem baseB_zero (n Δ m : ℕ) : baseB n Δ m 0 = (n : ℚ) / Δ := by
  unfold baseB
  simp

theorem baseB_nonneg (n Δ m κmax : ℕ) : 0 ≤ baseB n Δ m κmax := by
  have h1 : (0 : ℚ) ≤ ∏ i ∈ Finset.range (0 + 1),
      (((n : ℚ) - (m : ℚ) * i) / ((Δ : ℚ) + (m : ℚ) * (((0 : ℕ) : ℚ) - i))) := by
    simp only [zero_add, Finset.prod_range_one, Nat.cast_zero, mul_zero, sub_zero, add_zero]
    positivity
  exact h1.trans (Finset.le_sup' (fun κ => ∏ i ∈ Finset.range (κ + 1),
      (((n : ℚ) - (m : ℚ) * i) / ((Δ : ℚ) + (m : ℚ) * ((κ : ℚ) - i))))
    (Finset.mem_range.mpr (Nat.succ_pos κmax)))

section CharTwo

variable [CharP F 2]

/-- The lists of the level `j₀` have at most `B_{j₀}` members (note 37 Lemma 3.2). -/
theorem LevelPb.card_le_baseB {D : Finset F} (hD : IsSubspace D) {N k T : ℕ}
    (hN : D.card = 2 ^ N) (hkT : k ≤ T) (hTn : T ≤ 2 ^ N) (p : LevelPb D k)
    (S : Finset F[X]) (hS : ∀ P ∈ S, p.Mem (T - k + 1) P) :
    (S.card : ℚ) ≤ baseB (2 ^ N) (T - k + 1) (2 ^ p.j) ((k - 1) / 2 ^ p.j) := by
  have hmκ : 2 ^ p.j * p.κ ≤ k - 1 :=
    (Nat.mul_le_mul_left _ p.hκ).trans (Nat.mul_div_le _ _)
  have h1 := base_bound D p.ℓ p.v p.κ (2 ^ p.j) (2 ^ p.j * p.κ + (T - k + 1))
    (p.hℓ.fiber_card_le hD) S (fun P hP => (hS P hP).1) (fun P hP => (hS P hP).2)
    (by omega) (by rw [hN]; omega)
  have h2 : ∏ i ∈ Finset.range (p.κ + 1),
        (((D.card : ℚ) - ((2 ^ p.j : ℕ) : ℚ) * i)
          / (((2 ^ p.j * p.κ + (T - k + 1) : ℕ) : ℚ) - ((2 ^ p.j : ℕ) : ℚ) * i))
      = ∏ i ∈ Finset.range (p.κ + 1),
        ((((2 ^ N : ℕ) : ℚ) - ((2 ^ p.j : ℕ) : ℚ) * i)
          / (((T - k + 1 : ℕ) : ℚ) + ((2 ^ p.j : ℕ) : ℚ) * ((p.κ : ℚ) - i))) := by
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [hN]
    congr 1
    push_cast
    ring
  rw [h2] at h1
  exact h1.trans (Finset.le_sup' (fun κ => ∏ i ∈ Finset.range (κ + 1),
      ((((2 ^ N : ℕ) : ℚ) - ((2 ^ p.j : ℕ) : ℚ) * i)
        / (((T - k + 1 : ℕ) : ℚ) + ((2 ^ p.j : ℕ) : ℚ) * ((κ : ℚ) - i))))
    (Finset.mem_range.mpr (Nat.lt_succ_of_le p.hκ)))

/-- The ordinary list problem as a level problem of level `0`: `ℓ = X`, degree bound `k - 1`, and
the word without blanks. -/
noncomputable def LevelPb.ofWord (D : Finset F) (k : ℕ) (w : F → F) : LevelPb D k where
  j := 0
  ℓ := X
  κ := k - 1
  v := fun x => some (w x)
  hℓ := IsLevel.zero
  hκ := by simp
  hκ0 := fun _ => rfl

omit [CharP F 2] in
/-- A polynomial of degree `< k` that agrees with `w` on at least `T` points of `D` is a member of
the level-`0` problem at slack `Δ = T - k + 1`. -/
theorem LevelPb.ofWord_mem (D : Finset F) {k T : ℕ} {w : F → F} (hk : 1 ≤ k) (hkT : k ≤ T)
    {P : F[X]} (hdeg : P.degree < k)
    (hagr : T ≤ (D.filter (fun x => P.eval x = w x)).card) :
    (LevelPb.ofWord D k w).Mem (T - k + 1) P := by
  constructor
  · show P.natDegree ≤ k - 1
    rcases eq_or_ne P 0 with rfl | hP0
    · simp
    · have h2 := (Polynomial.natDegree_lt_iff_degree_lt hP0).mpr hdeg
      omega
  · show 2 ^ 0 * (k - 1) + (T - k + 1) ≤ polyAgr D X (fun x => some (w x)) P
    have h1 : T ≤ polyAgr D X (fun x => some (w x)) P := by
      refine hagr.trans (Finset.card_le_card fun x hx => ?_)
      rw [Finset.mem_filter] at hx ⊢
      refine ⟨hx.1, ?_⟩
      rw [eval_X, hx.2]
    omega

/-- Below the top level a bad triple is periodic for some nonzero direction: a constant function
has every period. -/
theorem BadTriple.exists_dir {D : Finset F} (hD : IsSubspace D) {N j : ℕ} {ℓ Pa Pb Pc : F[X]}
    (h : BadTriple D ℓ Pa Pb Pc) (hN : D.card = 2 ^ N) (hℓ : IsLevel D j ℓ) (hj : j < N) :
    ∃ a' ∈ (D.image (fun x => ℓ.eval x)).erase 0, Periodic a' (Pb - Pa) (Pc - Pa) := by
  rcases h with ⟨t, ht⟩ | ⟨a', ha', ha'0, hper⟩
  · obtain ⟨a', ha', ha'0⟩ := hℓ.exists_dir hD hN hj
    refine ⟨a', Finset.mem_erase.mpr ⟨ha'0, ha'⟩, ?_⟩
    rw [ht]
    exact periodic_of_const a' _ t
  · exact ⟨a', Finset.mem_erase.mpr ⟨ha'0, ha'⟩, hper⟩

/-- **Theorem R with a general constant.** `G` is any number with `C(f, 2) ≤ G` and
`f + 1 ≤ 4 G`, and the hypothesis is `PL` over the level problems reached by the descent. The
conclusion carries the `- 1` that the recursion gives. -/
theorem theoremR_gen (D : Finset F) (hD : IsSubspace D) (N k T f j0 G : ℕ)
    (hN : D.card = 2 ^ N) (hk : 1 ≤ k) (hkT : k ≤ T) (hTn : T ≤ 2 ^ N)
    (hGf : f.choose 2 ≤ G) (hfG : f + 1 ≤ 4 * G) (hj0 : j0 + 1 ≤ N)
    (hPL : PL D k (T - k + 1) f j0)
    (w : F → F) (S : Finset F[X]) (hdeg : ∀ P ∈ S, P.degree < k)
    (hagr : ∀ P ∈ S, T ≤ (D.filter (fun x => P.eval x = w x)).card) :
    (S.card : ℚ) + 1 ≤ (G : ℚ) ^ j0 * 2 ^ (N * j0 - j0 * (j0 - 1) / 2)
      * (baseB (2 ^ N) (T - k + 1) (2 ^ j0) ((k - 1) / 2 ^ j0) + 1) := by
  have key := abstract_descent (Pb := LevelPb D k) (C := F[X]) (A := F) (fun p => p.j)
    (fun p => p.Mem (T - k + 1)) (fun p => (D.image (fun x => p.ℓ.eval x)).erase 0)
    (fun _ a c0 c1 c => Periodic a (c1 - c0) (c - c0)) N j0 f G
    ⌊baseB (2 ^ N) (T - k + 1) (2 ^ j0) ((k - 1) / 2 ^ j0)⌋₊ hGf hfG hj0
    (fun p _ => p.hℓ.dirs_card_le hD hN)
    (fun _ _ _ _ _ h => h.swap)
    (fun _ _ _ _ _ h => h.base_swap)
    ?_ ?_ ?_ (LevelPb.ofWord D k w) rfl S
    (fun P hP => LevelPb.ofWord_mem D hk hkT (hdeg P hP) (hagr P hP))
  · have h1 : ((S.card + 1 : ℕ) : ℚ) ≤ ((G ^ j0 * 2 ^ (N * j0 - j0 * (j0 - 1) / 2)
        * (⌊baseB (2 ^ N) (T - k + 1) (2 ^ j0) ((k - 1) / 2 ^ j0)⌋₊ + 1) : ℕ) : ℚ) := by
      exact_mod_cast key
    push_cast at h1
    have h2 : ((⌊baseB (2 ^ N) (T - k + 1) (2 ^ j0) ((k - 1) / 2 ^ j0)⌋₊ : ℕ) : ℚ)
        ≤ baseB (2 ^ N) (T - k + 1) (2 ^ j0) ((k - 1) / 2 ^ j0) :=
      Nat.floor_le (baseB_nonneg _ _ _ _)
    have h3 : (0 : ℚ) ≤ (G : ℚ) ^ j0 * 2 ^ (N * j0 - j0 * (j0 - 1) / 2) := by positivity
    calc (S.card : ℚ) + 1
        ≤ (G : ℚ) ^ j0 * 2 ^ (N * j0 - j0 * (j0 - 1) / 2)
          * ((⌊baseB (2 ^ N) (T - k + 1) (2 ^ j0) ((k - 1) / 2 ^ j0)⌋₊ : ℕ) + 1) := h1
      _ ≤ (G : ℚ) ^ j0 * 2 ^ (N * j0 - j0 * (j0 - 1) / 2)
          * (baseB (2 ^ N) (T - k + 1) (2 ^ j0) ((k - 1) / 2 ^ j0) + 1) :=
          mul_le_mul_of_nonneg_left (by linarith) h3
  · -- the descent step
    intro p _ c0 c1 h0 h1 h01 a ha
    exact p.descent_step hD _ h0 h1 h01 ha
  · -- the hypothesis
    intro p hp S' hS' hcard
    obtain ⟨Pa, hPa, Pb, hPb, Pc, hPc, hab, hac, hbc, hbad⟩ := hPL p hp S' hS' hcard
    exact ⟨Pa, hPa, Pb, hPb, Pc, hPc, hab, hac, hbc, hbad.exists_dir hD hN p.hℓ (by omega)⟩
  · -- the base case
    intro p hp S' hS'
    have h1 := p.card_le_baseB hD hN hkT hTn S' hS'
    rw [hp] at h1
    exact Nat.le_floor h1

/-- **Theorem R of note 46.** Let `F` be a field of characteristic two, `D ⊆ F` a subspace with
`2^N` elements, `1 ≤ k ≤ T ≤ 2^N`, `Δ = T - k + 1`, `f ≥ 2` and `j₀ ≤ N - 1`. Under the hypothesis
PL`(f, j₀)` (`PLsub`), for every word `w : D → F` the number of polynomials of degree `< k` that
agree with `w` on at least `T` points of `D` is at most
`C(f + 1, 3)^{j₀} 2^(N j₀ - j₀ (j₀ - 1) / 2) (B_{j₀} + 1)`. -/
theorem theoremR (D : Finset F) (hD : IsSubspace D) (N k T f j0 : ℕ)
    (hN : D.card = 2 ^ N) (hk : 1 ≤ k) (hkT : k ≤ T) (hTn : T ≤ 2 ^ N) (hf : 2 ≤ f)
    (hj0 : j0 + 1 ≤ N) (hPL : PLsub D k (T - k + 1) f j0)
    (w : F → F) (S : Finset F[X]) (hdeg : ∀ P ∈ S, P.degree < k)
    (hagr : ∀ P ∈ S, T ≤ (D.filter (fun x => P.eval x = w x)).card) :
    (S.card : ℚ) ≤ (((f + 1).choose 3 : ℕ) : ℚ) ^ j0 * 2 ^ (N * j0 - j0 * (j0 - 1) / 2)
      * (baseB (2 ^ N) (T - k + 1) (2 ^ j0) ((k - 1) / 2 ^ j0) + 1) := by
  have h := theoremR_gen D hD N k T f j0 ((f + 1).choose 3) hN hk hkT hTn
    (choose_two_le_choose_three f)
    ((succ_le_four_mul_choose hf).trans (Nat.mul_le_mul_left 4 (choose_two_le_choose_three f)))
    hj0 (PL_of_PLsub hD hPL) w S hdeg hagr
  linarith

/-- **Note 39 Theorem 1.3 at the last level.** If the degree bound of the level `j₀` is `0`, that
is `k ≤ 2^{j₀}`, then `B_{j₀} = n / Δ` and the bound is
`C(f + 1, 3)^{j₀} 2^(N j₀ - j₀ (j₀ - 1) / 2) (n / Δ + 1)`. -/
theorem theoremR_top (D : Finset F) (hD : IsSubspace D) (N k T f j0 : ℕ)
    (hN : D.card = 2 ^ N) (hk : 1 ≤ k) (hkT : k ≤ T) (hTn : T ≤ 2 ^ N) (hf : 2 ≤ f)
    (hj0 : j0 + 1 ≤ N) (hkj : k ≤ 2 ^ j0) (hPL : PLsub D k (T - k + 1) f j0)
    (w : F → F) (S : Finset F[X]) (hdeg : ∀ P ∈ S, P.degree < k)
    (hagr : ∀ P ∈ S, T ≤ (D.filter (fun x => P.eval x = w x)).card) :
    (S.card : ℚ) ≤ (((f + 1).choose 3 : ℕ) : ℚ) ^ j0 * 2 ^ (N * j0 - j0 * (j0 - 1) / 2)
      * ((2 : ℚ) ^ N / ((T - k + 1 : ℕ) : ℚ) + 1) := by
  have h := theoremR D hD N k T f j0 hN hk hkT hTn hf hj0 hPL w S hdeg hagr
  have h0 : (k - 1) / 2 ^ j0 = 0 := Nat.div_eq_of_lt (by omega)
  rw [h0, baseB_zero, Nat.cast_pow, Nat.cast_ofNat] at h
  exact h

/-- **A sharper constant** (not in the notes): `C(f, 2)` in place of `C(f + 1, 3)`. -/
theorem theoremR_sharp (D : Finset F) (hD : IsSubspace D) (N k T f j0 : ℕ)
    (hN : D.card = 2 ^ N) (hk : 1 ≤ k) (hkT : k ≤ T) (hTn : T ≤ 2 ^ N) (hf : 2 ≤ f)
    (hj0 : j0 + 1 ≤ N) (hPL : PLsub D k (T - k + 1) f j0)
    (w : F → F) (S : Finset F[X]) (hdeg : ∀ P ∈ S, P.degree < k)
    (hagr : ∀ P ∈ S, T ≤ (D.filter (fun x => P.eval x = w x)).card) :
    (S.card : ℚ) ≤ ((f.choose 2 : ℕ) : ℚ) ^ j0 * 2 ^ (N * j0 - j0 * (j0 - 1) / 2)
      * (baseB (2 ^ N) (T - k + 1) (2 ^ j0) ((k - 1) / 2 ^ j0) + 1) := by
  have h := theoremR_gen D hD N k T f j0 (f.choose 2) hN hk hkT hTn le_rfl
    (succ_le_four_mul_choose hf) hj0 (PL_of_PLsub hD hPL) w S hdeg hagr
  linarith

end CharTwo

end PeriodDescent
