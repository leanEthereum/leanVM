module

public import Quantum.Sponge.Database
public import Mathlib.Basic.Real.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Fintype.Perm
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.GCongr
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

@[expose] public section

/-!
# A uniform permutation is good except with small probability

Section 5.3 of Alagic, Carolan, Majenz and Tokat (ePrint 2025/731) conditions on the permutation
`π` of the sponge being good (`PermGood`, Definition 5.8). This file bounds the fraction of
permutations of `X × Z` that are not `PermGood π (3 * s)` by elementary union bounds.

* `card_filter_mem_mul_le`: the swap argument. Given the images of a set `T` of points, the image
  of a further point `q` is spread evenly over the `N - |T|` unused points.
* `card_filter_le_card_le`, `card_filter_le_card_div_le`: at least `s` points of `A` sent into `B`.
* `rateCount_tail`, `pairCount_tail`: the two conditions of `PermGood`, for fixed rates.
* `prob_not_permGood_le`: the union bound over all rates.
-/

namespace Quantum.Sponge

open Finset

section Perm

variable {α : Type} [Fintype α] [DecidableEq α]

/-- The swap argument: if an event `E` and a target set `S π` only depend on the images of the
points of `T`, then the image of a point `q ∉ T` lies in the target for at most a fraction
`m / (N - |T|)` of `E`, where `m` bounds the target sizes. -/
theorem card_filter_mem_mul_le (E : Finset (Equiv.Perm α)) (T : Finset α) {q : α} (hq : q ∉ T)
    (S : Equiv.Perm α → Finset α) (m : ℕ)
    (hE : ∀ π ∈ E, ∀ σ : Equiv.Perm α, (∀ t ∈ T, σ t = π t) → σ ∈ E)
    (hS : ∀ π ∈ E, ∀ σ : Equiv.Perm α, (∀ t ∈ T, σ t = π t) → S σ = S π)
    (hm : ∀ π ∈ E, #(S π) ≤ m) :
    #(E.filter fun π ↦ π q ∈ S π) * (Fintype.card α - #T) ≤ #E * m := by
  have hsrc : #((E.filter fun π ↦ π q ∈ S π).sigma fun π ↦ univ \ T.image π) =
      #(E.filter fun π ↦ π q ∈ S π) * (Fintype.card α - #T) := by
    rw [card_sigma, sum_const_nat]
    intro π _
    rw [card_sdiff_of_subset (subset_univ _), card_univ, card_image_of_injective _ π.injective]
  have htgt : #(E.sigma S) ≤ #E * m := by
    rw [card_sigma]
    simpa using sum_le_card_nsmul _ _ _ hm
  rw [← hsrc]
  refine le_trans (card_le_card_of_injOn
    (fun p ↦ (⟨Equiv.swap (p.1 q) p.2 * p.1, p.1 q⟩ : (_ : Equiv.Perm α) × α)) ?_ ?_) htgt
  · rintro ⟨π, y⟩ hp
    simp only [coe_sigma, Set.mem_sigma_iff, coe_filter, Set.mem_ofPred_eq, coe_sdiff, coe_univ,
      coe_image, Set.mem_sdiff, Set.mem_univ, Set.mem_image, mem_coe, true_and] at hp ⊢
    obtain ⟨⟨hπ, hq'⟩, hy⟩ := hp
    have hfix : ∀ t ∈ T, (Equiv.swap (π q) y * π) t = π t := by
      intro t ht
      rw [Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne]
      · intro h
        rw [← π.injective h] at hq
        exact hq ht
      · exact fun h ↦ hy ⟨t, ht, h⟩
    exact ⟨hE π hπ _ hfix, (hS π hπ _ hfix) ▸ hq'⟩
  · rintro ⟨π, y⟩ _ ⟨π', y'⟩ _ h
    simp only [Sigma.mk.injEq, heq_eq_eq] at h
    obtain ⟨h1, h2⟩ := h
    have hy : y = y' := by
      have := congrArg (· q) h1
      simpa [Equiv.Perm.mul_apply, h2] using this
    subst hy
    rw [h2] at h1
    rw [mul_left_cancel h1]

/-- The permutations sending every point of `T` into `B`, counted against `N!`:
their number times `N.descFactorial |T|` is at most `N! * |B|.descFactorial |T|`. -/
theorem card_forall_mem_mul_descFactorial_le (B T : Finset α) :
    #(univ.filter fun π : Equiv.Perm α ↦ ∀ t ∈ T, π t ∈ B) *
        (Fintype.card α).descFactorial #T ≤
      (Fintype.card α).factorial * (#B).descFactorial #T := by
  induction T using Finset.induction_on with
  | empty => simp [Fintype.card_perm]
  | insert a T ha ih =>
    rw [card_insert_of_notMem ha, Nat.descFactorial_succ, Nat.descFactorial_succ]
    have key := card_filter_mem_mul_le (univ.filter fun π : Equiv.Perm α ↦ ∀ t ∈ T, π t ∈ B) T
      ha (fun π ↦ B \ T.image π) (#B - #T) ?_ ?_ ?_
    · have hsub : (univ.filter fun π : Equiv.Perm α ↦ ∀ t ∈ insert a T, π t ∈ B) ⊆
          (univ.filter fun π : Equiv.Perm α ↦ ∀ t ∈ T, π t ∈ B).filter
            fun π ↦ π a ∈ B \ T.image π := by
        intro π hπ
        simp only [mem_filter, mem_univ, true_and, forall_mem_insert, mem_sdiff, mem_image]
          at hπ ⊢
        refine ⟨hπ.2, hπ.1, fun ⟨t, ht, h⟩ ↦ ha ?_⟩
        rw [← π.injective h]
        exact ht
      calc _ = #(univ.filter fun π : Equiv.Perm α ↦ ∀ t ∈ insert a T, π t ∈ B) *
              (Fintype.card α - #T) * (Fintype.card α).descFactorial #T := by ring
        _ ≤ #((univ.filter fun π : Equiv.Perm α ↦ ∀ t ∈ T, π t ∈ B).filter
              fun π : Equiv.Perm α ↦ π a ∈ B \ T.image π) *
              (Fintype.card α - #T) * (Fintype.card α).descFactorial #T := by
          gcongr
        _ ≤ #(univ.filter fun π : Equiv.Perm α ↦ ∀ t ∈ T, π t ∈ B) * (#B - #T) *
              (Fintype.card α).descFactorial #T := Nat.mul_le_mul_right _ key
        _ = #(univ.filter fun π : Equiv.Perm α ↦ ∀ t ∈ T, π t ∈ B) *
              (Fintype.card α).descFactorial #T * (#B - #T) := by ring
        _ ≤ (Fintype.card α).factorial * (#B).descFactorial #T * (#B - #T) := by gcongr
        _ = _ := by ring
    · intro π hπ σ hσ
      simp only [mem_filter, mem_univ, true_and] at hπ ⊢
      intro t ht
      rw [hσ t ht]
      exact hπ t ht
    · intro π _ σ hσ
      exact congrArg (B \ ·) (image_congr fun t ht ↦ hσ t ht)
    · intro π hπ
      simp only [mem_filter, mem_univ, true_and] at hπ
      have hsub : T.image π ⊆ B := by
        intro b hb
        obtain ⟨t, ht, rfl⟩ := mem_image.1 hb
        exact hπ t ht
      rw [card_sdiff_of_subset hsub, card_image_of_injective _ π.injective]

/-- The permutations sending at least `s` points of `A` into `B` number at most
`|A|.choose s * |B|.descFactorial s * (N - s)!`. -/
theorem card_filter_le_card_le (A B : Finset α) (s : ℕ) :
    #(univ.filter fun π : Equiv.Perm α ↦ s ≤ #(A.filter (π · ∈ B))) ≤
      (#A).choose s * (#B).descFactorial s * (Fintype.card α - s).factorial := by
  have hsub : (univ.filter fun π : Equiv.Perm α ↦ s ≤ #(A.filter (π · ∈ B))) ⊆
      (A.powersetCard s).biUnion fun T ↦ univ.filter fun π ↦ ∀ t ∈ T, π t ∈ B := by
    intro π hπ
    simp only [mem_filter, mem_univ, true_and] at hπ
    obtain ⟨T, hT, hTc⟩ := exists_subset_card_eq hπ
    simp only [mem_biUnion, mem_powersetCard, mem_filter, mem_univ, true_and]
    exact ⟨T, ⟨hT.trans (filter_subset _ _), hTc⟩, fun t ht ↦ (mem_filter.1 (hT ht)).2⟩
  refine (card_le_card hsub).trans ?_
  rw [← card_powersetCard s A, mul_assoc]
  refine card_biUnion_le_card_mul _ _ _ fun T hT ↦ ?_
  obtain ⟨-, rfl⟩ := mem_powersetCard.1 hT
  have hN : #T ≤ Fintype.card α := card_le_univ T
  have key := card_forall_mem_mul_descFactorial_le B T
  rw [← Nat.factorial_mul_descFactorial hN] at key
  refine le_of_mul_le_mul_right ?_ (Nat.descFactorial_pos.2 hN)
  calc _ ≤ (Fintype.card α - #T).factorial * (Fintype.card α).descFactorial #T *
          (#B).descFactorial #T := key
    _ = _ := by ring

/-- `b.descFactorial k / n.descFactorial k ≤ (b / n) ^ k` for `b ≤ n`, cleared of denominators. -/
theorem descFactorial_mul_pow_le {b n : ℕ} (h : b ≤ n) :
    ∀ k : ℕ, b.descFactorial k * n ^ k ≤ b ^ k * n.descFactorial k
  | 0 => by simp
  | k + 1 => by
    have hk : (b - k) * n ≤ b * (n - k) := by
      rcases le_total k b with hkb | hbk
      · rw [Nat.sub_mul, Nat.mul_sub]
        exact Nat.sub_le_sub_left (by rw [mul_comm]; exact Nat.mul_le_mul_left _ h) _
      · simp [Nat.sub_eq_zero_of_le hbk]
    rw [Nat.descFactorial_succ, Nat.descFactorial_succ]
    calc (b - k) * b.descFactorial k * n ^ (k + 1)
        = (b.descFactorial k * n ^ k) * ((b - k) * n) := by ring
      _ ≤ (b ^ k * n.descFactorial k) * (b * (n - k)) :=
          Nat.mul_le_mul (descFactorial_mul_pow_le h k) hk
      _ = _ := by ring

/-- The fraction of permutations sending at least `s` points of `A` into `B` is at most
`|A|.choose s * (|B| / N) ^ s`. -/
theorem card_filter_le_card_div_le (A B : Finset α) (s : ℕ) :
    (#(univ.filter fun π : Equiv.Perm α ↦ s ≤ #(A.filter (π · ∈ B))) : ℝ) /
        Fintype.card (Equiv.Perm α) ≤
      (#A).choose s * ((#B : ℝ) / Fintype.card α) ^ s := by
  by_cases hs : s ≤ Fintype.card α
  · have hNs : (0 : ℝ) < (Fintype.card α : ℝ) ^ s := by
      rcases Nat.eq_zero_or_pos (Fintype.card α) with h | h
      · rw [show s = 0 by omega, pow_zero]
        exact one_pos
      · positivity
    rw [Fintype.card_perm, div_pow, ← mul_div_assoc,
      div_le_div_iff₀ (by exact_mod_cast Nat.factorial_pos _) hNs]
    have h1 := card_filter_le_card_le A B s
    have h2 := descFactorial_mul_pow_le (card_le_univ B) s
    have hN := Nat.factorial_mul_descFactorial hs
    have key : #(univ.filter fun π : Equiv.Perm α ↦ s ≤ #(A.filter (π · ∈ B))) *
        Fintype.card α ^ s ≤ (#A).choose s * #B ^ s * (Fintype.card α).factorial :=
      calc _ ≤ (#A).choose s * (#B).descFactorial s * (Fintype.card α - s).factorial *
            Fintype.card α ^ s := by gcongr
        _ = (#A).choose s * (Fintype.card α - s).factorial *
            ((#B).descFactorial s * Fintype.card α ^ s) := by ring
        _ ≤ (#A).choose s * (Fintype.card α - s).factorial *
            (#B ^ s * (Fintype.card α).descFactorial s) := by gcongr
        _ = (#A).choose s * #B ^ s *
            ((Fintype.card α - s).factorial * (Fintype.card α).descFactorial s) := by ring
        _ = _ := by rw [hN]
    exact_mod_cast key
  · have hempty : (univ.filter fun π : Equiv.Perm α ↦ s ≤ #(A.filter (π · ∈ B))) = ∅ := by
      refine filter_false_of_mem fun π _ h ↦ hs ?_
      exact h.trans ((card_le_univ _))
    rw [hempty, card_empty, Nat.cast_zero, zero_div]
    positivity

end Perm

section Sponge

variable {X Z : Type} [Fintype X] [DecidableEq X] [Fintype Z] [DecidableEq Z] [AddCommGroup Z]

omit [DecidableEq Z] [AddCommGroup Z] in
/-- A rate's row `{x} × Z` has `|Z|` points. -/
theorem card_filter_fst_eq (x : X) : #(univ.filter fun p : X × Z ↦ p.1 = x) = Fintype.card Z := by
  rw [show (univ.filter fun p : X × Z ↦ p.1 = x) = univ.map (Function.Embedding.sectR x Z) by
    ext ⟨a, b⟩
    simp [eq_comm], card_map, card_univ]

omit [AddCommGroup Z] in
/-- The fraction of permutations sending at least `s` points of row `x1` into row `x2`. -/
theorem rateCount_tail (x1 x2 : X) (s : ℕ) :
    (#(univ.filter fun π : Equiv.Perm (X × Z) ↦ s ≤ rateCount π x1 x2) : ℝ) /
        Fintype.card (Equiv.Perm (X × Z)) ≤
      (Fintype.card Z).choose s *
        ((Fintype.card Z : ℝ) / (Fintype.card X * Fintype.card Z)) ^ s := by
  have hrate : ∀ π : Equiv.Perm (X × Z), rateCount π x1 x2 =
      #((univ.map (Function.Embedding.sectR x1 Z)).filter
        (π · ∈ univ.filter fun p : X × Z ↦ p.1 = x2)) := by
    intro π
    rw [filter_map, card_map]
    simp [rateCount]
  have := card_filter_le_card_div_le (univ.map (Function.Embedding.sectR x1 Z))
    (univ.filter fun p : X × Z ↦ p.1 = x2) s
  simp only [card_map, card_univ, card_filter_fst_eq, Fintype.card_prod, ← hrate] at this
  exact_mod_cast this

omit [Fintype Z] in
/-- Greedy extraction: any set `W` of capacities has a subset `V` with `|W| ≤ 3 |V|` none of
whose distinct members differ by `d`. -/
theorem exists_subset_sep (d : Z) : ∀ (n : ℕ) (W : Finset Z), #W ≤ n →
    ∃ V ⊆ W, #W ≤ 3 * #V ∧ ∀ v ∈ V, ∀ v' ∈ V, v' ≠ v → v' ≠ v + d
  | 0, W, h => ⟨∅, empty_subset _, by simpa using h, by simp⟩
  | n + 1, W, h => by
    rcases W.eq_empty_or_nonempty with rfl | ⟨w, hw⟩
    · exact ⟨∅, empty_subset _, by simp, by simp⟩
    have hsub : W \ {w, w + d, w - d} ⊆ W.erase w := by
      intro x hx
      simp only [mem_sdiff, mem_insert, mem_singleton, not_or] at hx
      exact mem_erase.2 ⟨hx.2.1, hx.1⟩
    have h1 := card_le_card hsub
    have h2 := card_erase_of_mem hw
    have h3 := card_le_card_sdiff_add_card (s := W) (t := {w, w + d, w - d})
    have h4 := card_le_three (a := w) (b := w + d) (c := w - d)
    obtain ⟨V, hVW, hcard, hsep⟩ := exists_subset_sep d n (W \ {w, w + d, w - d}) (by omega)
    have hwV : w ∉ V := fun hw' ↦ by simpa using hVW hw'
    refine ⟨insert w V, insert_subset hw (hVW.trans sdiff_subset), ?_, ?_⟩
    · rw [card_insert_of_notMem hwV]
      omega
    · intro v hv v' hv' hne
      rw [mem_insert] at hv hv'
      rcases hv with rfl | hv <;> rcases hv' with rfl | hv'
      · exact absurd rfl hne
      · intro h
        have := hVW hv'
        simp [h] at this
      · intro h
        have := hVW hv
        simp [h] at this
      · exact hsep v hv v' hv' hne

/-- For a family `V` of capacities whose points `(x1, w)` and `(x2, w + d)` are pairwise distinct,
the permutations giving each pair the same image rate, counted against `N!`. -/
theorem card_forall_pair_mul_le (x1 x2 : X) (d : Z) (V : Finset Z)
    (hV : ∀ v ∈ V, ∀ v' ∈ V, (x1, v') ≠ (x2, v + d)) :
    #(univ.filter fun π : Equiv.Perm (X × Z) ↦ ∀ w ∈ V, (π (x1, w)).1 = (π (x2, w + d)).1) *
        (Fintype.card X * Fintype.card Z - 2 * #V) ^ #V ≤
      (Fintype.card X * Fintype.card Z).factorial * Fintype.card Z ^ #V := by
  induction V using Finset.induction_on with
  | empty => simp [Fintype.card_perm, Fintype.card_prod]
  | insert v V hv ih =>
    specialize ih fun a ha b hb ↦ hV a (mem_insert_of_mem ha) b (mem_insert_of_mem hb)
    set E := univ.filter fun π : Equiv.Perm (X × Z) ↦
      ∀ w ∈ V, (π (x1, w)).1 = (π (x2, w + d)).1 with hE
    set T : Finset (X × Z) := insert (x2, v + d)
      (V.image (fun w ↦ (x1, w)) ∪ V.image fun w ↦ (x2, w + d)) with hT
    have hq : (x1, v) ∉ T := by
      simp only [hT, mem_insert, mem_union, mem_image, not_or, not_exists, not_and]
      refine ⟨hV v (mem_insert_self _ _) v (mem_insert_self _ _), fun w hw h ↦ hv ?_,
        fun w hw h ↦ hV w (mem_insert_of_mem hw) v (mem_insert_self _ _) h.symm⟩
      rw [← (Prod.mk.inj h).2]
      exact hw
    have hTc : #T ≤ 2 * #V + 1 := by
      rw [hT]
      have := card_union_le (V.image fun w ↦ (x1, w)) (V.image fun w ↦ (x2, w + d))
      have := card_image_le (s := V) (f := fun w ↦ (x1, w))
      have := card_image_le (s := V) (f := fun w ↦ (x2, w + d))
      have := card_insert_le (x2, v + d)
        (V.image (fun w ↦ (x1, w)) ∪ V.image fun w ↦ (x2, w + d))
      omega
    have key := card_filter_mem_mul_le E T hq
      (fun π ↦ univ.filter fun p : X × Z ↦ p.1 = (π (x2, v + d)).1) (Fintype.card Z) ?_ ?_ ?_
    · have heq : (univ.filter fun π : Equiv.Perm (X × Z) ↦
            ∀ w ∈ insert v V, (π (x1, w)).1 = (π (x2, w + d)).1) =
          E.filter fun π ↦ π (x1, v) ∈ univ.filter fun p : X × Z ↦ p.1 = (π (x2, v + d)).1 := by
        ext π
        simp only [hE, mem_filter, mem_univ, true_and, forall_mem_insert]
        exact and_comm
      rw [Fintype.card_prod] at key
      rw [card_insert_of_notMem hv, heq]
      calc _ = #(E.filter fun π ↦ π (x1, v) ∈ univ.filter fun p : X × Z ↦
              p.1 = (π (x2, v + d)).1) *
              (Fintype.card X * Fintype.card Z - 2 * (#V + 1)) *
              (Fintype.card X * Fintype.card Z - 2 * (#V + 1)) ^ #V := by ring
        _ ≤ #(E.filter fun π ↦ π (x1, v) ∈ univ.filter fun p : X × Z ↦
              p.1 = (π (x2, v + d)).1) *
              (Fintype.card X * Fintype.card Z - #T) *
              (Fintype.card X * Fintype.card Z - 2 * #V) ^ #V :=
          Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega))
            (Nat.pow_le_pow_left (by omega) _)
        _ ≤ #E * Fintype.card Z * (Fintype.card X * Fintype.card Z - 2 * #V) ^ #V := by
          gcongr
        _ = (#E * (Fintype.card X * Fintype.card Z - 2 * #V) ^ #V) * Fintype.card Z := by ring
        _ ≤ (Fintype.card X * Fintype.card Z).factorial * Fintype.card Z ^ #V *
              Fintype.card Z := by gcongr
        _ = _ := by ring
    · intro π hπ σ hσ
      simp only [hE, mem_filter, mem_univ, true_and] at hπ ⊢
      intro w hw
      rw [hσ (x1, w) (by simp [hT, hw]), hσ (x2, w + d) (by simp [hT, hw])]
      exact hπ w hw
    · intro π _ σ hσ
      rw [hσ (x2, v + d) (mem_insert_self _ _)]
    · intro π _
      rw [card_filter_fst_eq]

/-- The fraction of permutations for which at least `3 s` capacities `w` give `(x1, w)` and
`(x2, w + d)` the same image rate, for two distinct point families. -/
theorem pairCount_tail (x1 x2 : X) (d : Z) (hd : (x1, d) ≠ (x2, 0)) {s : ℕ}
    (hs : 2 * s < Fintype.card X * Fintype.card Z) :
    (#(univ.filter fun π : Equiv.Perm (X × Z) ↦ 3 * s ≤ pairCount π x1 x2 d) : ℝ) /
        Fintype.card (Equiv.Perm (X × Z)) ≤
      (Fintype.card Z).choose s *
        ((Fintype.card Z : ℝ) / (Fintype.card X * Fintype.card Z - 2 * s)) ^ s := by
  set P := (univ.powersetCard s).filter fun V : Finset Z ↦
    ∀ v ∈ V, ∀ v' ∈ V, (x1, v') ≠ (x2, v + d) with hP
  set E : Finset Z → Finset (Equiv.Perm (X × Z)) := fun V ↦
    univ.filter fun π ↦ ∀ w ∈ V, (π (x1, w)).1 = (π (x2, w + d)).1 with hE
  have hsub : (univ.filter fun π : Equiv.Perm (X × Z) ↦ 3 * s ≤ pairCount π x1 x2 d) ⊆
      P.biUnion E := by
    intro π hπ
    have h3 : 3 * s ≤ pairCount π x1 x2 d := (mem_filter.1 hπ).2
    unfold pairCount at h3
    obtain ⟨V, hVW, hcard, hsep⟩ := exists_subset_sep d _
      (univ.filter fun w ↦ (π (x1, w)).1 = (π (x2, w + d)).1) le_rfl
    obtain ⟨U, hUV, hUc⟩ := exists_subset_card_eq (s := V) (n := s) (by omega)
    simp only [hP, hE, mem_biUnion, mem_filter, mem_powersetCard, mem_univ, true_and,
      subset_univ]
    refine ⟨U, ⟨hUc, fun v hv v' hv' h ↦ ?_⟩, fun w hw ↦ (mem_filter.1 (hVW (hUV hw))).2⟩
    obtain ⟨rfl, h2⟩ := Prod.mk.inj h
    by_cases hvv : v' = v
    · subst hvv
      have hd0 : d = 0 := by simpa using h2
      exact hd (by rw [hd0])
    · exact hsep v (hUV hv) v' (hUV hv') hvv h2
  have hpos : (0 : ℝ) < Fintype.card X * Fintype.card Z - 2 * s := by
    have : ((2 * s : ℕ) : ℝ) < ((Fintype.card X * Fintype.card Z : ℕ) : ℝ) := by
      exact_mod_cast hs
    push_cast at this
    linarith
  have hbound : ∀ V ∈ P, (#(E V) : ℝ) ≤ (Fintype.card X * Fintype.card Z).factorial *
      ((Fintype.card Z : ℝ) / (Fintype.card X * Fintype.card Z - 2 * s)) ^ s := by
    intro V hV
    simp only [hP, mem_filter, mem_powersetCard] at hV
    obtain ⟨⟨-, rfl⟩, hsep⟩ := hV
    have h := card_forall_pair_mul_le x1 x2 d V hsep
    have h' := (Nat.cast_le (α := ℝ)).2 h
    push_cast [Nat.cast_sub hs.le] at h'
    rw [div_pow, ← mul_div_assoc, le_div_iff₀ (by positivity)]
    exact h'
  have hP : (#P : ℝ) ≤ (Fintype.card Z).choose s := by
    have : #P ≤ (Fintype.card Z).choose s := by
      refine (card_filter_le _ _).trans ?_
      rw [card_powersetCard, card_univ]
    exact_mod_cast this
  rw [Fintype.card_perm, Fintype.card_prod,
    div_le_iff₀ (by exact_mod_cast Nat.factorial_pos _)]
  calc (#(univ.filter fun π : Equiv.Perm (X × Z) ↦ 3 * s ≤ pairCount π x1 x2 d) : ℝ)
      ≤ #(P.biUnion E) := by exact_mod_cast card_le_card hsub
    _ ≤ ∑ V ∈ P, (#(E V) : ℝ) := by exact_mod_cast card_biUnion_le
    _ ≤ ∑ _V ∈ P, ((Fintype.card X * Fintype.card Z).factorial *
          ((Fintype.card Z : ℝ) / (Fintype.card X * Fintype.card Z - 2 * s)) ^ s) :=
        sum_le_sum hbound
    _ = #P * ((Fintype.card X * Fintype.card Z).factorial *
          ((Fintype.card Z : ℝ) / (Fintype.card X * Fintype.card Z - 2 * s)) ^ s) := by
        rw [sum_const, nsmul_eq_mul]
    _ ≤ (Fintype.card Z).choose s * ((Fintype.card X * Fintype.card Z).factorial *
          ((Fintype.card Z : ℝ) / (Fintype.card X * Fintype.card Z - 2 * s)) ^ s) := by
        gcongr
    _ = _ := by ring

/-- `PermGood` is decidable: both of its conditions range over finite types. -/
instance (π : Equiv.Perm (X × Z)) (G : ℕ) : Decidable (PermGood π G) :=
  decidable_of_iff ((∀ x1 x2, rateCount π x1 x2 ≤ G) ∧
      ∀ x1 x2 d, (x1, d) ≠ (x2, 0) → pairCount π x1 x2 d ≤ G)
    ⟨fun h ↦ ⟨h.1, h.2⟩, fun h ↦ ⟨h.rate, h.pair⟩⟩

/-- A uniform permutation of `X × Z` is `PermGood π (3 * s)` except with probability at most
`|X|² C(|Z|, s) (|Z| / N) ^ s + |X|² |Z| C(|Z|, s) (|Z| / (N - 2 s)) ^ s`, `N = |X| |Z|`. -/
theorem prob_not_permGood_le {s : ℕ} (hs : 2 * s < Fintype.card X * Fintype.card Z) :
    (#(univ.filter fun π : Equiv.Perm (X × Z) ↦ ¬PermGood π (3 * s)) : ℝ) /
        Fintype.card (Equiv.Perm (X × Z)) ≤
      (Fintype.card X : ℝ) ^ 2 * (Fintype.card Z).choose s *
          ((Fintype.card Z : ℝ) / (Fintype.card X * Fintype.card Z)) ^ s +
        (Fintype.card X : ℝ) ^ 2 * Fintype.card Z * (Fintype.card Z).choose s *
          ((Fintype.card Z : ℝ) / (Fintype.card X * Fintype.card Z - 2 * s)) ^ s := by
  set R : X × X → Finset (Equiv.Perm (X × Z)) := fun p ↦
    univ.filter fun π ↦ s ≤ rateCount π p.1 p.2 with hR
  set Q := (univ : Finset (X × X × Z)).filter fun t ↦ (t.1, t.2.2) ≠ (t.2.1, 0) with hQ
  set C : X × X × Z → Finset (Equiv.Perm (X × Z)) := fun t ↦
    univ.filter fun π ↦ 3 * s ≤ pairCount π t.1 t.2.1 t.2.2 with hC
  set M := Fintype.card (Equiv.Perm (X × Z))
  have hsub : (univ.filter fun π : Equiv.Perm (X × Z) ↦ ¬PermGood π (3 * s)) ⊆
      (univ : Finset (X × X)).biUnion R ∪ Q.biUnion C := by
    intro π hπ
    rw [mem_filter] at hπ
    by_contra hn
    simp only [hR, hQ, hC, mem_union, mem_biUnion, mem_filter, mem_univ, true_and, not_or,
      not_exists, not_and, not_le] at hn
    exact hπ.2 ⟨fun x1 x2 ↦ (hn.1 (x1, x2)).le.trans (by omega),
      fun x1 x2 d hd ↦ (hn.2 (x1, x2, d) hd).le⟩
  have hM : (0 : ℝ) < M := by exact_mod_cast Fintype.card_pos
  have hpos : (0 : ℝ) < Fintype.card X * Fintype.card Z - 2 * s := by
    have : ((2 * s : ℕ) : ℝ) < ((Fintype.card X * Fintype.card Z : ℕ) : ℝ) := by
      exact_mod_cast hs
    push_cast at this
    linarith
  have hQc : (#Q : ℝ) ≤ (Fintype.card X : ℝ) ^ 2 * Fintype.card Z := by
    have : #Q ≤ Fintype.card X ^ 2 * Fintype.card Z := by
      refine (card_filter_le _ _).trans ?_
      rw [card_univ, Fintype.card_prod, Fintype.card_prod, sq, mul_assoc]
    exact_mod_cast this
  calc (#(univ.filter fun π : Equiv.Perm (X × Z) ↦ ¬PermGood π (3 * s)) : ℝ) / M
      ≤ (∑ p, (#(R p) : ℝ) + ∑ t ∈ Q, (#(C t) : ℝ)) / M := by
        gcongr
        have := (card_le_card hsub).trans
          ((card_union_le _ _).trans (add_le_add card_biUnion_le card_biUnion_le))
        exact_mod_cast this
    _ = ∑ p, (#(R p) : ℝ) / M + ∑ t ∈ Q, (#(C t) : ℝ) / M := by
        rw [add_div, sum_div, sum_div]
    _ ≤ ∑ _p : X × X, ((Fintype.card Z).choose s *
            ((Fintype.card Z : ℝ) / (Fintype.card X * Fintype.card Z)) ^ s) +
          ∑ _t ∈ Q, ((Fintype.card Z).choose s *
            ((Fintype.card Z : ℝ) / (Fintype.card X * Fintype.card Z - 2 * s)) ^ s) :=
        add_le_add (sum_le_sum fun p _ ↦ rateCount_tail p.1 p.2 s)
          (sum_le_sum fun t ht ↦ pairCount_tail t.1 t.2.1 t.2.2 (mem_filter.1 ht).2 hs)
    _ = (Fintype.card X : ℝ) ^ 2 * ((Fintype.card Z).choose s *
            ((Fintype.card Z : ℝ) / (Fintype.card X * Fintype.card Z)) ^ s) +
          #Q * ((Fintype.card Z).choose s *
            ((Fintype.card Z : ℝ) / (Fintype.card X * Fintype.card Z - 2 * s)) ^ s) := by
        rw [sum_const, sum_const, nsmul_eq_mul, nsmul_eq_mul, card_univ, Fintype.card_prod]
        push_cast
        ring
    _ ≤ (Fintype.card X : ℝ) ^ 2 * ((Fintype.card Z).choose s *
            ((Fintype.card Z : ℝ) / (Fintype.card X * Fintype.card Z)) ^ s) +
          (Fintype.card X : ℝ) ^ 2 * Fintype.card Z * ((Fintype.card Z).choose s *
            ((Fintype.card Z : ℝ) / (Fintype.card X * Fintype.card Z - 2 * s)) ^ s) := by
        gcongr
    _ = _ := by ring

end Sponge

end Quantum.Sponge

end
