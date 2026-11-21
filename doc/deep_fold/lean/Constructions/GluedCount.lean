/-
The word `L_U ^ 5` has a list of size linear in `n` at agreement `5n/8` (Proposition 3.4(a) of the
paper).

The paper counts `56n - 392` members. Here only a lower bound of one member per hyperplane `W` of
`U` is proved, `n / 8 - 1` in all (`glued_list_card`): for each `W` a set of ten labels with sum
`η` that contains `η` and not `0` (`exists_label_set`), so its union of cosets is not invariant
under `U`, and unions from different hyperplanes are then different (`glued_eq_imp_invariant`).
-/
import Constructions.Glued

open Polynomial
open scoped Classical

namespace Constructions

variable {K : Type*} [Field K]

theorem exists_mem_notMem_of_card_lt {V Λ : AddSubgroup K} [Finite Λ] (hle : V ≤ Λ)
    (hlt : Nat.card V < Nat.card Λ) : ∃ x ∈ Λ, x ∉ V := by
  have : Finite V := Set.finite_coe_iff.mpr ((Set.toFinite (Λ : Set K)).subset hle)
  by_contra hcon
  have hle' : Λ ≤ V := fun x hx => by
    by_contra hx'
    exact hcon ⟨x, hx, hx'⟩
  rw [le_antisymm hle hle'] at hlt
  exact lt_irrefl _ hlt

theorem eq_of_le_of_card_le {V Λ : AddSubgroup K} [Finite Λ] (hle : V ≤ Λ)
    (hc : Nat.card Λ ≤ Nat.card V) : V = Λ := by
  have : Finite V := Set.finite_coe_iff.mpr ((Set.toFinite (Λ : Set K)).subset hle)
  have hsub : pts V ⊆ pts Λ := fun x hx => mem_pts.mpr (hle (mem_pts.mp hx))
  exact pts_injective (Finset.eq_of_subset_of_card_le hsub (by rwa [card_pts, card_pts]))

section CharTwo

variable [CharP K 2]

theorem card_adjoin_bot {a : K} (ha : a ≠ 0) : Nat.card (adjoin (⊥ : AddSubgroup K) a) = 2 := by
  rw [card_adjoin ⊥ (by rwa [AddSubgroup.mem_bot]), AddSubgroup.card_bot]

/-- The points of a subspace with at least four elements sum to zero. -/
theorem sum_pts_adjoin (V : AddSubgroup K) [Finite V] {b : K} (hb : b ∉ V)
    (heven : Even (Nat.card V)) : ∑ x ∈ pts (adjoin V b), x = 0 := by
  rw [pts_adjoin, Finset.sum_union (disjoint_pts_image V hb),
    Finset.sum_image (fun x _ y _ h => add_right_cancel h), Finset.sum_add_distrib,
    Finset.sum_const, card_pts, ← add_assoc, CharTwo.add_self_eq_zero, zero_add]
  obtain ⟨k, hk⟩ := heven
  rw [hk, add_smul, CharTwo.add_self_eq_zero]

/-- In a subspace `Λ` of sixteen labels containing `η ≠ 0` there is a set of ten labels with sum
`η` that contains `η` and not `0`: the complement of `{0, λ₁, λ₂, λ₁ + λ₂, λ₃, λ₃ + η}`. -/
theorem exists_label_set (Λ : AddSubgroup K) [Finite Λ] (hΛ : Nat.card Λ = 16) {η : K}
    (hη : η ∈ Λ) (hη0 : η ≠ 0) :
    ∃ Y : Finset K, Y ⊆ pts Λ ∧ Y.card = 10 ∧ ∑ y ∈ Y, y = η ∧ η ∈ Y ∧ (0 : K) ∉ Y := by
  -- a basis `η, l₁, l₂, l₃` of `Λ`
  have hstep : ∀ (V : AddSubgroup K) (b : K), V ≤ Λ → b ∈ Λ → adjoin V b ≤ Λ := by
    rintro V b hV hb x (hx | hx)
    · exact hV hx
    · have := Λ.sub_mem (hV hx) hb
      rwa [add_sub_cancel_right] at this
  have hA1 : adjoin (⊥ : AddSubgroup K) η ≤ Λ := hstep ⊥ η bot_le hη
  have hc1 : Nat.card (adjoin (⊥ : AddSubgroup K) η) = 2 := card_adjoin_bot hη0
  obtain ⟨l₁, hl₁Λ, hl₁⟩ := exists_mem_notMem_of_card_lt hA1 (by rw [hc1, hΛ]; norm_num)
  have hA2 := hstep _ l₁ hA1 hl₁Λ
  have hc2 : Nat.card (adjoin (adjoin (⊥ : AddSubgroup K) η) l₁) = 4 := by
    rw [card_adjoin _ hl₁, hc1]
  obtain ⟨l₂, hl₂Λ, hl₂⟩ := exists_mem_notMem_of_card_lt hA2 (by rw [hc2, hΛ]; norm_num)
  have hA3 := hstep _ l₂ hA2 hl₂Λ
  have hc3 : Nat.card (adjoin (adjoin (adjoin (⊥ : AddSubgroup K) η) l₁) l₂) = 8 := by
    rw [card_adjoin _ hl₂, hc2]
  obtain ⟨l₃, hl₃Λ, hl₃⟩ := exists_mem_notMem_of_card_lt hA3 (by rw [hc3, hΛ]; norm_num)
  have hA4 := hstep _ l₃ hA3 hl₃Λ
  have hΛeq : adjoin (adjoin (adjoin (adjoin (⊥ : AddSubgroup K) η) l₁) l₂) l₃ = Λ :=
    eq_of_le_of_card_le hA4 (by rw [card_adjoin _ hl₃, hc3, hΛ])
  set A1 := adjoin (⊥ : AddSubgroup K) η with hA1def
  set A2 := adjoin A1 l₁ with hA2def
  set A3 := adjoin A2 l₂ with hA3def
  have hηA1 : η ∈ A1 := self_mem_adjoin _ η
  have hηA3 : η ∈ A3 := le_adjoin A2 l₂ (le_adjoin A1 l₁ hηA1)
  have hl₁0 : l₁ ≠ 0 := fun h => hl₁ (h ▸ A1.zero_mem)
  have hl₃0 : l₃ ≠ 0 := fun h => hl₃ (h ▸ A3.zero_mem)
  -- the plane `B = {0, l₁, l₂, l₁ + l₂}`
  set B1 := adjoin (⊥ : AddSubgroup K) l₁ with hB1def
  have hB1A2 : B1 ≤ A2 := by
    rintro x (hx | hx)
    · rw [AddSubgroup.mem_bot.mp hx]
      exact A2.zero_mem
    · exact Or.inr (by rw [AddSubgroup.mem_bot.mp hx]; exact A1.zero_mem)
  have hl₂B1 : l₂ ∉ B1 := fun h => hl₂ (hB1A2 h)
  set B := adjoin B1 l₂ with hBdef
  have hBA3 : B ≤ A3 := by
    rintro x (hx | hx)
    · exact le_adjoin A2 l₂ (hB1A2 hx)
    · exact Or.inr (hB1A2 hx)
  have hcB1 : Nat.card B1 = 2 := card_adjoin_bot hl₁0
  have hcB : Nat.card B = 4 := by rw [card_adjoin _ hl₂B1, hcB1]
  have hBΛ : B ≤ Λ := hBA3.trans hA3
  have hl₃B : l₃ ∉ B := fun h => hl₃ (hBA3 h)
  have hl₃ηB : l₃ + η ∉ B := fun h => by
    apply hl₃
    have := A3.sub_mem (hBA3 h) hηA3
    rwa [add_sub_cancel_right] at this
  have hηB : η ∉ B := by
    rintro ((h | h) | (h | h))
    · exact hη0 (AddSubgroup.mem_bot.mp h)
    · exact hl₁ (Or.inr (by rwa [add_comm] at h))
    · exact hl₂ (le_adjoin A1 l₁ (Or.inr (by rwa [add_comm] at h)))
    · refine hl₂ (Or.inr (Or.inr ?_))
      rwa [show l₂ + l₁ + η = η + l₂ + l₁ by ring]
  have hne : l₃ ≠ l₃ + η := fun h => hη0 (left_eq_add.mp h)
  set Z : Finset K := pts B ∪ {l₃, l₃ + η} with hZ
  have hdisj : Disjoint (pts B) {l₃, l₃ + η} := by
    rw [Finset.disjoint_left]
    intro x hx hx'
    rcases Finset.mem_insert.mp hx' with rfl | hx'
    · exact hl₃B (mem_pts.mp hx)
    · rw [Finset.mem_singleton.mp hx'] at hx
      exact hl₃ηB (mem_pts.mp hx)
  have hZc : Z.card = 6 := by
    rw [hZ, Finset.card_union_of_disjoint hdisj, card_pts, hcB, Finset.card_pair hne]
  have hZΛ : Z ⊆ pts Λ := by
    intro x hx
    rcases Finset.mem_union.mp hx with h | h
    · exact mem_pts.mpr (hBΛ (mem_pts.mp h))
    · rcases Finset.mem_insert.mp h with rfl | h
      · exact mem_pts.mpr hl₃Λ
      · rw [Finset.mem_singleton.mp h]
        exact mem_pts.mpr (Λ.add_mem hl₃Λ hη)
  have hsumΛ : ∑ x ∈ pts Λ, x = 0 := by
    rw [← hΛeq]
    exact sum_pts_adjoin A3 hl₃ (by rw [hc3]; decide)
  have hsumB : ∑ x ∈ pts B, x = 0 := sum_pts_adjoin B1 hl₂B1 (by rw [hcB1]; decide)
  have hsumZ : ∑ x ∈ Z, x = η := by
    rw [hZ, Finset.sum_union hdisj, hsumB, Finset.sum_pair hne, zero_add, ← add_assoc,
      CharTwo.add_self_eq_zero, zero_add]
  refine ⟨pts Λ \ Z, Finset.sdiff_subset, ?_, ?_, ?_, ?_⟩
  · rw [Finset.card_sdiff_of_subset hZΛ, card_pts, hΛ, hZc]
  · have h := Finset.sum_sdiff (f := fun x => x) hZΛ
    rw [hsumΛ, hsumZ] at h
    have h2 : ∑ x ∈ pts Λ \ Z, x = -η := eq_neg_of_add_eq_zero_left h
    rwa [CharTwo.neg_eq] at h2
  · rw [Finset.mem_sdiff]
    refine ⟨mem_pts.mpr hη, fun h => ?_⟩
    rcases Finset.mem_union.mp h with h | h
    · exact hηB (mem_pts.mp h)
    · rcases Finset.mem_insert.mp h with h | h
      · exact hl₃ (h ▸ hηA3)
      · exact hl₃0 (right_eq_add.mp (Finset.mem_singleton.mp h))
  · rw [Finset.mem_sdiff, not_and, not_not]
    intro _
    exact Finset.mem_union_left _ (mem_pts.mpr B.zero_mem)

/-- **The list of `L_U ^ 5` at `5n/8` is linear in `n`.** On a subspace domain `D` with
`|D| = n = 8 |U|`, the word `L_U ^ 5` has at least `|U| - 1 = n / 8 - 1` polynomials of degree at
most `4 |U| = n / 2` agreeing with it on at least `5 |U| = 5n/8` points. -/
theorem glued_list_card (D U : AddSubgroup K) [Finite D] (hUD : U ≤ D)
    (hD : Nat.card D = 8 * Nat.card U) :
    ((Nat.card U - 1 : ℕ) : ℕ∞) ≤
      (RSList (pts D) (fun x => (subPoly U).eval x ^ 5)
        (4 * Nat.card U + 1) (5 * Nat.card U)).encard := by
  have : Finite U := Set.finite_coe_iff.mpr ((Set.toFinite (D : Set K)).subset hUD)
  set T : Set (AddSubgroup K) := {W | W ≤ U ∧ 2 * Nat.card W = Nat.card U} with hT
  -- for each hyperplane: the element `a`, and the label set
  have hex : ∀ W : AddSubgroup K, ∃ (a : K) (Y : Finset K), W ∈ T →
      a ∈ U ∧ a ∉ W ∧ (∀ y ∈ Y, ∃ b ∈ D, (subPoly W).eval b = y) ∧ Y.card = 10 ∧
      ∑ y ∈ Y, y = (subPoly W).eval a ∧ (subPoly W).eval a ∈ Y ∧ (0 : K) ∉ Y := by
    intro W
    by_cases hW : W ∈ T
    · obtain ⟨hWU, hc⟩ := hW
      have : Finite W := Set.finite_coe_iff.mpr ((Set.toFinite (U : Set K)).subset hWU)
      have hWpos : 0 < Nat.card W := by
        rw [← card_pts]
        exact card_pts_pos W
      obtain ⟨a, haU, haW⟩ := exists_mem_notMem_of_card_lt hWU (by omega)
      set Λ : AddSubgroup K := AddSubgroup.map (subPolyHom W) D with hΛdef
      have hΛfin : Finite Λ := by
        refine Set.finite_coe_iff.mpr ?_
        rw [hΛdef, AddSubgroup.coe_map]
        exact (Set.toFinite (D : Set K)).image _
      have hΛmem : ∀ y, y ∈ Λ ↔ ∃ b ∈ D, (subPoly W).eval b = y := fun y => AddSubgroup.mem_map
      have hglued : glued D W (pts Λ) = pts D := by
        ext x
        rw [glued, Finset.mem_filter, and_iff_left_iff_imp]
        intro hx
        exact mem_pts.mpr ((hΛmem _).mpr ⟨x, mem_pts.mp hx, rfl⟩)
      have hΛc : Nat.card Λ = 16 := by
        have h := card_glued D W (hWU.trans hUD) (pts Λ)
          (fun y hy => (hΛmem y).mp (mem_pts.mp hy))
        rw [hglued, card_pts, card_pts, hD, ← hc] at h
        have h' : 16 * Nat.card W = Nat.card Λ * Nat.card W := by rw [← h]; ring
        exact (Nat.eq_of_mul_eq_mul_right hWpos h').symm
      have hηΛ : (subPoly W).eval a ∈ Λ := (hΛmem _).mpr ⟨a, hUD haU, rfl⟩
      have hη0 : (subPoly W).eval a ≠ 0 := fun h => haW (subPoly_eval_eq_zero.mp h)
      obtain ⟨Y, hYΛ, hYc, hYs, hηY, h0Y⟩ := exists_label_set Λ hΛc hηΛ hη0
      exact ⟨a, Y, fun _ => ⟨haU, haW, fun y hy => (hΛmem y).mp (mem_pts.mp (hYΛ hy)), hYc, hYs,
        hηY, h0Y⟩⟩
    · exact ⟨0, ∅, fun h => absurd h hW⟩
  choose a Y hspec using hex
  let f : AddSubgroup K → K[X] := fun W => gluedPoly D U W 5 (Y W)
  have hsmul : ∀ x : K, (5 : ℕ) • x = x := by
    intro x
    rw [show (5 : ℕ) = 2 * 2 + 1 by norm_num, add_smul, mul_smul, one_smul, two_smul,
      CharTwo.add_self_eq_zero, zero_add]
  have hmaps : Set.MapsTo f T (RSList (pts D) (fun x => (subPoly U).eval x ^ 5)
      (4 * Nat.card U + 1) (5 * Nat.card U)) := by
    intro W hW
    obtain ⟨haU, haW, hY, hYc, hYs, -, -⟩ := hspec W hW
    have h := gluedPoly_mem_RSList D U W hUD hW.1 hW.2 haU haW (g := 5) (Y W) hY hYc
      (by rw [hsmul]; exact hYs)
    have e1 : (2 * 5 - 2) * Nat.card W + 1 = 4 * Nat.card U + 1 := by
      rw [← hW.2]
      ring
    have e2 : 2 * 5 * Nat.card W = 5 * Nat.card U := by
      rw [← hW.2]
      ring
    rwa [e1, e2] at h
  have hinj : Set.InjOn f T := by
    intro W hW W' hW' h
    by_contra hne
    obtain ⟨haU, haW, -, -, -, hηY, h0Y⟩ := hspec W hW
    have : Finite W := Set.finite_coe_iff.mpr ((Set.toFinite (U : Set K)).subset hW.1)
    have hS : glued D W (Y W) = glued D W' (Y W') :=
      locator_injective (sub_right_injective h)
    have haS : a W ∈ glued D W (Y W) :=
      Finset.mem_filter.mpr ⟨mem_pts.mpr (hUD haU), hηY⟩
    have h0 := glued_eq_imp_invariant D U W W' hUD hW.1 hW.2 hW'.1 hne hW'.2 hS haS haU
    rw [CharTwo.add_self_eq_zero] at h0
    have h0' := (Finset.mem_filter.mp h0).2
    rw [subPoly_eval_eq_zero.mpr W.zero_mem] at h0'
    exact h0Y h0'
  exact (card_hyperplanes_ge U).trans (Set.encard_le_encard_of_injOn hmaps hinj)

end CharTwo

end Constructions
