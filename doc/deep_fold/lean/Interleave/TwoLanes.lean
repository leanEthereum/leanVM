/-
Proposition 6.3 of the paper (two lanes against one):
`Λ_2(a) ≤ Λ_1(a) + Λ_1(2a - d) (Λ_1(a) - 1)`.

It is stated here for the product of two codes, one for each lane, with the count
`L₁ + L₁' (L₂ - 1)`: for `L₁' = 1` and `L₁ = L₂ = L` this is the `2L - 1` of Theorem 6.1.
-/
import Interleave.Basic

open Finset

namespace Interleave

variable {ι α β : Type*}

/-- The product of two codes: words over `α × β` whose two lanes are codewords. -/
def prodCode (C₁ : Set (ι → α)) (C₂ : Set (ι → β)) : Set (ι → α × β) :=
  {c | (fun i => (c i).1) ∈ C₁ ∧ (fun i => (c i).2) ∈ C₂}

/-- **Proposition 6.3 of the paper** for two codes. Group the list members by their first lane:
there are at most `L₁` first lanes, at most `L₁'` of them are shared by two members (a shared
first lane agrees with the word on at least `2a - d` coordinates), and each is shared by at most
`L₂` members. -/
theorem listBound_prod {D : Finset ι} {C₁ : Set (ι → α)} {C₂ : Set (ι → β)} {d a L₁ L₁' L₂ : ℕ}
    (hC₂ : AgreeLE D C₂ d) (h₁ : ListBound D C₁ a L₁) (h₁' : ListBound D C₁ (2 * a - d) L₁')
    (h₂ : ListBound D C₂ a L₂) : ListBound D (prodCode C₁ C₂) a (L₁ + L₁' * (L₂ - 1)) := by
  classical
  intro w S hS
  obtain ⟨f, hf⟩ : ∃ f : (ι → α × β) → ι → α, ∀ c i, f c i = (c i).1 :=
    ⟨fun c i => (c i).1, fun _ _ => rfl⟩
  obtain ⟨s, hs⟩ : ∃ s : (ι → α × β) → ι → β, ∀ c i, s c i = (c i).2 :=
    ⟨fun c i => (c i).2, fun _ _ => rfl⟩
  have hfC : ∀ c ∈ S, f c ∈ C₁ := fun c hc => by
    have := (hS c hc).1.1
    rwa [show (fun i => (c i).1) = f c from funext fun i => (hf c i).symm] at this
  have hsC : ∀ c ∈ S, s c ∈ C₂ := fun c hc => by
    have := (hS c hc).1.2
    rwa [show (fun i => (c i).2) = s c from funext fun i => (hs c i).symm] at this
  have hagrf : ∀ c, agr D w c ⊆ agr D (f w) (f c) := fun c i hi =>
    mem_agr.mpr ⟨(mem_agr.mp hi).1, by rw [hf, hf, (mem_agr.mp hi).2]⟩
  have hagrs : ∀ c, agr D w c ⊆ agr D (s w) (s c) := fun c i hi =>
    mem_agr.mpr ⟨(mem_agr.mp hi).1, by rw [hs, hs, (mem_agr.mp hi).2]⟩
  have hfs : ∀ c c', f c = f c' → s c = s c' → c = c' := fun c c' h h' => by
    funext i
    exact Prod.ext ((hf c i).symm.trans ((congrFun h i).trans (hf c' i)))
      ((hs c i).symm.trans ((congrFun h' i).trans (hs c' i)))
  -- at most `L₁` first lanes
  have hCh : (S.image f).card ≤ L₁ := h₁ (f w) _ fun b hb => by
    obtain ⟨c, hc, rfl⟩ := mem_image.mp hb
    exact ⟨hfC c hc, (hS c hc).2.trans (card_le_card (hagrf c))⟩
  -- each shared by at most `L₂` members
  have hfib : ∀ b, (S.filter (fun c => f c = b)).card ≤ L₂ := by
    intro b
    have hinj : Set.InjOn s (S.filter (fun c => f c = b)) := fun c hc c' hc' h =>
      hfs c c' ((mem_filter.mp (mem_coe.mp hc)).2.trans (mem_filter.mp (mem_coe.mp hc')).2.symm) h
    rw [← card_image_of_injOn hinj]
    refine h₂ (s w) _ fun b' hb' => ?_
    obtain ⟨c, hc, rfl⟩ := mem_image.mp hb'
    have hcS := (mem_filter.mp hc).1
    exact ⟨hsC c hcS, (hS c hcS).2.trans (card_le_card (hagrs c))⟩
  -- at most `L₁'` shared first lanes
  have hShared : ((S.image f).filter (fun b => 2 ≤ (S.filter (fun c => f c = b)).card)).card ≤
      L₁' := by
    refine h₁' (f w) _ fun b hb => ?_
    obtain ⟨hbI, hb2⟩ := mem_filter.mp hb
    obtain ⟨c, hc, c', hc', hne⟩ := one_lt_card.mp hb2
    obtain ⟨hcS, hcb⟩ := mem_filter.mp hc
    obtain ⟨hcS', hcb'⟩ := mem_filter.mp hc'
    have hsne : s c ≠ s c' := fun h => hne (hfs c c' (hcb.trans hcb'.symm) h)
    have h1 := card_union_add_card_inter (agr D w c) (agr D w c')
    have h2 : (agr D w c ∩ agr D w c').card ≤ d := by
      refine le_trans (card_le_card fun i hi => ?_) (hC₂ _ (hsC c hcS) _ (hsC c' hcS') hsne)
      exact mem_agr_of_mem_agr (hagrs c (mem_inter.mp hi).1) (hagrs c' (mem_inter.mp hi).2)
    have h3 : (agr D w c ∪ agr D w c').card ≤ (agr D (f w) b).card := by
      refine card_le_card (union_subset ?_ ?_)
      · rw [← hcb]
        exact hagrf c
      · rw [← hcb']
        exact hagrf c'
    have h4 := (hS c hcS).2
    have h5 := (hS c' hcS').2
    obtain ⟨c₀, hc₀, rfl⟩ := mem_image.mp hbI
    exact ⟨hfC c₀ hc₀, by omega⟩
  calc S.card = ∑ b ∈ S.image f, (S.filter (fun c => f c = b)).card := card_eq_sum_card_image f S
    _ ≤ ∑ b ∈ S.image f,
          (1 + if 2 ≤ (S.filter (fun c => f c = b)).card then L₂ - 1 else 0) := by
        refine sum_le_sum fun b _ => ?_
        have := hfib b
        split_ifs with h2 <;> omega
    _ = (S.image f).card +
          ((S.image f).filter (fun b => 2 ≤ (S.filter (fun c => f c = b)).card)).card *
            (L₂ - 1) := by
        rw [sum_add_distrib, ← sum_filter, sum_const, sum_const, smul_eq_mul, smul_eq_mul,
          mul_one]
    _ ≤ L₁ + L₁' * (L₂ - 1) := Nat.add_le_add hCh (Nat.mul_le_mul_right _ hShared)

/-- A weaker form of Proposition 6.3 of the paper: `Λ_2(a) ≤ Λ_1(a) (1 + Λ_1(2a - d))`. -/
theorem listBound_prod_self {D : Finset ι} {C : Set (ι → α)} {d a L L' : ℕ}
    (hC : AgreeLE D C d) (h : ListBound D C a L) (h' : ListBound D C (2 * a - d) L') :
    ListBound D (prodCode C C) a (L * (1 + L')) := by
  refine (listBound_prod hC h h' h).mono le_rfl ?_
  have : L' * (L - 1) ≤ L' * L := Nat.mul_le_mul_left _ (Nat.sub_le L 1)
  nlinarith

/-- The special case of Proposition 6.3 of the paper: for `a > (n + 3d)/4` two lanes have at most
`2L - 1` list members. -/
theorem listBound_prod_two_mul {D : Finset ι} {C : Set (ι → α)} {d a L : ℕ}
    (hC : AgreeLE D C d) (h : ListBound D C a L) (h4 : D.card + 3 * d < 4 * a) :
    ListBound D (prodCode C C) a (2 * L - 1) :=
  (listBound_prod hC h (hC.listBound_one (by omega)) h).mono le_rfl (by omega)

end Interleave
