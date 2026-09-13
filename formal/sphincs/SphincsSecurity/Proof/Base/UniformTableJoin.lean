import SphincsSecurity.Proof.Base.UniformTableProducts
import SphincsSecurity.Proof.Base.UniformTableSplit
namespace SphincsSecurity.Concrete.UniformTableSplit

open _root_.OracleComp ENNReal
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

variable {Index Cell Answer : Type} (embed : Index → Cell) (hinj : Function.Injective embed)

theorem join_eq_iff (table : Cell → Answer) (rows : Index → Answer) (outside : Outside embed → Answer) :
    table = join embed hinj rows outside ↔ rows = table ∘ embed ∧ outside = fun cell : Outside embed => table cell.val := by
  constructor
  · intro heq
    subst table
    constructor
    · funext index
      exact (join_embed embed hinj rows outside index).symm
    · funext cell
      exact (join_outside embed hinj rows outside cell).symm
  · rintro ⟨rfl, rfl⟩
    exact (join_split embed hinj table).symm

attribute [local irreducible] join

section Mass

attribute [local instance 10000] Classical.propDecidable

theorem bind_map_join_apply (left : PMF (Index → Answer)) (right : PMF (Outside embed → Answer)) (table : Cell → Answer) :
    (left.bind fun rows => right.map (join embed hinj rows)) table =
      left (table ∘ embed) * right (fun cell => table cell.val) := by
  simp only [PMF.bind_apply, PMF.map_apply]
  rw [tsum_eq_single (table ∘ embed)]
  · rw [tsum_eq_single (fun cell : Outside embed => table cell.val)]
    · rw [if_pos (join_split embed hinj table).symm]
    · intro outside hne
      exact if_neg (fun h => hne ((join_eq_iff embed hinj table _ outside).mp h).2)
  · intro rows hne
    have hz : (∑' outside : Outside embed → Answer,
        if table = join embed hinj rows outside then right outside else 0) = 0 := by
      apply ENNReal.tsum_eq_zero.mpr
      intro outside
      exact if_neg (fun h => hne ((join_eq_iff embed hinj table rows outside).mp h).1)
    rw [hz, mul_zero]

end Mass

variable [Fintype Index] [Fintype Cell] [DecidableEq Cell]

include hinj in
theorem prod_embed_mul_outside {M : Type} [CommMonoid M] (f : Cell → M) :
    (∏ index, f (embed index)) * (∏ cell : Outside embed, f cell.val) = ∏ cell, f cell := by
  letI : Fintype (Set.range embed) := Subtype.fintype (Set.range embed)
  have he : (∏ index, f (embed index)) = ∏ cell : Set.range embed, f cell.val :=
    Fintype.prod_equiv (Equiv.ofInjective embed hinj) _ _ (fun _ => rfl)
  rw [he]
  convert Fintype.prod_subtype_mul_prod_subtype (Set.range embed) f using 1
  congr 1
  exact Finset.prod_congr (by ext; simp) (fun _ _ => rfl)

variable [DecidableEq Index] [Fintype Answer]

theorem product_join (left : Index → PMF Answer) (right : Outside embed → PMF Answer) :
    (FinitePmfProduct.law left).bind (fun rows => (FinitePmfProduct.law right).map (join embed hinj rows)) =
      FinitePmfProduct.law (join embed hinj left right) := by
  apply PMF.ext
  intro table
  rw [bind_map_join_apply]
  simp only [FinitePmfProduct.apply]
  have hp := prod_embed_mul_outside embed hinj (fun cell => join embed hinj left right cell (table cell))
  simpa only [join_embed, join_outside, Function.comp_def] using hp

variable [DecidableEq Answer]

omit [Fintype Cell] [DecidableEq Index] [Fintype Answer] [DecidableEq Answer] in
theorem join_nonempty (left : Index → Finset Answer) (right : Outside embed → Finset Answer)
    (hl : ∀ index, (left index).Nonempty) (hr : ∀ cell, (right cell).Nonempty) :
    ∀ cell, (join embed hinj left right cell).Nonempty := by
  intro cell
  by_cases hc : cell ∈ Set.range embed
  · obtain ⟨index, rfl⟩ := hc
    rw [join_embed]
    exact hl index
  · change (join embed hinj left right (⟨cell, hc⟩ : Outside embed).val).Nonempty
    rw [join_outside]
    exact hr ⟨cell, hc⟩

theorem uniformTable_join (left : Index → Finset Answer) (right : Outside embed → Finset Answer)
    (hl : ∀ index, (left index).Nonempty) (hr : ∀ cell, (right cell).Nonempty) :
    (uniformTable left hl).bind (fun rows => (uniformTable right hr).map (join embed hinj rows)) =
      uniformTable (join embed hinj left right) (join_nonempty embed hinj left right hl hr) := by
  simp only [uniformTable_eq_product, product_join]
  apply congrArg FinitePmfProduct.law
  funext cell
  by_cases hc : cell ∈ Set.range embed
  · obtain ⟨index, rfl⟩ := hc
    simp only [join_embed]
  · change join embed hinj _ _ (⟨cell, hc⟩ : Outside embed).val = _
    rw [join_outside]
    have hrow := join_outside embed hinj left right (⟨cell, hc⟩ : Outside embed)
    simp only [hrow]

end SphincsSecurity.Concrete.UniformTableSplit
